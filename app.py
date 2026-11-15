#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
视频剪裁工具 —— 本地服务端
纯标准库实现：网页播放器 + ffmpeg 精确剪辑
"""
import hashlib
import json
import mimetypes
import os
import re
import shutil
import subprocess
import sys
import threading
import time
import urllib.parse
import urllib.request
import uuid
import webbrowser
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

ROOT = os.path.dirname(os.path.abspath(__file__))
BIN = os.path.join(ROOT, 'bin')
TMP = os.path.join(ROOT, '_tmp')
PORT = int(os.environ.get('CUTTER_PORT', '8777'))
CREATE_NO_WINDOW = 0x08000000 if os.name == 'nt' else 0

VIDEO_EXT = {'.mp4', '.mkv', '.mov', '.avi', '.flv', '.ts', '.m4v', '.webm',
             '.wmv', '.mpg', '.mpeg', '.m2ts', '.rmvb', '.3gp'}

# 自己导出的成片（xxx_剪辑.mp4、撞名时的 xxx_剪辑_2.mp4）不该再出现在待剪列表里
SPLIT_SUFFIX_RE = re.compile(r'_(剪辑|clip)(_\d+)?$', re.I)
NAT_RE = re.compile(r'(\d+)')


def find_ffmpeg():
    for name in ('ffmpeg.exe', 'ffmpeg'):
        p = os.path.join(BIN, name)
        if os.path.isfile(p):
            return p
    return shutil.which('ffmpeg') or ''


FFMPEG = find_ffmpeg()

STATE = {
    'video': None,      # 当前正在剪的视频绝对路径
    'proxy': None,      # 预览代理文件
    'info': {},
    'outdir': None,     # 用户手动指定的输出目录（对所有视频生效）
    'outdir_locked': False,
    'locating': None,   # 正在反查拖入文件的原目录
    'origin': None,     # 反查到的原文件所在目录
    'recent_dirs': [],  # 最近打开过的视频目录，反查时优先搜
    'hwenc': True,      # 用显卡编码加速
}
LOCK = threading.RLock()

# 后台剪辑任务：好几部片子可以同时排队，worker 逐个跑（串行，避免互相抢磁盘）
JOBS = {}
JOB_SEQ = []
EXPORT_WAKE = threading.Event()

# 文件夹递归出来的视频清单
LIB = {'root': '', 'items': [], 'scanning': False, 'scanned': 0, 'gen': 0}
SKIP_SCAN = {'$recycle.bin', 'system volume information', 'recycler', '_tmp',
             'node_modules', '.git', '__pycache__', '.workbuddy'}

# 标注工程：存在本地文件里，换浏览器 / 清缓存也不会丢
DATA = os.path.join(ROOT, '_data')
PROJ_FILE = os.path.join(DATA, 'annotations.json')
PROJECTS = {}          # 视频路径 -> {segs, dirty, done, out, ts}
PROJ_LOCK = threading.Lock()
PROJ_NEED_SAVE = False

# 片段预编码队列：标注时就把每段编好，导出时只剩拼接。
# 队列跨视频共用一条 —— 切到下一部时，上一部没编完的段继续排队，
# 后台导出还能直接吃到它们。
CACHE = os.path.join(TMP, 'cache')
PREWARM = {
    'queue': [],      # 待编码 [(src, a, b, mode)]
    'want': {},       # 源指纹 -> (src, [(a,b)], mode)
    'error': {},      # 源指纹 -> 错误信息
    'busy': False,
    'paused': False,
    'cur': '',
    'current': None,  # 正在编码的 (src, a, b, mode)
}
PREWARM_WAKE = threading.Event()
ENCODER = None        # 'nvenc' / 'x264'，首次使用时探测
PROBE_CACHE = {}      # (路径,大小,mtime) -> info，避免反复探测
_LAST_GC = 0.0
CACHE_LIMIT = int(float(os.environ.get('CUTTER_CACHE_GB', '20')) * (1 << 30))


# ----------------------------------------------------------------------------
# ffmpeg 调用
# ----------------------------------------------------------------------------
def run_cmd(args, timeout=None):
    kw = {}
    if CREATE_NO_WINDOW:
        kw['creationflags'] = CREATE_NO_WINDOW
    return subprocess.run(args, capture_output=True, timeout=timeout, **kw)


def _pkey(path):
    try:
        st = os.stat(path)
        return (os.path.abspath(path).lower(), st.st_size, int(st.st_mtime))
    except OSError:
        return None


def probe(path, use_cache=True):
    """解析 ffmpeg -i 输出，取时长 / 帧率 / 分辨率 / 是否含音频"""
    info = {'duration': 0.0, 'fps': 30.0, 'width': 0, 'height': 0,
            'audio': False, 'vcodec': '', 'acodec': ''}
    ck = _pkey(path) if use_cache else None
    if ck:
        hit = PROBE_CACHE.get(ck)
        if hit:
            return dict(hit)
    try:
        r = run_cmd([FFMPEG, '-hide_banner', '-i', path], timeout=60)
    except Exception:
        return info
    s = r.stderr.decode('utf-8', 'replace')
    m = re.search(r'Duration:\s*(\d+):(\d+):(\d+(?:\.\d+)?)', s)
    if m:
        info['duration'] = int(m.group(1)) * 3600 + int(m.group(2)) * 60 + float(m.group(3))
    m = re.search(r'Video:\s*([a-zA-Z0-9_]+).*?(\d{2,5})x(\d{2,5})', s)
    if m:
        info['vcodec'] = m.group(1)
        info['width'] = int(m.group(2))
        info['height'] = int(m.group(3))
    m = re.search(r'(\d+(?:\.\d+)?)\s*fps', s)
    if m:
        f = float(m.group(1))
        if 1 < f < 240:
            info['fps'] = f
    if re.search(r'Stream #\d+:\d+.*?: Audio:', s):
        info['audio'] = True
        m = re.search(r'Audio:\s*([a-zA-Z0-9_]+)', s)
        if m:
            info['acodec'] = m.group(1)
    if ck and (info['duration'] or info['width']):
        PROBE_CACHE[ck] = dict(info)
    return info


KEYINT_CACHE = {}


def keyframe_gap(path):
    """估算关键帧间隔（秒）。

    跳转必须先解到上一个关键帧，间隔 8 秒就意味着要连解 240 帧才能显示目标画面，
    这就是快进快退卡的根因。返回 (gap, ok)；gap<=0 表示探不出来。
    """
    ck = _pkey(path)
    if ck and ck in KEYINT_CACHE:
        return KEYINT_CACHE[ck]
    gap, ok = 0.0, False
    if FFMPEG:
        try:
            r = run_cmd([FFMPEG, '-hide_banner', '-nostats', '-skip_frame', 'nokey',
                         '-i', path, '-map', '0:v:0', '-vf', 'showinfo',
                         '-frames:v', '4', '-t', '120', '-f', 'null', '-'], timeout=45)
            ts = sorted({float(x) for x in
                         re.findall(r'pts_time:\s*([0-9]+(?:\.[0-9]+)?)',
                                    r.stderr.decode('utf-8', 'replace'))})
            if ts:
                ok = True
                if len(ts) >= 2:
                    diffs = sorted(b - a for a, b in zip(ts, ts[1:]) if b - a > 0.004)
                    if diffs:
                        gap = diffs[len(diffs) // 2]
                else:
                    # 前 2 分钟只有 1 个关键帧：跳转必然极慢
                    gap = 120.0
        except Exception:
            pass
    if ck:
        KEYINT_CACHE[ck] = (gap, ok)
    return gap, ok


SEEK_PROBING = set()


def detect_seek_info(path):
    """后台算关键帧间隔，塞进 STATE['info']，前端轮询到就能提示"""
    key = os.path.abspath(path).lower()
    with LOCK:
        if key in SEEK_PROBING:
            return
        SEEK_PROBING.add(key)
    try:
        gap, ok = keyframe_gap(path)
        with LOCK:
            cur = STATE.get('video')
            if cur and os.path.abspath(cur).lower() == key:
                STATE['info']['keyint'] = round(gap, 2) if ok else 0
                STATE['info']['keyintOk'] = ok
    except Exception:
        pass
    finally:
        with LOCK:
            SEEK_PROBING.discard(key)


BELOW_NORMAL_PRIORITY_CLASS = 0x00004000


def ffmpeg_progress(args, total_sec, on_pct=None, low_priority=False):
    """运行 ffmpeg 并解析 time= 上报进度

    low_priority: 后台预览代理用低优先级，不能跟用户在做的跳转抢 CPU/GPU
    """
    cmd = [FFMPEG, '-hide_banner', '-y'] + args
    kw = {}
    flags = CREATE_NO_WINDOW
    if low_priority and os.name == 'nt':
        flags |= BELOW_NORMAL_PRIORITY_CLASS
    if flags:
        kw['creationflags'] = flags
    p = subprocess.Popen(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE,
                         universal_newlines=True, encoding='utf-8', errors='replace', **kw)
    tail = []
    for line in p.stderr:
        line = line.rstrip()
        if not line:
            continue
        tail.append(line)
        if len(tail) > 40:
            tail.pop(0)
        m = re.search(r'time=(\d+):(\d+):(\d+(?:\.\d+)?)', line)
        if m and total_sec > 0 and on_pct:
            t = int(m.group(1)) * 3600 + int(m.group(2)) * 60 + float(m.group(3))
            on_pct(min(0.999, t / total_sec))
    p.wait()
    if p.returncode != 0:
        raise RuntimeError('ffmpeg 失败：\n' + '\n'.join(tail[-12:]))


# ----------------------------------------------------------------------------
# 任务（导出 / 代理）：多个任务可以同时存在，导出串行执行
# ----------------------------------------------------------------------------
def new_job(kind, label, **extra):
    job = {'id': uuid.uuid4().hex[:12], 'kind': kind, 'label': label,
           'status': 'queued', 'running': False, 'pct': 0.0, 'message': '排队中…',
           'output': '', 'error': '', 't0': time.time(), 't1': 0.0, 'size': 0,
           'src': '', 'name': '', 'segments': [], 'mode': 'accurate'}
    job.update(extra)
    with LOCK:
        JOBS[job['id']] = job
        JOB_SEQ.append(job['id'])
        while len(JOB_SEQ) > 40:
            JOBS.pop(JOB_SEQ.pop(0), None)
    return job


def job_update(job, **kw):
    with LOCK:
        job.update(kw)
        if 'status' in kw:
            job['running'] = (kw['status'] == 'running')


def find_job(jid):
    with LOCK:
        return JOBS.get(jid)


def jobs_snapshot(limit=24):
    """最新在前；正在跑/排队的排最上面"""
    with LOCK:
        items = [sanitize_job(JOBS[j]) for j in JOB_SEQ if j in JOBS]
    live = [j for j in items if j['status'] in ('queued', 'running')]
    rest = [j for j in items if j['status'] not in ('queued', 'running')]
    live.sort(key=lambda j: 0 if j['status'] == 'running' else 1)
    rest.reverse()
    return (live + rest)[:limit]


def active_export_count():
    with LOCK:
        return sum(1 for j in JOBS.values()
                   if j['kind'] == 'export' and j['status'] in ('queued', 'running'))


def job_for_src(src, statuses=('queued', 'running')):
    with LOCK:
        for j in JOB_SEQ:
            jj = JOBS.get(j)
            if jj and jj['kind'] == 'export' and jj.get('src') == src and jj['status'] in statuses:
                return jj
    return None


def export_worker():
    """串行跑导出：一次只编一部，其它在队列里等，界面不受影响"""
    while True:
        EXPORT_WAKE.wait(timeout=2.0)
        EXPORT_WAKE.clear()
        while True:
            job = None
            with LOCK:
                for jid in JOB_SEQ:
                    j = JOBS.get(jid)
                    if j and j['kind'] == 'export' and j['status'] == 'queued':
                        j['status'] = 'running'
                        j['running'] = True
                        j['message'] = '准备中…'
                        job = j
                        break
            if not job:
                break
            try:
                do_export(job)
            except Exception as e:
                job_update(job, status='error', error=str(e), message='失败', t1=time.time())
                with LOCK:
                    PREWARM['paused'] = False
                PREWARM_WAKE.set()


threading.Thread(target=export_worker, name='export', daemon=True).start()



def clean_tmp():
    """清掉本次运行的临时文件。

    顺滑预览（_tmp/proxy）现在默认就生成，每次启动都删等于每次都要重编，
    所以留着按容量/时间淘汰，见 prune_proxy_cache()。
    """
    try:
        for n in os.listdir(TMP):
            if n == 'proxy':
                continue
            p = os.path.join(TMP, n)
            shutil.rmtree(p, ignore_errors=True) if os.path.isdir(p) else os.remove(p)
    except Exception:
        pass


def prune_proxy_cache(max_gb=5.0, keep_days=10):
    """预览代理只当缓存用：太大或太旧就淘汰，别把用户磁盘吃掉"""
    try:
        if not os.path.isdir(PROXY_DIR):
            return
        with LOCK:
            keep = {STATE.get('proxy') or ''}
        now = time.time()
        files = []
        total = 0
        for n in os.listdir(PROXY_DIR):
            if '.part' in n:          # 正在编码的临时文件，别动
                continue
            p = os.path.join(PROXY_DIR, n)
            if not os.path.isfile(p):
                continue
            st = os.stat(p)
            files.append((st.st_mtime, st.st_size, p))
            total += st.st_size
        gone = []
        for mt, sz, p in files:
            if p in keep:
                continue
            if now - mt > keep_days * 86400:
                safe_unlink(p)
                total -= sz
                gone.append(p)
        if total > max_gb * (1 << 30):
            # 从最旧的开始删，删到额度以内
            for mt, sz, p in sorted(files):
                if total <= max_gb * 0.8 * (1 << 30):
                    break
                if p in keep or not os.path.isfile(p):
                    continue
                safe_unlink(p)
                total -= sz
                gone.append(p)
        if gone:
            gs = {os.path.abspath(p).lower() for p in gone}
            with LOCK:
                for k, v in list(PROXIES.items()):
                    if os.path.abspath(v).lower() in gs:
                        PROXIES.pop(k, None)
                        PROXY_READY.discard(k)
    except Exception:
        pass


EXPORT_LOG = os.path.join(ROOT, 'exports.log')


def log_export(src, out, seconds, note=''):
    """每次导出写一行记录；以后找不到成片时可以直接查这个文件"""
    try:
        line = '%s\t%s\t->\t%s\t(%s)%s\n' % (
            time.strftime('%Y-%m-%d %H:%M:%S'), src, out, fmt_sec(seconds or 0),
            ('\t[' + note + ']') if note else '')
        with open(EXPORT_LOG, 'a', encoding='utf-8') as f:
            f.write(line)
    except Exception:
        pass


def safe_unlink(p):
    try:
        os.remove(p)
    except Exception:
        pass


# ----------------------------------------------------------------------------
# 删除原片（导出成功后才会调用）
# 默认走回收站：误删还能捞回来；回收站放不下的大文件才直接删。
# ----------------------------------------------------------------------------
def _recycle_win32(path):
    """把文件丢进 Windows 回收站，成功返回 True"""
    try:
        import ctypes
        from ctypes import wintypes

        class SHFILEOPSTRUCTW(ctypes.Structure):
            _fields_ = [('hwnd', wintypes.HWND),
                        ('wFunc', wintypes.UINT),
                        ('pFrom', wintypes.LPCWSTR),
                        ('pTo', wintypes.LPCWSTR),
                        ('fFlags', ctypes.c_ushort),
                        ('fAnyOperationsAborted', wintypes.BOOL),
                        ('hNameMappings', ctypes.c_void_p),
                        ('lpszProgressTitle', wintypes.LPCWSTR)]

        FO_DELETE = 3
        FOF_SILENT = 0x0004
        FOF_NOCONFIRMATION = 0x0010
        FOF_ALLOWUNDO = 0x0040          # 关键：进回收站而不是彻底删
        FOF_NOERRORUI = 0x0400
        buf = os.path.abspath(path) + '\0\0'   # 必须双 \0 结尾
        op = SHFILEOPSTRUCTW()
        op.hwnd = None
        op.wFunc = FO_DELETE
        op.pFrom = buf
        op.pTo = None
        op.fFlags = FOF_ALLOWUNDO | FOF_NOCONFIRMATION | FOF_SILENT | FOF_NOERRORUI
        rc = ctypes.windll.shell32.SHFileOperationW(ctypes.byref(op))
        return rc == 0 and not op.fAnyOperationsAborted
    except Exception:
        return False


def delete_source(src, outpath):
    """删原片，返回一句给人看的结果（空串＝跳过，不需要提示）"""
    try:
        s = os.path.abspath(src)
        o = os.path.abspath(outpath)
    except Exception:
        return '原片未删除'
    if not os.path.isfile(s):
        return ''
    if s.lower() == o.lower():
        return '原片未删除（成片与源同名）'
    if s.lower().startswith(TMP_LOWER):
        return ''        # 拖拽进来的临时副本，本来就随工具清理
    # 成片得是完整文件才动原片，宁可留一份也不删错
    try:
        if os.path.getsize(o) < 1024:
            return '原片保留（成片异常）'
    except OSError:
        return '原片保留（成片不存在）'

    if os.name == 'nt' and _recycle_win32(s):
        return '原片已移入回收站'
    try:
        os.remove(s)
        return '原片已删除'
    except Exception as e:
        return '原片没删掉：%s' % e


def lib_forget(path):
    """把已删除的文件从待剪列表里摘掉"""
    try:
        low = os.path.abspath(path).lower()
    except Exception:
        return
    with LOCK:
        LIB['items'] = [it for it in LIB['items']
                        if os.path.abspath(it.get('path', '')).lower() != low]
        PROXY_READY.discard(low)     # 原片都删了，⚡ 也别再挂在别人身上


def drop_project(path):
    """文件没了，它的标注记录也一起清掉，避免列表里留幽灵"""
    gone = False
    with PROJ_LOCK:
        gone = PROJECTS.pop(path, None) is not None
    if gone:
        touch_projects()


# ----------------------------------------------------------------------------
# 编码器选择：优先显卡硬件编码（NVENC / QSV / AMF），不可用则回退 CPU
# ----------------------------------------------------------------------------
def detect_encoder():
    """实测一次能否真正出片，光看 -encoders 列表不算（驱动缺失会失败）"""
    global ENCODER
    if not STATE.get('hwenc', True):
        return 'x264'
    if ENCODER:
        return ENCODER
    probed = []
    if FFMPEG:
        for name, codec in (('nvenc', 'h264_nvenc'), ('qsv', 'h264_qsv'), ('amf', 'h264_amf')):
            try:
                r = run_cmd([FFMPEG, '-hide_banner', '-loglevel', 'error', '-f', 'lavfi',
                             '-i', 'color=c=black:s=320x240:r=30:d=0.5',
                             '-c:v', codec, '-f', 'null', '-'], timeout=25)
                if r.returncode == 0:
                    ENCODER = name
                    probed.append(name)
                    break
            except Exception:
                pass
    if not ENCODER:
        ENCODER = 'x264'
    return ENCODER


ENCODER_LABEL = {'nvenc': '显卡 NVENC', 'qsv': '核显 QSV', 'amf': '显卡 AMF', 'x264': 'CPU x264'}


def encoder_args(enc, quality='high', threads=None, max_kbps=None):
    """给每段用的编码参数；导出与预编码必须完全一致，否则拼不起来"""
    codec = {'nvenc': 'h264_nvenc', 'qsv': 'h264_qsv', 'amf': 'h264_amf'}.get(enc)
    if codec == 'h264_nvenc':
        # cq 越小越好；19 的实测 SSIM 已高于 x264 crf18，体积略大
        cq = '21' if quality == 'high' else '24'
        v = ['-c:v', codec, '-preset', 'p4', '-tune', 'hq', '-rc', 'vbr',
             '-cq', cq, '-b:v', '0']
        if max_kbps:
            # 质量模式在简单画面上会白白堆码率，封顶到源码率以内
            v += ['-maxrate', '%dk' % int(max_kbps), '-bufsize', '%dk' % int(max_kbps * 2)]
        v += ['-pix_fmt', 'yuv420p']
    elif codec == 'h264_qsv':
        v = ['-c:v', codec, '-preset', 'medium', '-global_quality', '20' if quality == 'high' else '23',
             '-pix_fmt', 'nv12']
    elif codec == 'h264_amf':
        v = ['-c:v', codec, '-quality', 'balanced', '-rc', 'cqp',
             '-qp_i', '20', '-qp_p', '22', '-pix_fmt', 'yuv420p']
    else:
        crf = '18' if quality == 'high' else '21'
        v = ['-c:v', 'libx264', '-preset', 'veryfast', '-crf', crf, '-pix_fmt', 'yuv420p']
        if threads:
            v += ['-threads', str(threads)]
    return v + ['-c:a', 'aac', '-b:a', '192k']


_RATE_CACHE = {}


def src_maxrate(src):
    """成片码率上限取源码率，避免简单画面被硬件编码器撑大"""
    key = src_fingerprint(src)
    if key in _RATE_CACHE:
        return _RATE_CACHE[key]
    val = None
    try:
        info = probe(src)
        d = info.get('duration') or 0
        size = os.path.getsize(src)
        if d > 0 and size > 0:
            val = max(3000, min(80000, int(size * 8 / d / 1000)))
    except Exception:
        val = None
    _RATE_CACHE[key] = val
    return val


def seg_base(src, a, b):
    return ['-ss', '%.3f' % a, '-to', '%.3f' % b, '-i', src,
            '-map', '0:v:0', '-map', '0:a:0?',
            '-avoid_negative_ts', 'make_zero', '-sn', '-dn']


def src_fingerprint(src):
    """源文件的指纹：路径+大小+修改时间，任何一个变了缓存就作废"""
    try:
        st = os.stat(src)
        raw = '%s|%d|%d' % (os.path.abspath(src).lower(), st.st_size, int(st.st_mtime))
    except Exception:
        raw = os.path.abspath(src).lower()
    return hashlib.md5(raw.encode('utf-8')).hexdigest()[:16]


def cache_dir_for(src):
    return os.path.join(CACHE, src_fingerprint(src))


def cache_file(src, a, b, enc):
    """一段的缓存路径；时间取到毫秒，和 ffmpeg 参数一致"""
    key = '%s_%s_%s' % (('%.3f' % a).replace('.', ''), ('%.3f' % b).replace('.', ''), enc)
    return os.path.join(cache_dir_for(src), key + '.mp4')


def clear_cache(src=None):
    """换编码器时清全部；清某一部时只清它自己的，别动别人正在用的缓存"""
    try:
        if src:
            shutil.rmtree(cache_dir_for(src), ignore_errors=True)
        else:
            shutil.rmtree(CACHE, ignore_errors=True)
    except Exception:
        pass
    with LOCK:
        if src:
            key = src_fingerprint(src)
            PREWARM['want'].pop(key, None)
            PREWARM['error'].pop(key, None)
            PREWARM['queue'] = [it for it in PREWARM['queue'] if it[0] != src]
        else:
            PREWARM['queue'].clear()
            PREWARM['want'].clear()
            PREWARM['error'].clear()
            PREWARM['cur'] = ''
            PREWARM['current'] = None
            PREWARM['busy'] = False


def cached_ok(path):
    try:
        return os.path.exists(path) and os.path.getsize(path) > 1024
    except Exception:
        return False


def prewarm_summary(src=None):
    """某部片子的预编码进度。done 直接按缓存文件数算，不会和实际漂移"""
    key = src_fingerprint(src) if src else ''
    with LOCK:
        want = PREWARM['want'].get(key)
        cur = PREWARM['current']
        busy_all = PREWARM['busy']
        paused = PREWARM['paused']
        err = PREWARM['error'].get(key, '')
        curlabel = PREWARM['cur']
    if not want:
        return {'busy': False, 'done': 0, 'total': 0, 'cur': '', 'error': err,
                'paused': paused}
    s, segs, _mode = want
    enc = detect_encoder()
    done = sum(1 for a, b in segs if cached_ok(cache_file(s, a, b, enc)))
    busy = busy_all and bool(cur) and cur[0] == s
    return {'busy': busy, 'done': done, 'total': len(segs),
            'cur': curlabel if busy else '', 'error': err, 'paused': paused}


def prewarm_worker():
    """单线程后台队列：一段一段编，避免多进程抢磁盘反而更慢"""
    while True:
        PREWARM_WAKE.wait(timeout=3.0)
        PREWARM_WAKE.clear()
        while True:
            with LOCK:
                if PREWARM['paused'] or not PREWARM['queue']:
                    PREWARM['busy'] = False
                    PREWARM['cur'] = ''
                    PREWARM['current'] = None
                    break
                item = PREWARM['queue'].pop(0)
                PREWARM['busy'] = True
                PREWARM['current'] = item
                PREWARM['cur'] = '%s–%s' % (fmt_sec(item[1]), fmt_sec(item[2]))
            src, a, b, mode = item
            key = src_fingerprint(src)
            enc = detect_encoder()
            out = cache_file(src, a, b, enc)
            try:
                if not cached_ok(out):
                    os.makedirs(os.path.dirname(out), exist_ok=True)
                    tmp = out + '.tmp.mp4'
                    # 预编码限 4 线程：别把 CPU 占满影响你播放/拖时间轴
                    if mode == 'fast':
                        args = seg_base(src, a, b) + ['-c', 'copy']
                    else:
                        args = seg_base(src, a, b) + encoder_args(
                            enc, threads=4, max_kbps=src_maxrate(src))
                    r = run_cmd([FFMPEG, '-hide_banner', '-y', '-loglevel', 'error'] + args + [tmp],
                                timeout=1800)
                    if r.returncode != 0:
                        # 硬件编码吃不下这个素材就退回 CPU
                        if enc != 'x264':
                            r = run_cmd([FFMPEG, '-hide_banner', '-y', '-loglevel', 'error']
                                        + seg_base(src, a, b)
                                        + encoder_args('x264', threads=4) + [tmp], timeout=1800)
                            if r.returncode == 0:
                                with LOCK:
                                    globals()['ENCODER'] = 'x264'
                        if r.returncode != 0:
                            with LOCK:
                                PREWARM['error'][key] = '有一段预编码失败，导出时会重新编码'
                            safe_unlink(tmp)
                            continue
                    os.replace(tmp, out)
            except Exception:
                with LOCK:
                    PREWARM['error'][key] = '预编码中断，导出时会重新编码'
            finally:
                with LOCK:
                    PREWARM['current'] = None
                cache_gc()


def queue_prewarm(src, segments, mode='accurate'):
    """重排这一部的待编段；别的视频排队的段保留不动（切走也接着编）"""
    if not FFMPEG or not src:
        return
    enc = detect_encoder()
    key = src_fingerprint(src)
    missing = [(src, a, b, mode) for a, b in segments
               if not cached_ok(cache_file(src, a, b, enc))]
    with LOCK:
        cur = PREWARM['current']
        cur_key = (cur[1], cur[2]) if cur and cur[0] == src else None
        others = [it for it in PREWARM['queue'] if it[0] != src]
        mine = [m for m in missing if (m[1], m[2]) != cur_key]
        # 当前这部的段排前面，切走的片子排在后面慢慢编
        PREWARM['queue'] = mine + others
        PREWARM['want'][key] = (src, sorted(segments), mode)
        PREWARM['error'].pop(key, None)
        if len(PREWARM['want']) > 40:      # 只留最近的几十部，别无限涨
            for k in list(PREWARM['want'].keys())[:-40]:
                if k != key:
                    PREWARM['want'].pop(k, None)
        # 已删掉的片段，顺手把它编好的缓存也删了
        keep = {(('%.3f' % a).replace('.', ''), ('%.3f' % b).replace('.', ''))
                for a, b in segments}
    try:
        d = cache_dir_for(src)
        if os.path.isdir(d):
            for f in os.listdir(d):
                if not f.endswith('.mp4'):
                    continue
                base = f[:-4].split('_')
                if len(base) >= 2 and (base[0], base[1]) not in keep:
                    safe_unlink(os.path.join(d, f))
    except Exception:
        pass
    PREWARM_WAKE.set()


def prewarm_boost(src):
    """有这部片子的导出排队时，把它的段挪到队头先编"""
    with LOCK:
        PREWARM['queue'].sort(key=lambda it: 0 if it[0] == src else 1)


threading.Thread(target=prewarm_worker, name='prewarm', daemon=True).start()


def prewarm_pending(src):
    """(还有多少段没编, 是否正在编这部)"""
    with LOCK:
        cur = PREWARM['current']
        n = sum(1 for it in PREWARM['queue'] if it[0] == src)
        busy = bool(cur) and cur[0] == src
    return n, busy


def prewarm_wait_src(src, timeout=900, on_tick=None):
    """等这部片子自己的段编完 —— 导出时直接拼接，比分段重编码快得多"""
    key = src_fingerprint(src)
    t0 = time.time()
    last = -1
    while time.time() - t0 < timeout:
        n, busy = prewarm_pending(src)
        if not n and not busy:
            return
        with LOCK:
            err = PREWARM['error'].get(key, '')
        if err:
            return
        if on_tick:
            with LOCK:
                want = PREWARM['want'].get(key)
            if want:
                done = len(want[1]) - n
                if done != last:
                    last = done
                    on_tick(done, len(want[1]))
        time.sleep(0.15)


def prewarm_pause_wait(timeout=5):
    """暂停后台队列，等手上那一段收尾"""
    t0 = time.time()
    while time.time() - t0 < timeout:
        with LOCK:
            if not PREWARM['busy'] and not PREWARM['current']:
                return
        time.sleep(0.1)


def cache_gc(force=False):
    """缓存超了就从最久没动过的片子开始清，正在剪/正在导出的不碰"""
    global _LAST_GC
    now = time.time()
    if not force and now - _LAST_GC < 120:
        return
    _LAST_GC = now
    total = 0
    entries = []
    try:
        for name in os.listdir(CACHE):
            d = os.path.join(CACHE, name)
            if not os.path.isdir(d):
                continue
            sz = 0
            try:
                for f in os.listdir(d):
                    try:
                        sz += os.path.getsize(os.path.join(d, f))
                    except OSError:
                        pass
                mt = os.path.getmtime(d)
            except OSError:
                continue
            total += sz
            entries.append((d, sz, mt))
    except Exception:
        return
    if total <= CACHE_LIMIT:
        return
    protected = set()
    if STATE['video']:
        protected.add(os.path.basename(cache_dir_for(STATE['video'])))
    with LOCK:
        for j in JOBS.values():
            if j['status'] in ('queued', 'running') and j.get('src'):
                protected.add(os.path.basename(cache_dir_for(j['src'])))
    entries.sort(key=lambda e: e[2])
    for d, sz, _mt in entries:
        if total <= CACHE_LIMIT * 0.8:
            break
        if os.path.basename(d) in protected:
            continue
        shutil.rmtree(d, ignore_errors=True)
        total -= sz



def media_duration(path):
    """读取输出文件的真实时长，用于校验快速模式的关键帧对齐误差"""
    try:
        r = run_cmd([FFMPEG, '-hide_banner', '-i', path], timeout=30)
        m = re.search(r'Duration:\s*(\d+):(\d+):(\d+(?:\.\d+)?)',
                      r.stderr.decode('utf-8', 'replace'))
        if m:
            return int(m.group(1)) * 3600 + int(m.group(2)) * 60 + float(m.group(3))
    except Exception:
        pass
    return None


# 快速模式允许的关键帧对齐误差：短片段要求更严，长片段适当放宽，上限 2 秒
def fast_tolerance(seg_len):
    return min(2.0, max(0.5, seg_len * 0.15))


def _fast_mismatch(seg_path, a, b):
    got = media_duration(seg_path)
    return bool(got and got - (b - a) > fast_tolerance(b - a))


def do_export(job):
    """跑一个导出任务。片段若已被后台预编码，这里只剩拼接，几乎瞬间完成。"""
    src = job['src']
    segments = job['segments']
    mode = job['mode']
    outpath = job['output']
    total = sum(b - a for a, b in segments)
    tmpd = os.path.join(TMP, job['id'])
    # 先写到同目录下的 .part 文件，成功后改名；中途失败不会留下半成品
    stem, ext = os.path.splitext(outpath)
    part = '%s.part%s' % (stem, ext)
    safe_unlink(part)
    parts = []
    fell_back = 0
    reused = 0
    encoder = detect_encoder()
    try:
        # 等这部片子自己的段预编码完（后台队列已把这个源排到最前）
        pending, _busy = prewarm_pending(src)
        if pending:
            job_update(job, message='等待预编码 %d 段…' % pending)
        prewarm_wait_src(src, 900,
                         lambda d, t: job_update(
                             job, message='等待预编码 %d/%d 段…' % (d, t),
                             pct=min(0.4, d / max(1, t) * 0.4)))
        with LOCK:
            PREWARM['paused'] = True     # 导出期间别再抢磁盘
        prewarm_pause_wait(5)

        os.makedirs(tmpd, exist_ok=True)
        done = 0.0
        for i, (a, b) in enumerate(segments):
            base = seg_base(src, a, b)
            enc = encoder_args(encoder, max_kbps=src_maxrate(src))
            seg_path = cache_file(src, a, b, encoder)

            def pct(p, _d=done):
                job_update(job, pct=min(0.97, 0.4 + (_d + p * (b - a)) / total * 0.57))

            # 标注时已经后台编好，直接用，省掉这段全部编码时间
            if os.path.exists(seg_path) and os.path.getsize(seg_path) > 1024 \
                    and not (mode == 'fast' and _fast_mismatch(seg_path, a, b)):
                job_update(job, message='片段 %d/%d 已就绪' % (i + 1, len(segments)))
                parts.append(seg_path)
                done += (b - a)
                reused += 1
                job_update(job, pct=min(0.97, 0.4 + done / total * 0.57))
                continue

            job_update(job, message='处理片段 %d/%d …' % (i + 1, len(segments)))
            seg_path = os.path.join(tmpd, 'seg%03d.mp4' % i)

            if mode == 'fast':
                ffmpeg_progress(base + ['-c', 'copy', seg_path], b - a, pct)
                got = media_duration(seg_path)
                if got and got - (b - a) > fast_tolerance(b - a):
                    # 关键帧太稀：这段直接复制会多带一大截，改走精确重编码
                    job_update(job, message='片段 %d 关键帧过稀，改用精确裁剪…' % (i + 1))
                    safe_unlink(seg_path)
                    ffmpeg_progress(base + enc + [seg_path], b - a, pct)
                    fell_back += 1
            else:
                ffmpeg_progress(base + enc + [seg_path], b - a, pct)

            parts.append(seg_path)
            done += (b - a)

        job_update(job, message='合并片段…', pct=0.98)
        listfile = os.path.join(tmpd, 'list.txt')
        with open(listfile, 'w', encoding='utf-8') as f:
            for p in parts:
                f.write("file '%s'\n" % p.replace('\\', '/').replace("'", r"'\''"))
        if len(parts) == 1 and outpath.lower().endswith('.mp4'):
            shutil.copyfile(parts[0], part)
        else:
            # 走 concat 复用一次封装，能保证输出容器（mkv/ts…）与扩展名一致
            flags = (['-movflags', '+faststart']
                     if outpath.lower().endswith(('.mp4', '.mov', '.m4v')) else [])
            ffmpeg_progress(['-f', 'concat', '-safe', '0', '-i', listfile,
                             '-c', 'copy', '-fflags', '+genpts'] + flags + [part], 0, None)
        os.replace(part, outpath)

        actual = media_duration(outpath)
        msg = '完成'
        if actual:
            msg = '完成（成片 %s，标注 %s）' % (fmt_sec(actual), fmt_sec(total))
        if fell_back:
            msg += '，%d 段关键帧过稀已自动精确裁剪' % fell_back
        if reused == len(segments):
            msg += '（片段已预编码，直接拼接）'
        # 成片已经落盘且校验过，勾了「删除原片」才动手
        deleted = False
        if job.get('del_src'):
            cdir = cache_dir_for(src)      # 得在删之前算，删完指纹就变了
            note = delete_source(src, outpath)
            if note:
                msg += '，' + note
            if note.startswith('原片已'):
                deleted = True
                lib_forget(src)
                drop_project(src)
                shutil.rmtree(cdir, ignore_errors=True)
                try:
                    pxy = PROXIES.pop(os.path.abspath(src).lower(), '')
                    if pxy:
                        safe_unlink(pxy)
                except Exception:
                    pass
                if STATE.get('video') and os.path.abspath(STATE['video']) == src:
                    STATE['video'] = None
        log_export(src, outpath, actual or total,
                   '原片已删' if deleted else ('' if not job.get('del_src') else '原片保留'))
        size = 0
        try:
            size = os.path.getsize(outpath)
        except OSError:
            pass
        job_update(job, status='done', pct=1.0, message=msg, output=outpath,
                   t1=time.time(), size=size, deleted=deleted)
    except Exception as e:
        safe_unlink(part)
        job_update(job, status='error', error=str(e), message='失败', t1=time.time())
    finally:
        shutil.rmtree(tmpd, ignore_errors=True)
        with LOCK:
            PREWARM['paused'] = False
        PREWARM_WAKE.set()
        cache_gc(force=True)


def fmt_sec(t):
    if t < 60:
        return '%.1fs' % t
    return '%d:%04.1f' % (int(t // 60), t % 60)


# ----------------------------------------------------------------------------
# 标注工程持久化
# ----------------------------------------------------------------------------
def load_projects():
    global PROJECTS
    try:
        with open(PROJ_FILE, 'r', encoding='utf-8') as f:
            d = json.load(f)
        if isinstance(d, dict):
            PROJECTS = d
    except Exception:
        PROJECTS = {}


def touch_projects():
    global PROJ_NEED_SAVE
    with PROJ_LOCK:
        PROJ_NEED_SAVE = True


def projects_flusher():
    """每 2 秒把改动落盘一次，拖时间轴时不会疯狂写文件"""
    global PROJ_NEED_SAVE
    while True:
        time.sleep(2)
        with PROJ_LOCK:
            if not PROJ_NEED_SAVE:
                continue
            PROJ_NEED_SAVE = False
            data = json.dumps(PROJECTS, ensure_ascii=False)
        try:
            os.makedirs(DATA, exist_ok=True)
            tmp = PROJ_FILE + '.tmp'
            with open(tmp, 'w', encoding='utf-8') as f:
                f.write(data)
            os.replace(tmp, PROJ_FILE)
        except Exception:
            pass


def put_project(path, entry):
    """合并一条标注记录；ts 新的覆盖旧的"""
    if not path:
        return
    with PROJ_LOCK:
        old = PROJECTS.get(path) or {}
        ts = int(entry.get('ts') or 0)
        if ts and ts < int(old.get('ts') or 0):
            return
        cur = {'segs': [], 'dirty': False, 'done': False, 'out': '', 'ts': ts}
        segs = []
        for s in entry.get('segs') or []:
            try:
                a, b = float(s[0]), float(s[1])
            except Exception:
                continue
            if b - a > 0.02 and a >= 0:
                segs.append([round(a, 3), round(b, 3)])
        cur['segs'] = sorted(segs)[:2000]
        cur['dirty'] = bool(entry.get('dirty'))
        cur['done'] = bool(entry.get('done'))
        cur['out'] = str(entry.get('out') or '')[:500]
        PROJECTS[path] = cur
    touch_projects()


threading.Thread(target=projects_flusher, name='projects', daemon=True).start()



PROXY_DIR = os.path.join(TMP, 'proxy')
PROXIES = {}          # 源文件绝对路径(小写) -> 代理文件；本次运行内复用，切走再切回不用重编
PROXY_READY = set()   # 已经有代理文件的片子（小写绝对路径），列表上打 ⚡ 用


def proxy_path(src):
    try:
        return os.path.join(PROXY_DIR, '%s.mp4' % src_fingerprint(src))
    except Exception:
        return os.path.join(PROXY_DIR, 'p_%s.mp4' % uuid.uuid4().hex[:10])


def proxy_encoder_args(info):
    """预览代理专用：0.5 秒一个关键帧，跳转几乎零延迟；编码尽量快

    现在是默认播放源了，画质比当初（cq28）提一档到 cq24 —— 实测只慢 10%，
    渐变和暗部不至于糊成块。
    """
    fps = float(info.get('fps') or 30)
    gop = max(6, int(round(fps * 0.5)))
    enc = detect_encoder()
    if enc == 'nvenc':
        v = ['-c:v', 'h264_nvenc', '-preset', 'p3', '-tune', 'hq', '-rc', 'vbr',
             '-cq', '24', '-b:v', '0', '-maxrate', '6000k', '-bufsize', '12000k']
    elif enc == 'qsv':
        v = ['-c:v', 'h264_qsv', '-preset', 'veryfast', '-global_quality', '24']
    elif enc == 'amf':
        v = ['-c:v', 'h264_amf', '-quality', 'speed', '-rc', 'cqp',
             '-qp_i', '24', '-qp_p', '26']
    else:
        v = ['-c:v', 'libx264', '-preset', 'veryfast', '-crf', '25']
    return (['-vf', "scale='min(1280,iw)':-2",
             '-g', str(gop), '-keyint_min', str(gop), '-sc_threshold', '0',
             '-pix_fmt', 'yuv420p'] + v +
            ['-c:a', 'aac', '-b:a', '128k', '-movflags', '+faststart'])


def mark_proxy(src, out):
    key = os.path.abspath(src).lower()
    with LOCK:
        PROXIES[key] = out
        PROXY_READY.add(key)
        cur = STATE.get('video')
        if cur and os.path.abspath(cur).lower() == key:
            STATE['proxy'] = out


def _proxy_cached(src):
    """这次运行里编过、或者上次留在 _tmp/proxy 里的，都算命中"""
    out = PROXIES.get(os.path.abspath(src).lower())
    if out and os.path.isfile(out) and os.path.getsize(out) > 4096:
        return out
    try:
        p = proxy_path(src)
    except Exception:
        return None
    if os.path.exists(p) and os.path.getsize(p) > 4096:
        return p
    return None


def do_proxy(job, src, out=None):
    info = probe(src)
    d = info.get('duration') or 0
    out = out or proxy_path(src)
    os.makedirs(os.path.dirname(out), exist_ok=True)
    hit = _proxy_cached(src)
    if hit:
        mark_proxy(src, hit)
        job_update(job, status='done', pct=1.0, message='预览已就绪', output=hit, t1=time.time())
        return
    tmp = out + '.part.mp4'
    safe_unlink(tmp)
    args = (['-i', src, '-map', '0:v:0', '-map', '0:a:0?']
            + proxy_encoder_args(info) + [tmp])
    try:
        ffmpeg_progress(args, d, lambda p: job_update(job, pct=p, message='生成顺滑预览…'),
                        low_priority=True)
        os.replace(tmp, out)
        mark_proxy(src, out)
        job_update(job, status='done', pct=1.0, message='预览已就绪', output=out, t1=time.time())
    except Exception as e:
        safe_unlink(tmp)
        job_update(job, status='error', error=str(e), message='失败', t1=time.time())


# ----------------------------------------------------------------------------
# 顺滑预览队列 —— 现在默认就给每部片子生成，所以要排队、去重、低优先级，
# 用户切走再切回来不会重复编，也不会一次开十几路 ffmpeg 把机器拖死。
# ----------------------------------------------------------------------------
PROXY_QLOCK = threading.Lock()
PROXY_Q = []          # src 列表，队首优先
PROXY_JOBS = {}       # src -> job
PROXY_FAIL = set()    # 编不出来的片子，别每次打开都白试一遍


def ensure_proxy(src, auto=False):
    """确保这部片子的顺滑预览在排队/已就绪；返回 (job 或 None, 是否已就绪)"""
    if not FFMPEG or not src:
        return None, False
    src = os.path.abspath(src)
    if src in PROXY_FAIL:
        return None, False
    hit = _proxy_cached(src)
    if hit:
        mark_proxy(src, hit)
        return None, True
    with PROXY_QLOCK:
        j = PROXY_JOBS.get(src)
        if j:
            # 用户切回来了：把这部提到队首，别让他在后面干等
            if src in PROXY_Q:
                PROXY_Q.remove(src)
                PROXY_Q.insert(0, src)
            return j, False
        j = new_job('proxy', '顺滑预览', src=src, name=os.path.basename(src), auto=bool(auto))
        PROXY_JOBS[src] = j
        PROXY_Q.insert(0, src)
        # 队列只留最近切换的几部，更早的丢掉（以后再打开会重新排）
        # 上限 8 = 正在看的 1 部 + 预编的后 2 部 + 之前没编完的几部
        while len(PROXY_Q) > 8:
            drop = PROXY_Q.pop()
            old = PROXY_JOBS.pop(drop, None)
            if old and old.get('status') == 'queued':
                job_update(old, status='done', pct=1.0, message='已跳过')
        return j, False


# ----------------------------------------------------------------------------
# 预编后两部的顺滑预览
#   一部一部往下标的场景里，等切过去再开始编就晚了 —— 每打开一部，顺手把它后面
#   两部的预览排到队尾（不抢正在看的这部，也不影响导出）。
#   切过去时命中缓存，0 等待。
# ----------------------------------------------------------------------------
PREFETCH_N = 2


def _video_siblings(src):
    """没扫资源库时，拿同文件夹里排在这部后面的视频当"下一部" """
    d = os.path.dirname(os.path.abspath(src))
    out = []
    try:
        with os.scandir(d) as it:
            for e in it:
                try:
                    if not e.is_file():
                        continue
                except OSError:
                    continue
                base, ext = os.path.splitext(e.name)
                if ext.lower() not in VIDEO_EXT or SPLIT_SUFFIX_RE.search(base):
                    continue
                try:
                    sz = e.stat().st_size
                except OSError:
                    sz = 0
                out.append({'path': e.path, 'name': e.name, 'dur': 0.0, 'size': sz})
    except OSError:
        return []
    out.sort(key=lambda it: nat_key(it['name']))
    return out


def _video_queue():
    """往后翻的顺序表：优先用扫好的资源库；没有就用当前片子的同文件夹兄弟"""
    with LOCK:
        if LIB['items']:
            return [dict(it) for it in LIB['items']]
    return []


def _find_in(seq, key):
    for i, it in enumerate(seq):
        try:
            if os.path.abspath(it['path']).lower() == key:
                return i
        except Exception:
            continue
    return -1


def prefetch_neighbors(src, n=PREFETCH_N):
    """把 src 后面 n 部的顺滑预览排到队尾，返回 [名字] 方便回显/测试"""
    if not FFMPEG or not src:
        return []
    src = os.path.abspath(src)
    key = src.lower()
    seq = _video_queue()
    idx = _find_in(seq, key)
    if idx < 0:
        # 扫的文件夹里没有这部（单文件打开的）：就按同文件夹的自然顺序往后取
        seq = _video_siblings(src)
        idx = _find_in(seq, key)
    if idx < 0 or idx + 1 >= len(seq):
        return []
    queued = []
    for it in seq[idx + 1: idx + 1 + n]:
        try:
            p = os.path.abspath(it['path'])
        except Exception:
            continue
        if p in PROXY_FAIL:
            continue
        dur = it.get('dur') or 0
        if dur > 4 * 3600:          # 和打开时同一套门槛，超长的不接
            continue
        hit = _proxy_cached(p)
        if hit:                      # 已经备好了，登记一下让它显示 ⚡
            mark_proxy(p, hit)
            continue
        if not os.path.isfile(p):
            continue
        with PROXY_QLOCK:
            if p in PROXY_JOBS or p in PROXY_Q:
                continue             # 正在排/正在编，别重复
            if len(PROXY_Q) >= 8:
                break                # 队里积太多了，这一轮就不贪了
            job = new_job('proxy', '顺滑预览', src=p, name=it['name'],
                          auto=True, prefetch=True)
            PROXY_JOBS[p] = job
            PROXY_Q.append(p)         # 队尾：不抢正在看的这部
        queued.append(it['name'])
    return queued


def prefetch_soon(src):
    """开片/切片时顺手排一下，别让它在 HTTP 响应里等"""
    if not src:
        return

    def run():
        try:
            prefetch_neighbors(src)
        except Exception:
            pass

    threading.Thread(target=run, daemon=True).start()


LIB_IDX = {'sig': None, 'map': {}}


def proxy_ready_indices():
    """资源库里哪些片子的预览已备好 —— 前端在列表行首打 ⚡"""
    with LOCK:
        gen = LIB['gen']
        items = LIB['items']
        ready = list(PROXY_READY)
    sig = (gen, len(items))
    if LIB_IDX['sig'] != sig:
        LIB_IDX['map'] = {os.path.abspath(it['path']).lower(): i
                          for i, it in enumerate(items)}
        LIB_IDX['sig'] = sig
    m = LIB_IDX['map']
    out = [m[p] for p in ready if p in m]
    out.sort()
    return out[:600]


def proxy_progress(src):
    """当前这部片子的顺滑预览状态，前端直接拿去画提示条"""
    out = {'busy': False, 'pct': 0.0, 'ready': False, 'jobId': ''}

    if not src:
        return out
    key = os.path.abspath(src)
    with PROXY_QLOCK:
        job = PROXY_JOBS.get(key)
    with LOCK:
        ready = bool(STATE['proxy']) and \
            (os.path.abspath(STATE['video'] or '').lower() == key.lower())
    out['ready'] = ready
    if job:
        out['busy'] = job.get('status') in ('queued', 'running')
        out['pct'] = round(float(job.get('pct') or 0), 4)
        out['jobId'] = job.get('id') or ''
    return out


def proxy_worker():
    while True:
        src = None
        with PROXY_QLOCK:
            if PROXY_Q:
                src = PROXY_Q.pop(0)
        if not src:
            time.sleep(0.2)
            continue
        with PROXY_QLOCK:
            # 不能从 PROXY_JOBS 里摘掉：前端靠它读实时进度
            job = PROXY_JOBS.get(src)
        if not job:
            continue
        job_update(job, status='running', message='生成顺滑预览…')
        try:
            do_proxy(job, src)
        except Exception as e:
            job_update(job, status='error', error=str(e), message='失败', t1=time.time())
        finally:
            with PROXY_QLOCK:
                if job.get('status') == 'error':
                    PROXY_FAIL.add(src)
                if PROXY_JOBS.get(src) is job:
                    PROXY_JOBS.pop(src, None)


threading.Thread(target=proxy_worker, name='proxy', daemon=True).start()


# ----------------------------------------------------------------------------
# 关键帧索引
#   实测：跳转耗时 ≈ 12ms + 1.4ms × 目标离前面那个关键帧的帧数。
#   8 秒 GOP 跳一次 350ms，落到关键帧上只要 15ms。所以「先跳关键帧、再精确」，
#   看到画面是瞬间的，精确那一下在后台补。
# ----------------------------------------------------------------------------
KF_CACHE = {}
KF_BUSY = set()
KF_MAX = 4000


def keyframe_times(path):
    """整片关键帧时间点（秒），太多就抽稀"""
    ck = _pkey(path)
    if ck and ck in KF_CACHE:
        return KF_CACHE[ck]
    ts = []
    if FFMPEG:
        try:
            r = run_cmd([FFMPEG, '-hide_banner', '-nostats', '-skip_frame', 'nokey',
                         '-i', path, '-map', '0:v:0', '-vf', 'showinfo',
                         '-f', 'null', '-'], timeout=180)
            found = sorted({round(float(x), 3) for x in
                            re.findall(r'pts_time:\s*([0-9]+(?:\.[0-9]+)?)',
                                       r.stderr.decode('utf-8', 'replace'))})
            if len(found) > KF_MAX:
                step = len(found) / float(KF_MAX)
                found = [found[int(i * step)] for i in range(KF_MAX)]
            ts = found
        except Exception:
            ts = []
    if ck:
        KF_CACHE[ck] = ts
    return ts


def start_keyframe_index(path):
    """后台算关键帧索引，前端轮询 /api/keyframes 取"""
    key = os.path.abspath(path).lower()
    with LOCK:
        ck = _pkey(path)
        if not ck or ck in KF_CACHE or key in KF_BUSY:
            return
        KF_BUSY.add(key)
    try:
        keyframe_times(path)
    finally:
        with LOCK:
            KF_BUSY.discard(key)


def keyframes_payload(path):
    if not path:
        return {'ok': True, 'times': [], 'ready': False}
    ck = _pkey(path)
    if ck and ck in KF_CACHE:
        return {'ok': True, 'times': KF_CACHE[ck], 'ready': True}
    start_keyframe_index(path)
    return {'ok': True, 'times': [], 'ready': False}




# ----------------------------------------------------------------------------
# 文件夹递归扫描
# ----------------------------------------------------------------------------
def nat_key(s):
    """EP2 排在 EP10 前面"""
    return [int(t) if t.isdigit() else t.lower() for t in NAT_RE.split(s)]


def scan_videos(root):
    """递归列出 root 下所有视频；跳过自己导出的成片和系统/垃圾目录"""
    root = os.path.abspath(root)
    items = []
    try:
        for dirpath, dirnames, filenames in os.walk(root, onerror=lambda e: None):
            dirnames[:] = [d for d in dirnames
                           if d.lower() not in SKIP_SCAN and not d.startswith('.')]
            for fn in filenames:
                ext = os.path.splitext(fn)[1].lower()
                if ext not in VIDEO_EXT:
                    continue
                if SPLIT_SUFFIX_RE.search(os.path.splitext(fn)[0]):
                    continue
                p = os.path.join(dirpath, fn)
                try:
                    sz = os.path.getsize(p)
                except OSError:
                    continue
                rel = os.path.relpath(p, root)
                it = {'path': p, 'name': fn, 'rel': rel,
                      'sub': os.path.dirname(rel), 'size': sz,
                      'dur': 0.0, 'fps': 0.0, 'w': 0, 'h': 0, 'probed': False}
                ck = _pkey(p)
                info = PROBE_CACHE.get(ck) if ck else None
                if info:
                    it.update({'dur': round(info['duration'], 2),
                               'fps': round(info['fps'], 2),
                               'w': info['width'], 'h': info['height'], 'probed': True})
                items.append(it)
    except Exception:
        pass
    items.sort(key=lambda it: nat_key(it['rel']))
    return items


def probe_library(gen, items):
    """后台补时长/分辨率：4 个并发探，探到一条推一条，界面能实时刷新"""
    todo = [it for it in items if not it['probed']]
    if not todo:
        with LOCK:
            if LIB['gen'] == gen:
                LIB['scanning'] = False
        return
    pos = [0]

    def work():
        while True:
            if LIB['gen'] != gen:
                return
            with LOCK:
                if pos[0] >= len(todo):
                    return
                it = todo[pos[0]]
                pos[0] += 1
            info = probe(it['path'])
            with LOCK:
                if LIB['gen'] != gen:
                    return
                it.update({'dur': round(info.get('duration') or 0, 2),
                           'fps': round(info.get('fps') or 0, 2),
                           'w': info.get('width') or 0, 'h': info.get('height') or 0,
                           'probed': True})
                LIB['scanned'] += 1
                if LIB['scanned'] >= len(items):
                    LIB['scanning'] = False

    for _ in range(min(4, len(todo))):
        threading.Thread(target=work, daemon=True).start()


def library_payload(full=True):
    with LOCK:
        items = LIB['items']
        base = {'root': LIB['root'], 'total': len(items),
                'scanning': bool(LIB['scanning']), 'scanned': LIB['scanned']}
        if full:
            base['items'] = [dict(it) for it in items]
    return base



OFN_READONLY = 0x00000001
OFN_OVERWRITEPROMPT = 0x00000002
OFN_NOCHANGEDIR = 0x00000008
OFN_PATHMUSTEXIST = 0x00000800
OFN_FILEMUSTEXIST = 0x00001000
OFN_EXPLORER = 0x00080000


def pick_file_win32(title='选择视频文件', initial=''):
    """调用 comdlg32!GetOpenFileNameW。返回路径，取消返回 ''。"""
    import ctypes
    from ctypes import wintypes

    class OPENFILENAMEW(ctypes.Structure):
        _fields_ = [
            ('lStructSize', wintypes.DWORD), ('hwndOwner', wintypes.HWND),
            ('hInstance', wintypes.HINSTANCE), ('lpstrFilter', wintypes.LPCWSTR),
            ('lpstrCustomFilter', wintypes.LPWSTR), ('nMaxCustFilter', wintypes.DWORD),
            ('nFilterIndex', wintypes.DWORD), ('lpstrFile', wintypes.LPWSTR),
            ('nMaxFile', wintypes.DWORD), ('lpstrFileTitle', wintypes.LPWSTR),
            ('nMaxFileTitle', wintypes.DWORD), ('lpstrInitialDir', wintypes.LPCWSTR),
            ('lpstrTitle', wintypes.LPCWSTR), ('Flags', wintypes.DWORD),
            ('nFileOffset', wintypes.WORD), ('nFileExtension', wintypes.WORD),
            ('lpstrDefExt', wintypes.LPCWSTR), ('lCustData', wintypes.LPARAM),
            ('lpfnHook', wintypes.LPVOID), ('lpTemplateName', wintypes.LPCWSTR),
            ('pvReserved', wintypes.LPVOID), ('dwReserved', wintypes.DWORD),
            ('FlagsEx', wintypes.DWORD),
        ]

    buf = ctypes.create_unicode_buffer(2048)
    flt = ('视频文件\0*.mp4;*.mkv;*.mov;*.avi;*.flv;*.ts;*.m4v;*.webm;*.wmv;*.mpg;*.mpeg;*.m2ts\0'
           '所有文件\0*.*\0\0')
    ofn = OPENFILENAMEW()
    ofn.lStructSize = ctypes.sizeof(OPENFILENAMEW)
    try:
        fg = ctypes.windll.user32.GetForegroundWindow()
        ofn.hwndOwner = fg if fg else None
    except Exception:
        ofn.hwndOwner = None
    ofn.lpstrFilter = flt
    ofn.lpstrFile = ctypes.cast(buf, wintypes.LPWSTR)
    ofn.nMaxFile = 2048
    ofn.lpstrTitle = title
    ofn.lpstrInitialDir = initial or None
    ofn.Flags = OFN_EXPLORER | OFN_FILEMUSTEXIST | OFN_PATHMUSTEXIST | OFN_NOCHANGEDIR
    try:
        ok = ctypes.windll.comdlg32.GetOpenFileNameW(ctypes.byref(ofn))
    except Exception as e:
        print('[dialog error]', e)
        return ''
    return buf.value if ok else ''


def pick_dir_win32(title='选择输出文件夹', initial=''):
    """没有 tkinter 时用 PowerShell 的 FolderBrowserDialog 兜底"""
    ps = ("[Console]::OutputEncoding=[System.Text.Encoding]::UTF8;"
          "Add-Type -AssemblyName System.Windows.Forms;"
          "$d=New-Object System.Windows.Forms.FolderBrowserDialog;"
          "$d.Description='%s';" % title)
    if initial:
        ps += "$d.SelectedPath='%s';" % initial.replace("'", "''")
    ps += "if($d.ShowDialog() -eq 'OK'){Write-Output $d.SelectedPath}"
    kw = {}
    if CREATE_NO_WINDOW:
        kw['creationflags'] = CREATE_NO_WINDOW
    try:
        r = subprocess.run(['powershell', '-NoProfile', '-STA', '-Command', ps],
                           capture_output=True, timeout=300, **kw)
        return (r.stdout or b'').decode('utf-8', 'replace').strip()
    except Exception as e:
        print('[dir dialog error]', e)
        return ''


def pick_file():
    if os.name == 'nt':
        return pick_file_win32()
    try:
        import tkinter as tk
        from tkinter import filedialog
        r = tk.Tk(); r.withdraw(); r.attributes('-topmost', True)
        p = filedialog.askopenfilename()
        r.destroy()
        return p or ''
    except Exception:
        return ''


def pick_dir(initial='', title='选择输出文件夹'):
    if os.name == 'nt':
        return pick_dir_win32(title=title, initial=initial)
    try:
        import tkinter as tk
        from tkinter import filedialog
        r = tk.Tk(); r.withdraw(); r.attributes('-topmost', True)
        p = filedialog.askdirectory(title=title)
        r.destroy()
        return p or ''
    except Exception:
        return ''


# ----------------------------------------------------------------------------
# HTTP 服务
# ----------------------------------------------------------------------------
class Handler(BaseHTTPRequestHandler):
    protocol_version = 'HTTP/1.1'
    server_version = 'VideoCutter/1.0'

    def log_message(self, *args):
        pass

    # ---------- 工具 ----------
    def _json(self, obj, code=200):
        body = json.dumps(obj, ensure_ascii=False).encode('utf-8')
        self.send_response(code)
        self.send_header('Content-Type', 'application/json; charset=utf-8')
        self.send_header('Content-Length', str(len(body)))
        self.send_header('Cache-Control', 'no-store')
        self.end_headers()
        try:
            self.wfile.write(body)
        except Exception:
            pass

    def _err(self, msg, code=400):
        self._json({'ok': False, 'error': msg}, code)

    def _read_body(self):
        n = int(self.headers.get('Content-Length') or 0)
        if n <= 0:
            return {}
        raw = self.rfile.read(n)
        try:
            return json.loads(raw.decode('utf-8'))
        except Exception:
            return {}

    def _file(self, path, ctype=None):
        if not path or not os.path.isfile(path):
            self._err('文件不存在', 404)
            return
        size = os.path.getsize(path)
        ctype = ctype or mimetypes.guess_type(path)[0] or 'application/octet-stream'
        if path.lower().endswith('.mkv'):
            ctype = 'video/x-matroska'
        start, end = 0, size - 1
        code = 200
        rng = self.headers.get('Range')
        if rng:
            m = re.match(r'bytes=(\d*)-(\d*)', rng.strip())
            if m:
                if m.group(1):
                    start = int(m.group(1))
                if m.group(2):
                    end = min(int(m.group(2)), size - 1)
                if not m.group(1) and m.group(2):
                    start = max(0, size - int(m.group(2)))
                    end = size - 1
                if start > end or start >= size:
                    self.send_response(416)
                    self.send_header('Content-Range', 'bytes */%d' % size)
                    self.send_header('Content-Length', '0')
                    self.end_headers()
                    return
                code = 206
        self.send_response(code)
        self.send_header('Content-Type', ctype)
        self.send_header('Accept-Ranges', 'bytes')
        self.send_header('Content-Length', str(end - start + 1))
        if code == 206:
            self.send_header('Content-Range', 'bytes %d-%d/%d' % (start, end, size))
        self.send_header('Cache-Control', 'no-store')
        self.end_headers()
        remaining = end - start + 1
        try:
            with open(path, 'rb') as f:
                f.seek(start)
                while remaining > 0:
                    chunk = f.read(min(1 << 18, remaining))
                    if not chunk:
                        break
                    self.wfile.write(chunk)
                    remaining -= len(chunk)
        except (BrokenPipeError, ConnectionResetError, ConnectionAbortedError):
            pass

    # ---------- 路由 ----------
    def do_GET(self):
        u = urllib.parse.urlparse(self.path)
        p = u.path
        q = urllib.parse.parse_qs(u.query)
        if p in ('/', '/index.html'):
            return self._file(os.path.join(ROOT, 'index.html'), 'text/html; charset=utf-8')
        if p == '/api/state':
            v = STATE['video']
            if v and 'keyint' not in (STATE['info'] or {}):
                threading.Thread(target=detect_seek_info, args=(v,), daemon=True).start()
            data = {
                'ok': True, 'video': v or '',
                'name': os.path.basename(v) if v else '',
                'dir': os.path.dirname(v) if v else '',
                'info': STATE['info'],
                'proxy': bool(STATE['proxy']),
                'proxyUrl': ('/video?p=1' if STATE['proxy'] else ''),
                'proxyWork': proxy_progress(v),
                'pready': proxy_ready_indices(),
                'ffmpeg': os.path.basename(FFMPEG) if FFMPEG else '',
                'hasFfmpeg': bool(FFMPEG),
                'outdir': STATE['outdir'] or default_outdir(v),
                'outname': output_name(v) if v else '',
                'dropped': is_dropped(v),
                'locating': bool(STATE['locating']),
                'origin': STATE['origin'] or '',
                'outdirLocked': bool(STATE['outdir_locked']),
                'encoder': detect_encoder(),
                'hwenc': bool(STATE.get('hwenc', True)),
                'encoderLabel': ENCODER_LABEL.get(detect_encoder(), ''),
                'prewarm': prewarm_summary(v),
                'jobs': jobs_snapshot(),
                'active': active_export_count(),
                'library': library_payload(full=False),
            }
            return self._json(data)
        if p == '/api/status':
            v = STATE['video']
            info = STATE['info'] or {}
            if v and 'keyint' not in info:
                threading.Thread(target=detect_seek_info, args=(v,), daemon=True).start()
            return self._json({'ok': True, 'prewarm': prewarm_summary(v),
                               'jobs': jobs_snapshot(), 'active': active_export_count(),
                               'library': library_payload(full=False),
                               'keyint': info.get('keyint') or 0,
                               'proxyReady': bool(STATE['proxy']),
                               'pready': proxy_ready_indices(),
                               'proxyWork': proxy_progress(v)})
        if p == '/api/jobs':
            return self._json({'ok': True, 'jobs': jobs_snapshot()})
        if p == '/api/keyframes':
            return self._json(keyframes_payload(STATE['video']))
        if p == '/api/projects':
            with PROJ_LOCK:
                data = {k: v for k, v in PROJECTS.items() if v.get('segs')}
            return self._json({'ok': True, 'projects': data})
        if p == '/api/library':
            return self._json({'ok': True, **library_payload(full=True)})
        if p == '/video':
            if q.get('p') and STATE['proxy']:
                return self._file(STATE['proxy'])
            return self._file(STATE['video'])
        if p == '/api/probe':
            v = STATE['video']
            if not v:
                return self._err('未打开视频')
            return self._json({'ok': True, 'info': probe(v)})
        if p == '/favicon.ico':
            self.send_response(204)
            self.send_header('Content-Length', '0')
            self.end_headers()
            return
        return self._err('not found', 404)

    def do_POST(self):
        u = urllib.parse.urlparse(self.path)
        p = u.path
        if p == '/api/open':
            body = self._read_body()
            path = (body.get('path') or '').strip()
            if not path:
                path = pick_file()
            if not path:
                return self._json({'ok': True, 'cancelled': True})
            if not os.path.isfile(path):
                return self._err('文件不存在：%s' % path)
            ext = os.path.splitext(path)[1].lower()
            if ext not in VIDEO_EXT:
                return self._err('不支持的文件类型：%s' % ext)
            STATE['video'] = os.path.abspath(path)
            STATE['proxy'] = None
            STATE['info'] = probe(STATE['video'])
            STATE['locating'] = None
            STATE['origin'] = None
            # 这部之前生成过顺滑预览就直接复用，省掉重新编码
            cached_proxy = _proxy_cached(STATE['video'])
            if cached_proxy:
                mark_proxy(STATE['video'], cached_proxy)
            # 关键帧间隔要解一段才测得出来，放后台，别卡住打开动作
            threading.Thread(target=detect_seek_info, args=(STATE['video'],),
                             daemon=True).start()
            # 默认就做顺滑预览：没缓存就在后台排队编，前端收到 proxyJob 后盯进度，
            # 编完自动切过去（用户手动点过「切回原画质」的片子不会被打扰）
            proxy_job = None
            if not cached_proxy and (STATE['info'].get('duration') or 0) < 4 * 3600:
                try:
                    proxy_job, _ready = ensure_proxy(STATE['video'], auto=True)
                except Exception:
                    proxy_job = None
            # 顺手把后两部的预览排上：切过去就是秒开
            prefetch_soon(STATE['video'])
            # 注意：不清缓存 —— 切走的片子可能还在后台剪/预编码
            d = os.path.dirname(STATE['video'])
            dirs = STATE.setdefault('recent_dirs', [])
            if d in dirs:
                dirs.remove(d)
            dirs.insert(0, d)
            del dirs[6:]
            return self._json({'ok': True, 'path': STATE['video'],
                               'name': os.path.basename(path),
                               'dir': d,
                               'info': STATE['info'],
                               'outname': output_name(STATE['video']),
                               'outdir': STATE['outdir'] or default_outdir(STATE['video']),
                               'proxy': bool(STATE['proxy']),
                               'proxyJob': sanitize_job(proxy_job) if proxy_job else None,
                               'dropped': False})

        if p == '/api/upload':
            # 拖拽上传：图片体直接写入缓存目录
            name = urllib.parse.unquote(q_val(u.query, 'name') or 'video.mp4')
            n = int(self.headers.get('Content-Length') or 0)
            if n <= 0:
                return self._err('空文件')
            updir = os.path.join(TMP, 'drop')
            os.makedirs(updir, exist_ok=True)
            dst = os.path.join(updir, re.sub(r'[\\/:*?"<>|]', '_', name))
            got = 0
            try:
                with open(dst, 'wb') as f:
                    while got < n:
                        chunk = self.rfile.read(min(1 << 20, n - got))
                        if not chunk:
                            break
                        f.write(chunk)
                        got += len(chunk)
            except Exception as e:
                return self._err('上传失败：%s' % e)
            STATE['video'] = dst
            STATE['proxy'] = None
            STATE['info'] = probe(dst)
            STATE['origin'] = None
            size = os.path.getsize(dst)
            try:
                ensure_proxy(dst, auto=True)
            except Exception:
                pass
            threading.Thread(target=locate_in_background,
                             args=(os.path.basename(dst), size, dst), daemon=True).start()
            return self._json({'ok': True, 'path': dst, 'name': name,
                               'dir': os.path.dirname(dst), 'info': STATE['info'],
                               'locating': True,
                               'outname': output_name(dst),
                               'outdir': STATE['outdir'] or default_outdir(dst),
                               'dropped': True})

        if p == '/api/scan-dir':
            body = self._read_body()
            root = (body.get('path') or '').strip().strip('"')
            if not root or not os.path.isdir(root):
                ini = os.path.dirname(STATE['video']) if STATE['video'] else ''
                root = pick_dir(initial=ini, title='选择视频文件夹（会递归所有子文件夹）')
            if not root:
                return self._json({'ok': True, 'cancelled': True})
            root = os.path.abspath(root)
            items = scan_videos(root)
            truncated = False
            if len(items) > 3000:
                items = items[:3000]
                truncated = True
            with LOCK:
                LIB['root'] = root
                LIB['items'] = items
                LIB['gen'] += 1
                gen = LIB['gen']
                LIB['scanned'] = sum(1 for it in items if it['probed'])
                LIB['scanning'] = LIB['scanned'] < len(items)
                scanning = LIB['scanning']
            if items and scanning:
                threading.Thread(target=probe_library, args=(gen, items), daemon=True).start()
            # 已经开着一部片子的话，扫完就知道"后两部"是谁了
            if STATE.get('video'):
                prefetch_soon(STATE['video'])
            dirs = STATE.setdefault('recent_dirs', [])
            if root in dirs:
                dirs.remove(root)
            dirs.insert(0, root)
            del dirs[6:]
            return self._json({'ok': True, 'root': root, 'total': len(items),
                               'truncated': truncated, 'scanning': scanning,
                               'items': [dict(it) for it in items]})

        if p == '/api/pick-outdir':
            d = pick_dir(initial=STATE['outdir'] or default_outdir(STATE['video']))
            if d:
                STATE['outdir'] = os.path.abspath(d)
                STATE['outdir_locked'] = True
            return self._json({'ok': True, 'outdir': STATE['outdir'] or default_outdir(STATE['video']),
                               'outname': output_name(STATE['video']) if STATE['video'] else ''})

        if p == '/api/prewarm':
            body = self._read_body()
            src = STATE['video']
            if not src or not FFMPEG:
                return self._json({'ok': True, 'prewarm': prewarm_summary(src)})
            segs = parse_segments(body.get('segments'))
            queue_prewarm(src, segs, 'accurate' if body.get('mode') != 'fast' else 'fast')
            return self._json({'ok': True, 'prewarm': prewarm_summary(src)})

        if p == '/api/export':
            body = self._read_body()
            src = (body.get('src') or '').strip() or (STATE['video'] or '')
            src = os.path.abspath(src) if src else ''
            if not src or not os.path.isfile(src):
                return self._err('未打开视频')
            if not FFMPEG:
                return self._err('缺少 ffmpeg，无法导出')
            segs = parse_segments(body.get('segments'))
            if not segs:
                return self._err('请先标注至少一个片段')
            segs.sort()
            # 同一部片子已经在剪/排队了，直接复用，不重复提交
            dup = job_for_src(src)
            if dup:
                return self._json({'ok': True, 'dup': True, 'out': dup['output'],
                                   'job': sanitize_job(dup)})
            if active_export_count() >= 30:
                return self._err('后台已经排了 30 个任务，先等几个跑完')
            mode = 'fast' if body.get('mode') == 'fast' else 'accurate'
            outdir = os.path.normpath(os.path.abspath(
                body.get('outdir') or STATE['outdir'] or default_outdir(src)))
            outpath = os.path.join(outdir, output_name(src))
            if os.path.abspath(outpath) == os.path.abspath(src):
                return self._err('输出文件与源文件同名，请换一个输出目录')
            outpath = unique_outpath(outpath, src)
            if os.path.abspath(outdir).lower().startswith(TMP_LOWER):
                return self._err('输出目录不能是工具自己的临时目录（会被自动清理），请选原视频所在文件夹')
            try:
                os.makedirs(outdir, exist_ok=True)
                # 提前验证可写，避免剪辑完才发现没权限
                with open(os.path.join(outdir, '.~write_test'), 'ab'):
                    pass
                safe_unlink(os.path.join(outdir, '.~write_test'))
            except Exception as e:
                return self._err('输出目录不可写：%s' % e)
            job = new_job('export', '剪辑', src=src, name=os.path.basename(src),
                          segments=segs, mode=mode, output=outpath,
                          del_src=bool(body.get('del_src')), deleted=False)
            prewarm_boost(src)          # 这部的段先编，导出时才快
            EXPORT_WAKE.set()
            return self._json({'ok': True, 'job': sanitize_job(job), 'out': outpath})

        if p == '/api/jobs/clear':
            with LOCK:
                for jid in list(JOB_SEQ):
                    j = JOBS.get(jid)
                    if j and j['status'] in ('done', 'error'):
                        JOBS.pop(jid, None)
                        JOB_SEQ.remove(jid)
            return self._json({'ok': True, 'jobs': jobs_snapshot()})

        if p == '/api/projects':
            body = self._read_body()
            path = (body.get('path') or '').strip()
            if not path:
                return self._err('缺少路径')
            put_project(os.path.abspath(path), body.get('entry') or {})
            return self._json({'ok': True})

        if p == '/api/proxy':
            src = STATE['video']
            if not src:
                return self._err('未打开视频')
            job, ready = ensure_proxy(src, auto=False)
            if ready:
                return self._json({'ok': True, 'ready': True, 'job': None})
            return self._json({'ok': True, 'job': sanitize_job(job)})

        if p == '/api/hwenc':
            body = self._read_body()
            on = bool(body.get('on'))
            if active_export_count():
                return self._err('后台还有剪辑任务在跑，等它完成再切换编码器')
            with LOCK:
                STATE['hwenc'] = on
            globals()['ENCODER'] = None      # 让编码器重新探测
            clear_cache()                    # 换了编码器，旧缓存作废
            enc = detect_encoder()
            return self._json({'ok': True, 'hwenc': on, 'encoder': enc,
                               'encoderLabel': ENCODER_LABEL.get(enc, '')})

        if p == '/api/set-outdir':
            body = self._read_body()
            d = (body.get('outdir') or '').strip().strip('"')
            if not d:
                return self._err('路径为空')
            d = os.path.abspath(os.path.expanduser(d))
            try:
                os.makedirs(d, exist_ok=True)
            except Exception as e:
                return self._err('无法创建目录：%s' % e)
            STATE['outdir'] = d
            STATE['outdir_locked'] = True
            return self._json({'ok': True, 'outdir': d})

        if p == '/api/reveal':
            body = self._read_body()
            target = body.get('path') or ''
            if not target:
                done = [j for j in jobs_snapshot() if j['status'] == 'done' and j['output']]
                target = done[0]['output'] if done else ''
            if not target:
                return self._err('没有可打开的位置')
            try:
                if os.name == 'nt':
                    if os.path.isfile(target):
                        subprocess.Popen(['explorer', '/select,%s' % os.path.normpath(target)])
                    else:
                        os.startfile(os.path.dirname(target) or '.')
                else:
                    subprocess.Popen(['xdg-open', os.path.dirname(target) or '.'])
            except Exception as e:
                return self._err(str(e))
            return self._json({'ok': True})

        if p == '/api/quit':
            self._json({'ok': True})
            threading.Timer(0.3, lambda: os._exit(0)).start()
            return

        return self._err('not found', 404)


def q_val(qs, key):
    for part in qs.split('&'):
        if '=' in part:
            k, v = part.split('=', 1)
            if k == key:
                return v
    return ''


def is_dropped(video):
    """是否是拖拽上传（源文件在临时目录里）"""
    if not video:
        return False
    try:
        return os.path.abspath(video).lower().startswith(os.path.abspath(TMP).lower())
    except Exception:
        return False


def default_outdir(video):
    """默认输出到原视频所在文件夹；拖拽上传的文件先尽力反查原目录"""
    if not video:
        return ''
    if is_dropped(video):
        home = os.path.expanduser('~')
        desk = os.path.join(home, 'Desktop')
        return desk if os.path.isdir(desk) else home
    return os.path.dirname(video) or '.'


# ----------------------------------------------------------------------------
# 拖拽进来的文件拿不到原始路径（浏览器安全限制），只能按「同名 + 同大小」
# 到磁盘上反查一次；找到就把输出目录设为原文件夹，并把源切回真实文件。
# ----------------------------------------------------------------------------
SEARCH_SKIP = {'windows', 'program files', 'program files (x86)', 'programdata',
               '$recycle.bin', 'system volume information', 'appdata', 'node_modules',
               '.git', '__pycache__', 'anaconda3', 'miniconda3', '$windows.~bt',
               '$windows.~ws', 'perflogs', 'recovery', 'msocache', 'onedrivetemp'}


TMP_LOWER = os.path.abspath(TMP).lower()


def _search_dir(root, fname, size, max_depth, stop):
    """在 root 下广度优先找同名同大小的文件，返回所在目录"""
    queue = [(root, 0)]
    while queue and not stop.is_set():
        d, depth = queue.pop(0)
        subs = []
        try:
            with os.scandir(d) as it:
                for e in it:
                    if stop.is_set():
                        return None
                    try:
                        if e.is_dir(follow_symlinks=False):
                            if depth < max_depth and e.name.lower() not in SEARCH_SKIP \
                                    and not os.path.abspath(e.path).lower().startswith(TMP_LOWER):
                                subs.append(e.path)
                        elif e.name == fname and e.stat().st_size == size:
                            return d
                    except OSError:
                        continue
        except OSError:
            continue
        queue.extend((p, depth + 1) for p in subs)
    return None


def locate_source(fname, size, timeout=50):
    """反查拖入视频的原目录；多个位置并行搜，谁先命中用谁"""
    home = os.path.expanduser('~')
    roots = []
    for d in STATE.get('recent_dirs') or []:
        if os.path.isdir(d):
            roots.append((d, 3))
    for sub in ('Desktop', 'Downloads', 'Videos', 'Documents', 'Pictures'):
        p = os.path.join(home, sub)
        if os.path.isdir(p):
            roots.append((p, 5))
    for letter in 'CDEFGHIJKLMNOPQRSTUVWXYZ':
        p = letter + ':\\'
        if os.path.isdir(p):
            roots.append((p, 5))
    # 去重，保持顺序
    seen = set()
    roots = [r for r in roots if not (r[0].lower() in seen or seen.add(r[0].lower()))]

    stop = threading.Event()
    found = []

    def work(root, depth):
        hit = _search_dir(root, fname, size, depth, stop)
        if hit and not found:
            found.append(hit)
            stop.set()

    for root, depth in roots:
        threading.Thread(target=work, args=(root, depth), daemon=True).start()
    end = time.time() + timeout
    while time.time() < end and not found:
        time.sleep(0.2)
    stop.set()
    return found[0] if found else None


def locate_in_background(fname, size, dropped_path):
    """上传完成后调用：反查原目录，找到就改写输出目录并把源切回真实文件"""
    try:
        STATE['locating'] = {'name': fname}
        hit = locate_source(fname, size)
        if hit:
            real = os.path.join(hit, fname)
            if os.path.isfile(real) and os.path.getsize(real) == size:
                STATE['origin'] = hit
                if not STATE['outdir_locked']:
                    STATE['outdir'] = hit
                STATE['video'] = real
                STATE['info'] = STATE['info'] or probe(real)
                dirs = STATE.setdefault('recent_dirs', [])
                if hit in dirs:
                    dirs.remove(hit)
                dirs.insert(0, hit)
                del dirs[6:]
                # 临时副本延迟删除，避免正在播放的请求被打断
                threading.Timer(6, lambda: safe_unlink(dropped_path)).start()
                # 源换成真实文件了，顺滑预览要按真文件重排（可能还能直接命中缓存）
                try:
                    ensure_proxy(real, auto=True)
                except Exception:
                    pass
                prefetch_soon(real)
    except Exception:
        pass
    finally:
        STATE['locating'] = None


# 可以安全沿用原扩展名的容器（重编码后是 H.264 + AAC）
KEEP_EXT = {'.mp4', '.m4v', '.mov', '.mkv', '.ts', '.m2ts', '.flv'}
SUFFIX = '剪辑'


def output_name(src):
    """原文件名 + 「剪辑」后缀，扩展名尽量沿用原片"""
    base, ext = os.path.splitext(os.path.basename(src))
    if ext.lower() not in KEEP_EXT:
        ext = '.mp4'
    return '%s_%s%s' % (base, SUFFIX, ext)


# 同一输出目录里可能撞名（不同子文件夹下的 01.mp4）；记住谁占了哪个文件名
_OUT_OWNER = {}
_OUT_LOCK = threading.Lock()


def unique_outpath(outpath, src):
    """被别的源占用了就加 _2、_3…，绝不悄悄覆盖另一部片子的成片"""
    with _OUT_LOCK:
        owner = _OUT_OWNER.get(outpath.lower())
        if owner and owner.lower() != src.lower():
            stem, ext = os.path.splitext(outpath)
            i = 2
            while True:
                cand = '%s_%d%s' % (stem, i, ext)
                o = _OUT_OWNER.get(cand.lower())
                if not o or o.lower() == src.lower():
                    outpath = cand
                    break
                i += 1
        _OUT_OWNER[outpath.lower()] = src
    return outpath


def parse_segments(raw):
    """[a,b] 列表 → [(a,b)]，顺手丢掉太短的"""
    segs = []
    for s in raw or []:
        try:
            a, b = float(s[0]), float(s[1])
        except Exception:
            continue
        if b - a > 0.02:
            segs.append((max(0.0, a), b))
    return segs


def sanitize_job(job):
    if not job:
        return None
    out = {}
    for k in ('id', 'kind', 'label', 'status', 'running', 'pct', 'message', 'output',
              'error', 'src', 'name', 'mode', 't0', 't1', 'size', 'deleted'):
        if k in job:
            out[k] = job[k]
    out['segs'] = len(job.get('segments') or [])
    return out


class Server(ThreadingHTTPServer):
    # Windows 下 SO_REUSEADDR 会让多个进程同时绑同一端口，请求被旧进程接走，
    # 表现出来就是「改了代码却不生效」。这里关掉，让第二个实例直接报错。
    allow_reuse_address = False
    daemon_threads = True

    def handle_error(self, request, client_address):
        # 浏览器关页面/断连是常态，不用刷一屏报错
        e = sys.exc_info()[1]
        if isinstance(e, (ConnectionAbortedError, ConnectionResetError, BrokenPipeError)):
            return
        super().handle_error(request, client_address)


def alive_instance(port):
    """端口上是不是已经跑着本工具（而不是别的程序）"""
    try:
        with urllib.request.urlopen('http://127.0.0.1:%d/api/state' % port, timeout=0.8) as f:
            data = json.loads(f.read().decode('utf-8', 'replace'))
        return bool(data.get('ok') and 'hasFfmpeg' in data)
    except Exception:
        return False


def main():
    if not FFMPEG:
        print('!! 未找到 ffmpeg，导出功能不可用。请把 ffmpeg.exe 放到 bin 目录。')
    os.makedirs(TMP, exist_ok=True)

    # 先判断是不是已经开着了 —— 已经在跑的话绝不能清 _tmp，
    # 否则会把那个实例正在用的缓存和 .part 全删了
    if alive_instance(PORT):
        url = 'http://127.0.0.1:%d/' % PORT
        print('=' * 48)
        print('  工具已经在运行： %s' % url)
        print('  直接打开浏览器即可，不需要重复启动')
        print('=' * 48)
        if not os.environ.get('CUTTER_NO_BROWSER'):
            webbrowser.open(url)
        time.sleep(2.5)
        return

    clean_tmp()
    threading.Thread(target=prune_proxy_cache, daemon=True).start()
    load_projects()

    port = PORT
    for _ in range(20):
        try:
            httpd = Server(('127.0.0.1', port), Handler)
            break
        except OSError:
            port += 1
    else:
        print('端口被占用，无法启动')
        return
    url = 'http://127.0.0.1:%d/' % port
    print('=' * 48)
    print('  视频剪裁工具已启动： %s' % url)
    print('  ffmpeg: %s' % (FFMPEG or '未找到'))
    print('  关闭本窗口即可退出')
    print('=' * 48)
    threading.Timer(0.8, lambda: None if os.environ.get('CUTTER_NO_BROWSER') else webbrowser.open(url)).start()
    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        pass


if __name__ == '__main__':
    main()
