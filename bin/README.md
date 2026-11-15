# bin/

把 **ffmpeg.exe** 放到这个目录（Windows static build，单个 exe 就够用，不需要 ffprobe）。

下载地址（任选一个，选 `ffmpeg-release-essentials.zip` 或 gyan.dev 的 static 版本）：

- https://www.gyan.dev/ffmpeg/builds/  → `ffmpeg-release-essentials.zip`
- https://github.com/BtbN/FFmpeg-Builds/releases  → `ffmpeg-master-latest-win64-gpl.zip`

解压后把 `bin\ffmpeg.exe` 复制到这里，目录长这样：

```
视频剪裁工具/
└── bin/
    └── ffmpeg.exe
```

也可以不放进这里——只要 `ffmpeg` 在系统 PATH 里，工具会自动找到它。

> 为什么不放进仓库：ffmpeg.exe 有 100MB+，超过 GitHub 单文件 100MB 的限制。
