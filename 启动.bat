@echo off
chcp 65001 >nul
title 视频剪裁工具
cd /d "%~dp0"

where python >nul 2>nul
if errorlevel 1 (
  echo 未找到 Python，请先安装 Python 3 并加入 PATH。
  pause
  exit /b 1
)

echo 正在启动视频剪裁工具...
python app.py
if errorlevel 1 pause
