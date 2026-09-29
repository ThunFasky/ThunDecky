# ThunDecky

Windows 向けのローカル音楽プレーヤー。フォルダ内の音声・動画ファイルをジャケット付きで再生する。

## 構成

```text
src/music.py                アプリ本体
assets/ui/                  UI 画像とアプリアイコン
assets/fonts/               実際に使用するフォント
packaging/ThunDecky.spec   PyInstaller 設定
docs/仕様説明.md             旧称 MyFavMusicBox 時代の仕様メモ
```

## ソースから起動

Windows と Python 3.13 を想定。PowerShell でこのフォルダを開いて実行する。

```powershell
py -3.13 -m venv .venv
.\.venv\Scripts\python.exe -m pip install -r requirements.txt
.\.venv\Scripts\python.exe src\music.py
```

初回起動時に再生するフォルダを選択する。設定 JSON、編集したジャケット、作業用音声は実行したカレントフォルダに生成され、Git から除外される。

## Windows 用ビルド

```powershell
.\.venv\Scripts\python.exe -m pip install -r requirements-build.txt
.\.venv\Scripts\python.exe -m PyInstaller --noconfirm --clean --workpath build --distpath dist packaging\ThunDecky.spec
```

完成した実行ファイルは `dist/ThunDecky/ThunDecky.exe`。`dist/ThunDecky` フォルダ全体を配布する。ビルド成果物や個人の再生履歴は Git に含めない。

## フォントと公開範囲

同梱フォントの出典と条件は [THIRD_PARTY_FONTS.md](THIRD_PARTY_FONTS.md) を参照。このフォルダには実行ファイル、仮想環境、個人設定、サムネイルのバックアップ、音楽ファイルを含めていない。アプリ本体のライセンスは未設定なので、公開時に作者が選んで追加する。
