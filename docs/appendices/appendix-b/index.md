# 付録B：ツールインストールガイド

本書のツール実行は、**再現性（環境差の最小化）**を優先し、次の2系統で提供する。

1. **コンテナ（推奨）**：devcontainer で統一環境を用意する  
2. **ローカル**：最小依存（Java/curl/unzip）で実行する

コマンドは代表例であり、配布形式や前提は変更される可能性がある。必要に応じて付録E（一次情報）も参照する。

本付録の手順により、少なくとも **1つのモデルチェック**（Alloy/TLC/Apalache）と、**1つのプログラム検証**（Dafny）を再現できる。

## 対象ツール（最小セット）

- Alloy 6.x（CLI実行）
- TLA+ TLC（tla2tools.jar）
- Apalache（TLA+向け、SMTベース）
- Dafny（検証器）

補足：
- Rocq/Isabelle等の定理証明器は依存が大きいため、本付録では一次情報リンク（付録E）を主とする。
- Lean 4 は、本書の導線として **最小構成のみ**を本付録末尾に示す（Optional）。

## 推奨：devcontainer（コンテナ手順）

前提：
- Docker が利用可能
- devcontainer を扱えるエディタ（例：VS Code + Dev Containers）

手順：
1. 本リポジトリを devcontainer で開く（`.devcontainer/` を利用）
2. 初回起動時に `tools/bootstrap.sh` が実行され、ツールが `tools/.cache/` に配置される
3. 次のコマンドでサンプルを実行する

```bash
# ツール取得（再実行しても可）
bash tools/bootstrap.sh

# Alloy（SATを確認）
bash tools/alloy-check.sh --verbose examples/alloy/collection.als

# TLC（No errorを確認）
bash tools/tlc-run.sh --config examples/tla/QueueBounded.cfg examples/tla/QueueBounded.tla

# Apalache（NoErrorを確認）
bash tools/apalache-check.sh --config examples/apalache/Counter.cfg --length 10 --init Init --next Next --inv Inv examples/apalache/Counter.tla

# Dafny（0 errorsを確認）
bash tools/dafny-verify.sh examples/dafny/Abs.dfy
```

期待される出力（抜粋）：
- Alloy：`SAT`（例：`SAT` を含む行が表示される）
- TLC：`Model checking completed. No error has been found.`
- Apalache：`The outcome is: NoError` および `EXITCODE: OK`
- Dafny：`finished with ... verified, 0 errors`

出力（反例・ログ）は `.artifacts/` 配下に保存される（CIのartifactとしてもアップロードされる）。

## ローカル手順（非コンテナ）

### 前提（Linux/WSL）

- Java 17 以上（TLC/Alloy/Apalacheの実行に必要）
- `curl` / `unzip`

手順は devcontainer と同じで、`bash tools/bootstrap.sh` で必要物を取得し、`tools/*.sh` を実行する。

### OS差分（要点）

- Windows：
  - **WSL2での実行を推奨**（ツール配布物・シェルスクリプトの前提が揃う）
  - WSL側に Java を導入する（Windows側のJavaではなく）
- macOS：
  - `timeout` が標準でないため、`tools/tlc-run.sh --time-limit` を利用するには `gtimeout` 等の提供が必要（例：Homebrewで `coreutils` を導入）。`tools/tlc-run.sh` は `timeout`/`gtimeout` を自動検出する。
  - `tools/bootstrap.sh` が取得するDafnyはLinux向け配布物のため、macOSでは公式配布物（macOS向け）か `dotnet tool` を利用する
- Linux：
  - ディストリ依存でJavaパッケージ名が異なる（例：Ubuntu/Debianは `openjdk-17-jre`）

## Lean 4 環境構築（最小構成 / Optional）

Lean 4 は、本書では「定理証明を資産化し、運用可能にする」選択肢として位置づける（第9章参照）。ここでは **最短・最小構成**として、起動までの導線のみを示す（詳細は一次情報を参照）。

### 事前に理解しておくこと（最小）

- **elan**：Lean toolchain（Lean本体・コンパイラ等）を管理するためのツール
- **Lake**：Lean 4 のビルド/依存管理ツール（プロジェクト作成・ビルドに使用）
- **VS Code拡張**：型チェック結果やゴール表示など、対話的な開発体験を提供

### 手順（代表例）

1. elan を導入する（一次情報）
2. VS Code + Lean 4 拡張を導入する（一次情報）
3. Lean 4 の最小プロジェクトを作成して起動確認する（代表例）

```bash
mkdir -p lean-sandbox && cd lean-sandbox
lake init hello
lake build
```

確認：
- VS Code で `lean-sandbox/` を開き、生成された `.lean` ファイルを開く
- エラーが出ないこと（ツールチェーンが有効であること）を確認する

一次情報（公式/代表）：
- Lean 公式: <https://lean-lang.org/>
- Lean 4（GitHub）: <https://github.com/leanprover/lean4>
- elan: <https://github.com/leanprover/elan>
- VS Code Lean 4 拡張: <https://github.com/leanprover/vscode-lean4>

## CI（自動実行）

GitHub Actions では `.github/workflows/formal-checks.yml` で、PR向け（軽量）と夜間向け（深い探索）のジョブを提供している。  
ローカルで同等の実行をしたい場合は、`bash examples/ci/pr-quick-check.sh` を実行する。
