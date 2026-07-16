---
layout: book
title: "付録B：ツールインストールガイド"
locale: "ja"
lang: "ja"
source_path: "src/ja/appendices/appendix-b.md"
---
# 付録B：ツールインストールガイド

本書のツール実行は、**再現性（環境差の最小化）**を優先し、次の2系統で提供する。

1. **コンテナ（推奨）**：devcontainer で統一環境を用意する
2. **ローカル**：最小依存（Java/curl/unzip）で実行する

コマンドは代表例であり、配布形式や前提は変更される可能性がある。必要に応じて付録E（一次情報）も参照する。

本付録の手順により、少なくとも **1つのモデルチェック**（Alloy/TLC/Apalache）と、**1つのプログラム検証**（Dafny）を再現できる。

## 対象ツール（最小セット）

- Alloy 6.x（CLI実行）
- TLA+ TLC（tla2tools.jar）
- Apalache（TLA+ 向け、SMT ベース）
- Dafny（検証器）

補足：
- Quint CLI は、TLA+ 意味論に基づく型付き仕様言語を CI に載せる選択肢である。ただし本リポジトリの最小セットには含めず、導入する場合は公式手順に従ってバージョンを固定する。
- Rocq/Isabelle等の定理証明器は依存が大きいため、本付録では一次情報リンク（付録E）を主とする。
- Lean 4 は、本書の導線として **最小構成のみ**を本付録末尾に示す（Optional）。
- SPIN / NuSMV / CBMC は `nightly` lane の対象であり、後述する Ubuntu 24.04 x86-64 向け追加前提を満たす場合に実行する。

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

出力（反例・ログ）は `.artifacts/` 配下に保存される（CI のartifactとしてもアップロードされる）。

## ローカル手順（非コンテナ）

### 前提（Linux/WSL）

- Java 17 以上（TLC/Alloy/Apalache の実行に必要）
- `curl` / `unzip`

手順は devcontainer と同じで、`bash tools/bootstrap.sh` で必要物を取得し、`tools/*.sh` を実行する。

### nightly lane の追加前提（Ubuntu 24.04 x86-64）

`node scripts/run-example-manifest.js --lane nightly` は SPIN 6.5.2、NuSMV 2.7.1、CBMC 6.10.0 を実行する。最小セットとは別に、次のビルド前提が必要である。NuSMV は公式 source archive をローカル build し、CBMC は Ubuntu 24.04 x86-64 用の固定 deb を展開するため、この手順は同環境または互換環境を対象とする。

```bash
sudo apt-get update
sudo apt-get install --yes \
  bison build-essential flex g++ gcc m4 patch pkg-config \
  python3 python3-venv xz-utils

python3 -m venv tools/.tmp/nusmv-build-tools
tools/.tmp/nusmv-build-tools/bin/pip install \
  --disable-pip-version-check \
  --require-hashes \
  --requirement tools/nusmv-build-requirements.txt

PATH="$PWD/tools/.tmp/nusmv-build-tools/bin:$PATH" \
  node scripts/run-example-manifest.js --lane nightly
```

取得物は commit/version と SHA-256、Meson/Ninja は requirements の package hash で固定される。macOS、Windows ネイティブ、異なる CPU architecture ではこの lane を直接再現せず、Ubuntu 24.04 x86-64 のコンテナ、WSL2、または GitHub Actions の `workflow_dispatch` を使う。

### OS差分（要点）

- Windows：
  - **WSL2での実行を推奨**（ツール配布物・シェルスクリプトの前提が揃う）
  - WSL側に Java を導入する（Windows側のJavaではなく）
- macOS：
  - `timeout` が標準でないため、`tools/tlc-run.sh --time-limit` を利用するには `gtimeout` 等の提供が必要（例：Homebrewで `coreutils` を導入）。`tools/tlc-run.sh` は `timeout`/`gtimeout` を自動検出する。
  - `tools/bootstrap.sh` が取得する Dafny はLinux向け配布物のため、macOSでは公式配布物（macOS向け）か `dotnet tool` を利用する
- Linux：
  - ディストリ依存でJavaパッケージ名が異なる（例：Ubuntu/Debianは `openjdk-17-jre`）

## TLA+ / Apalache / Quint のエディタ・CLI導線（Optional）

本リポジトリでは `tools/bootstrap.sh` が TLC (`tla2tools.jar`) と Apalache を取得し、次のラッパーでログと成果物を `.artifacts/` に保存する。

```bash
# TLC: .cfg、workers、depth、seed、timeoutを明示できる
bash tools/tlc-run.sh --config examples/tla/QueueBounded.cfg --workers 1 --seed 202606 --time-limit 120 examples/tla/QueueBounded.tla

# Apalache: init/next/invariantと探索長を明示する
bash tools/apalache-check.sh --config examples/apalache/Counter.cfg --length 10 --init Init --next Next --inv Inv examples/apalache/Counter.tla
```

TLA+ をエディタで編集する場合は、VS Code拡張を利用しつつ、拡張、Java、`tla2tools.jar`、`.cfg` の版を PR 本文に記録する。
Quint を導入する場合は、`@informalsystems/quint` のバージョンを `package.json` / lockfile / コンテナ定義等で固定し、`typecheck`、`test`、`verify` を分けて CI に組み込む。
次の断片は導入例であり、本リポジトリではまだ実行対象として固定していない。

```bash
npm install --save-dev @informalsystems/quint@<固定バージョン>
npx quint typecheck specs/example.qnt
npx quint test specs/example.qnt --seed 202606
npx quint verify specs/example.qnt --invariant=Inv --max-steps=10 --out-itf .artifacts/quint/example.itf.json
```

`quint verify` は既定で Apalache を使い、必要に応じて `--backend=tlc` で TLC を使う。
結果を「仕様全体の証明」とは扱わず、対象仕様、backend、境界、seed、timeout、反例 trace の保存場所を合わせて確認する。

## Lean 4 環境構築（最小構成 / Optional）

Lean 4 は、本書では「定理証明を資産化し、運用可能にする」選択肢として位置づける（第9章参照）。ここでは **最短・最小構成**として、起動までの導線のみを示す（詳細は一次情報を参照）。

### 事前に理解しておくこと（最小）

- **elan**：Lean toolchain（Lean 本体・コンパイラ等）を管理するためのツール
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

## 主要ツール別の導入メモ（最小導線）

個別ツールは更新頻度が高いため、本書では完全なインストール手順を固定しない。
導入時は付録Eの一次情報を起点に、次の三点を PR 本文または CI 設定に残す。

1. 公式ドキュメントまたは公式リリースへのリンク
2. 実行したバージョン確認コマンドと結果
3. CI で固定した依存（バイナリ、jar、npm package、opam switch、Rust toolchain、solver、timeout、seed）

| 領域 | ツール | 導入・確認の最小方針 |
| --- | --- | --- |
| Alloy | Alloy 6 Analyzer | 公式リリースから jar を固定し、`java -jar ...` で起動確認する。CI では jar のURL、SHAまたはバージョン、`steps`、scope を記録する。 |
| TLA+ | TLC / VS Code 拡張 | `tla2tools.jar`、Java、`.cfg`、workers、seed、timeout を記録する。VS Code拡張は編集支援であり、CI ではCLI再実行を正本にする。 |
| TLA+ 周辺 | Apalache | 配布zipまたはコンテナを固定し、`apalache-mc version` 相当の出力、探索長、init/next/invariant、solver設定を記録する。 |
| TLA+ 周辺 | Quint | `@informalsystems/quint` を `package.json` / lockfile で固定し、`typecheck`、`test`、`verify` を分ける。backend（Apalache/TLC）と出力traceの保存先を記録する。 |
| 定理証明 | Lean 4 / Lake / mathlib | `elan` で toolchain を固定し、`lake build` を CI で再実行する。`lean-toolchain`、`lake-manifest.json`、mathlibのrevisionを証跡に含める。 |
| 定理証明 | Rocq | 公式リリース/パッケージ手順を使い、Rocq/Coq 互換コマンド名、opam switch、ライブラリ版を記録する。`Admitted.` や不要な公理は CI で棚卸しする。 |
| Rust検証 | Kani | `cargo kani` または公式手順で導入し、`kani --version` 相当、Rust toolchain、proof harness、unwind/探索境界を記録する。 |
| Rust検証 | Verus | 公式配布またはソースビルドのrevision、`verus --version` 相当、Rust toolchain、Z3版、未証明 `assume` を記録する。 |
| Rust検証 | Creusot | 公式ガイドに従い、Creusot、Why3、SMT ソルバー、Rust toolchain、loop invariant / variant、ghost codeの扱いを記録する。 |
| Rust検証 | Prusti | Prusti/Viper、Rust toolchain、事前条件・事後条件・ループ不変条件、counterexample出力を記録する。 |
| Rust検証 | Aeneas | 変換対象のRust subset、Charon/LLBC、接続先（F*、Rocq、HOL4、Lean 等）、生成物のrevisionを記録する。 |
| SMT | cvc5 / Z3 | solver単体の版、呼び出し元ツール、timeout、`unknown` の扱いを記録する。solver差し替え時は結果差分をレビュー対象にする。 |

Cedar、Bedrock Guardrails、スマートコントラクト検証のようなクラウド/産業ツールは、CLI手順よりもサービス仕様の変化が大きい。
導入メモでは、対象API、リージョン、対応言語、ポリシー/仕様の版、検証対象コミット、実行ログを中心に残す。

## CI（自動実行）

GitHub Actions では `.github/workflows/formal-checks.yml` で、PR 向け（軽量）と夜間向け（深い探索）のジョブを提供している。
ローカルで同等の実行をしたい場合は、`bash examples/ci/pr-quick-check.sh` を実行する。
