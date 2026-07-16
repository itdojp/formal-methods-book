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
- Quint CLI は、TLA+ 意味論に基づく型付き仕様言語をCIに載せる選択肢であり、本リポジトリでは固定版のtypecheck/testを`nightly`で実行する。
- Rocq/Isabelle等の定理証明器は依存が大きいため、本付録では一次情報リンク（付録E）を主とする。
- Lean 4 は、本書の導線として **最小構成のみ**を本付録末尾に示す（Optional）。
- SPIN / NuSMV / CBMC / Quint は`nightly` laneの対象であり、source buildが必要なtoolだけ後述するUbuntu 24.04 x86-64向け追加前提を使う。

## Tool lane inventoryと実行保証 {#tool-lane-inventory}

全toolの分類、実行版、配布物digest、artifact上限、更新手順の正本は `tools/tool-manifest.json` である。
`pr-quick` はPR差分に関連する小さい例、`nightly` はtool単位の独立matrix、`optional/manual` は明示的な `workflow_dispatch` だけで実行する。
`documentation-only` は本文で紹介するが、このリポジトリがversion、環境、実行結果を保証しないtool/serviceを表す。
他toolに内蔵されたsolverを間接利用しても、solver単体の実行保証には数えない。

<!-- tool-inventory:start -->
| Tool / service | lane | 検証済み version | 分類理由 |
| --- | --- | --- | --- |
| Alloy Analyzer | pr-quick | 6.2.0 | 小さい scope の4例を短時間で再現できる。 |
| TLC | pr-quick | 1.7.4 | 固定 cfg・worker・seed・timeout で有限モデルを検査する。 |
| Apalache | pr-quick | 0.52.1 | 短い探索長を固定した不変条件検査を毎PRで再現できる。 |
| Dafny | pr-quick | 4.11.0 | 最小検証例が高速で安定している。 |
| SPIN | nightly | 6.5.2 | source buildと状態探索をtool単位nightlyで分離する。 |
| NuSMV | nightly | 2.7.1 | 依存を伴う公式source buildのためnightlyへ分離する。 |
| CBMC | nightly | 6.10.0 | Ubuntu固定配布と有界検査をtool単位nightlyで実行する。 |
| Quint | nightly | 0.32.0 | 公式single binaryでtypecheck/testを固定seedかつTypeScript backendで再現する。 |
| Kani Rust Verifier | optional/manual | 0.67.0 | 固定Rust nightlyを追加取得するため明示的manual dispatchに限定する。 |
| TLA+ Toolbox | documentation-only | — | GUI/編集環境であり、本リポジトリのCLI保証対象外。 |
| TLA+ VS Code extension | documentation-only | — | 編集支援はCLI検査と分離し、extension版を固定していない。 |
| Community Z Tools (CZT) | documentation-only | — | Zの一次情報導線のみで実行assetがない。 |
| FDR | documentation-only | — | CSPM例は掲載するが、配布・licenseを含むCI環境を固定していない。 |
| ProB | documentation-only | — | 紹介のみで実行assetと固定環境がない。 |
| PAT | documentation-only | — | 紹介のみで実行assetと固定環境がない。 |
| nuXmv | documentation-only | — | NuSMVとは別製品として紹介するが、CIはNuSMVだけを保証する。 |
| Java PathFinder | documentation-only | — | 紹介・演習候補のみで実行assetがない。 |
| UPPAAL | documentation-only | — | GUI/license/配布条件を伴い自動化していない。 |
| TIMES | documentation-only | — | リアルタイム検証の紹介のみ。 |
| Rocq / Coq | documentation-only | — | 証明project、opam switch、library版を固定していない。 |
| Lean 4 / Lake / mathlib / elan | documentation-only | — | proof projectと依存revisionがなく、Linux配布物も大きいため未実行。 |
| Isabelle/HOL | documentation-only | — | 紹介のみでsession/build環境を固定していない。 |
| Agda | documentation-only | — | 紹介のみでprojectとlibrary版を固定していない。 |
| HOL4 | documentation-only | — | Aeneas接続先として紹介するだけで実行契約がない。 |
| F* | documentation-only | — | 接続先/関連技術として紹介するだけで実行契約がない。 |
| Frama-C | documentation-only | — | 紹介のみでplugin/solver構成を固定していない。 |
| VeriFast | documentation-only | — | 紹介のみで実行assetがない。 |
| SPARK | documentation-only | — | 産業toolchain/licenseを含む実行環境を固定していない。 |
| Why3 | documentation-only | — | backend solverを含む実行構成を固定していない。 |
| Verus | documentation-only | — | Rust/Z3/revisionを含む実行構成を固定していない。 |
| Creusot | documentation-only | — | Why3/solver/Rustの組合せを固定していない。 |
| Prusti / Viper | documentation-only | — | Rust/Viper toolchainと実行assetを固定していない。 |
| Aeneas / Charon | documentation-only | — | 変換先を含むend-to-end contractを固定していない。 |
| Z3 | documentation-only | — | 他toolの間接依存をsolver単体の実行保証には数えない。 |
| cvc5 / CVC4 | documentation-only | — | 紹介のみでsolver単体assetを固定していない。 |
| Yices | documentation-only | — | 紹介のみで実行assetを固定していない。 |
| MathSAT | documentation-only | — | 紹介のみでlicense/配布を含む環境を固定していない。 |
| SCADE | documentation-only | — | 商用/GUI toolchainでありCI必須化しない。 |
| Simulink | documentation-only | — | 産業事例の紹介のみでlicense環境を固定していない。 |
| SAW | documentation-only | — | 産業事例の参照のみでs2n検証assetを同梱していない。 |
| Cedar Analysis | documentation-only | — | service/APIとtool群が変化し、対象policy assetを固定していない。 |
| Bedrock Guardrails Automated Reasoning checks | documentation-only | — | 外部service、region、API条件を固定CIへ必須化しない。 |
| Solidity SMTChecker | documentation-only | — | Solidity/compiler/solver構成とcontract assetを固定していない。 |
| Aptos Move Prover | documentation-only | — | Move toolchainとcontract assetを固定していない。 |
| Certora Prover | documentation-only | — | 外部/産業toolchainを必須CIへ組み込まない。 |
| LeanDojo | documentation-only | — | AI証明支援の評価基盤として紹介するだけ。 |
| Lean Copilot | documentation-only | — | AI証明支援の紹介のみでmodel/projectを固定していない。 |
| AlphaProof / AlphaGeometry 2 | documentation-only | — | 研究成果の紹介で、再配布可能なCLI契約がない。 |
| DeepSeek-Prover-V2 | documentation-only | — | 研究成果の紹介でmodel/runtimeを固定していない。 |
| ProofGym | documentation-only | — | 評価基盤の紹介のみでdataset/runtimeを固定していない。 |
| APOLLO | documentation-only | — | 研究成果の紹介のみで実行contractがない。 |
<!-- tool-inventory:end -->

実行laneでは、各entryにtimeout、memory budget、seed、scope、depth、boundを明示する。
artifactはtool version、command、入力ファイル別SHA-256と集約hash、exit code、stdout/stderr、`success`、`counterexample`、`unknown`、timeout、resource exhaustionを区別して残す。
保持期間は14日、stdout/stderrは1 entry当たり16 MiB、tool outputは1 entry当たり64 MiBを上限とする。
timeoutとstdout/stderr上限はrunnerが強制し、retained tool outputは実行後に検査する。一方、`memoryMiB`はCI容量計画用の申告値であり、OS/cgroupによる強制上限ではない。このため`resource-exhausted`は検出可能な出力超過を表し、OOM killは`tool-error`またはrunner failureになる場合がある。

- `quint-counter`: [examples/quint/counter.qnt](../../../examples/quint/counter.qnt) をQuint 0.32.0のTypeScript evaluatorでtypecheckし、seed `20260716`、各test 1 sampleで実行する。別配布のRust evaluatorを暗黙downloadしない。
<!-- example-contract: quint-counter -->
【ツール準拠（そのまま動く）】
```bash
node scripts/run-example-manifest.js --id quint-counter
```

- `kani-abs`: [examples/kani/abs.rs](../../../examples/kani/abs.rs) の`abs_is_nonnegative` harnessをKani 0.67.0、固定Rust nightly、unwind 1で検査する。追加downloadと実行コストがあるため`optional/manual`であり、PRやscheduleからは起動しない。

cache復元後もQuint binaryのSHA-256を再検証する。Kaniは検証済みarchiveから毎回再展開し、固定日のRust channel manifestもSHA-256を検証する。Rust component本体の整合性検査は、そのmanifestに記録されたchecksumを検証するrustupに委ねる。
<!-- example-contract: kani-abs -->
【ツール準拠（そのまま動く）】
```bash
node scripts/run-example-manifest.js --id kani-abs
```

version更新は月次に公式release/tagとasset digestを確認し、versionだけの専用PRでclean-cache実行と出力契約差分をレビューする。
任意のrelease assetはDependabot/Renovateのpackage参照ではないため、自動更新されたものとして扱わない。

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

`node scripts/run-example-manifest.js --lane nightly`はSPIN 6.5.2、NuSMV 2.7.1、CBMC 6.10.0、Quint 0.32.0の6 entryを実行する。最小セットとは別に、SPIN/NuSMVのsource buildには次の前提が必要である。CBMCはUbuntu 24.04 x86-64用の固定deb、Quintは同platform用の固定single binaryを使うため、この手順は同環境または互換環境を対象とする。

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
本リポジトリのQuint契約は、公式release binaryとSHA-256を`tools/tool-manifest.json`で固定し、暗黙に追加componentを取得しないTypeScript evaluatorで`typecheck`と`test`を実行する。
`verify`を追加する場合はApalache/TLC backend、JDK、探索境界、timeout、trace artifactを別entryとして固定する。

```bash
node scripts/run-example-manifest.js --id quint-counter
```

`quint-counter`の成功は、対象仕様の型検査と固定testが通ったことだけを表す。
結果を「仕様全体の証明」とは扱わず、verifyを使う場合は対象仕様、backend、境界、seed、timeout、反例traceの保存場所を合わせて確認する。

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
