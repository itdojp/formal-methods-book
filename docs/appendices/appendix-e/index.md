---
layout: book
title: "付録E：参考文献とWebリソース"
description: "レベル別推薦図書リストと最新情報へのリンク"
locale: "ja"
lang: "ja"
source_path: "src/ja/appendices/appendix-e.md"
---
# 付録E：参考文献とWebリソース

本付録は、本文で扱った形式的手法・ツールについて、**一次情報（公式サイト/公式リポジトリ/公式ドキュメント/公式リリース）**へ到達するための索引である。
2026-07 時点で、名称変更・主流ツールの更新（例：Coq→Rocq、CVC4→cvc5、Alloy 6 系、TLA+ の Apalache / Quint 等）を反映している。

## 実行保証の読み方

本付録への掲載は、リポジトリでの実行保証を意味しない。実行状態の正本は
`tools/tool-manifest.json` と[付録Bの lane inventory]({{ '/appendices/appendix-b/#tool-lane-inventory' | relative_url }})である。
Alloy、TLC、Apalache、Dafny は `pr-quick`、SPIN、NuSMV、CBMC、Quint、PRISM、Tamarin、SymbiYosys、cvc5 / Carcara、RTLola は
`nightly`、Kani は明示的な `optional/manual` で検証する。それ以外の掲載ツールは
`documentation-only` であり、本書は固定バージョン、実行環境、実行結果を保証しない。

## 数値の出典ポリシー（本書共通）

- **報告値（実測/事例）**：一次・準一次情報（論文/公式ブログ/公式レポート等）への出典URLを必須とする。
- **例示**：例示であることを明記し、読者が「一般に成立する値」と誤認しない表現にする。
- **不確実な推定**：推定値は避け、必要なら「不確実である」旨と前提条件（スコープ、計測条件）を併記する。

## 1) 仕様記述（Alloy / TLA+ / Z / CSP）

### Alloy（Alloy 6.x）

- 用途：関係モデルの記述と、有限スコープでの反例探索（モデル発見）
- 推奨読者：第4章（Alloy）、第8章（模型検査の考え方）
- 一次情報：
  - 公式サイト：<https://alloytools.org/>
  - Alloy 6 概要（`var`、prime、temporal operator、steps、lasso trace）：<https://alloytools.org/alloy6.html>
  - Alloy Documentation：<https://alloy.readthedocs.io/>
  - Practical Alloy: A temporal logic primer：<https://practicalalloy.github.io/chapters/behavioral-topics/topics/temporal-logic/index.html>
  - リリース（Alloy 6.x）：<https://github.com/AlloyTools/org.alloytools.alloy/releases>

### TLA+（TLC）

- 用途：分散システム/並行システムの状態遷移仕様と、探索による検証（TLC）。新規導入では Toolbox だけでなく、VS Code 拡張と CLI 実行も確認する。
- 推奨読者：第7章（TLA+）、第8章（模型検査）、第12章（ツールと自動化）
- 一次情報：
  - TLA+ 公式（Lamportサイト）：<https://lamport.azurewebsites.net/tla/tla.html>
  - TLA+2（現行版と文書の位置づけ）：<https://lamport.azurewebsites.net/tla/tla2.html>
  - Leslie Lamport, *Specifying Systems*：<https://lamport.azurewebsites.net/tla/book.html>
  - Leslie Lamport, *The Specification Language TLA+*（集合論的な値と意味論）：<https://lamport.azurewebsites.net/pubs/lamport-spec-tla-plus.pdf>
  - Leslie Lamport, *Specifying Systems* chapter draft（TLA+ は untyped、型不変条件を明示）：<https://lamport.azurewebsites.net/pubs/spec-book-chap.pdf>
  - *A PlusCal User's Manual - P-Syntax*（PlusCal translator と TLC の使い方を含む）：<https://lamport.azurewebsites.net/tla/p-manual.pdf>
  - TLA+ Hyperbook：<https://lamport.azurewebsites.net/tla/hyperbook.html>
  - TLA+ Documentation and Tools Guide：<https://docs.tlapl.us/>
  - TLA+ VS Code拡張：<https://marketplace.visualstudio.com/items?itemName=tlaplus.vscode-ide>
  - Current Versions of the TLA+ Tools：<https://github.com/tlaplus/tlaplus/blob/master/general/docs/current-tools.md>
  - tlaplus/tlaplus リリース（tla2tools.jar）：<https://github.com/tlaplus/tlaplus/releases>

### Quint（TLA+ 意味論に基づく型付き仕様言語）

- 用途：TLA的な状態機械仕様を、型付きでプログラミング言語に近い構文として記述し、CLI / REPL / simulation / model checking に接続する
- 推奨読者：第7章（TLA+）、第8章（模型検査）、第12章（CI）
- 注意：TLA+ 本体の置換ではなく、TLA+ の考え方をエンジニアに導入しやすくする表層言語として扱う
- 一次情報：
  - Quint Documentation：<https://quint.sh/docs/lang>
  - Quint CLI Manual：<https://quint.sh/docs/quint>
  - Quint Design principles：<https://quint.sh/docs/design-principles>
  - Quint Model Checkers：<https://quint.sh/docs/model-checkers>

### Z（Z記法）

- 用途：状態ベース仕様（集合/関係/写像）を厳密に記述し、レビューや検証の基盤にする
- 推奨読者：第5章（Z記法）
- 一次情報（実装・ツール）：
  - Community Z Tools (CZT) source repository：<https://github.com/community-z-users/czt>
  - SourceForge（CZTプロジェクト）：<https://sourceforge.net/projects/czt/>

### CSP

- 用途：並行プロセスの通信・同期・デッドロック等の性質を扱う
- 推奨読者：第6章（CSP）
- 一次情報（ツール例）：
  - FDR（CSP模型検査ツール情報）：<https://www.cs.ox.ac.uk/projects/fdr/>

## 2) 模型検査（TLC / Apalache / SPIN / NuSMV / PRISM / SymbiYosys）

### Apalache（TLA+ の追加検査：SMT ベース）

- 用途：TLA+ 仕様に対して、SMT ベースの探索/制約解決で性質検査を行う（TLC と棲み分け）
- 推奨読者：第7章（TLA+）、第8章（模型検査）、第12章（ツールと自動化）
- 一次情報：
  - 公式サイト：<https://apalache-mc.org/>
  - Documentation：<https://apalache-mc.org/docs/>
  - Running the Tool：<https://apalache-mc.org/docs/apalache/running.html>
  - GitHub（リリース/配布物）：<https://github.com/apalache-mc/apalache/releases>

### SPIN（Promela）

- 用途：並行システムの明示的状態模型検査（Promela）と反例トレース。full-state search と bitstate hashing などの近似モードを区別する。
- 推奨読者：第6章（並行性の落とし穴）、第8章（模型検査）
- 一次情報：
  - 公式（spinroot）：<https://spinroot.com/spin/whatispin.html>
  - 固定版SPIN CLI man page（`-search`等のoption）：<https://github.com/nimble-code/Spin/blob/4883fbb1b1ef1f75fa9dda78efe1ad8910baf819/Man/spin.1>

### NuSMV / nuXmv

- 用途：NuSMV は古典的な記号的模型検査器、nuXmv はその後継・拡張系である。結果を引用するときは、ツール名に加えて、使用したエンジン、fairness constraints、timeout、`unknown`、抽象化を記録する。
- 推奨読者：第8章（模型検査の俯瞰）
- 一次情報：
  - 公式サイト：<https://nusmv.fbk.eu/>
  - nuXmv 公式サイト：<https://nuxmv.fbk.eu/>
  - nuXmv User Manual：<https://nuxmv.fbk.eu/downloads/nuxmv-user-manual.pdf>


### PRISM（確率的・定量的模型検査）

- 用途：DTMC、CTMC、MDPに対する確率的到達可能性、定常確率、閾値、reward / expected costの検査
- 推奨読者：第8章（確率的・定量的模型検査）、付録C（LTL / CTLとの概念対応）、付録B（nightly実行）
- 実行境界：本書のnightly契約はPRISM 4.10.1、公式Linux x86-64 archive、SHA-256、explicit engine、教育用DTMCを固定する。公式配布物はGPL-2.0であり、CI artifactやPagesへtool binaryを再配布しない。
- 一次情報：
  - 公式サイト：<https://www.prismmodelchecker.org/>
  - Download、現行version、GPL-2.0：<https://www.prismmodelchecker.org/download.php>
  - PRISM 4.10.1公式release：<https://github.com/prismmodelchecker/prism/releases/tag/v4.10.1>
  - 公式manual：<https://www.prismmodelchecker.org/manual/>
  - DTMC / CTMC / MDPのmodel type：<https://www.prismmodelchecker.org/manual/ThePRISMLanguage/ModelType>
  - Property languageの導入：<https://www.prismmodelchecker.org/manual/PropertySpecification/Introduction>
  - Propertyの構文と意味：<https://www.prismmodelchecker.org/manual/PropertySpecification/SyntaxAndSemantics>
  - Reward-based property：<https://www.prismmodelchecker.org/manual/PropertySpecification/Reward-basedProperties>
  - 通常のmodel checking：<https://www.prismmodelchecker.org/manual/RunningPRISM/ModelChecking>
  - Statistical model checking：<https://www.prismmodelchecker.org/manual/RunningPRISM/StatisticalModelChecking>
  - 公式case studies：<https://www.prismmodelchecker.org/casestudies/>

### SymbiYosys（open-source RTL formal verification）

- 用途：SystemVerilog RTLに対するBMC、k-inductionによるsafety proof、cover reachabilityとcycle trace生成
- 推奨読者：第8章（RTL形式検証）、付録B（nightly実行）、付録C（`assert` / `assume` / `cover`の概念対応）
- 実行境界：本書のnightly契約はOSS CAD Suite 20260716の公式Linux x64 assetとSHA-256、SBY `v0.67-4-gfea6e46`、Yosys `0.67+40`、Bitwuzla `0.9.1`、`smtbmc` engine、depth 6を固定する。CI artifactやPagesへsuite binaryを再配布しない。
- 保証境界：結果はYosysが受理したSystemVerilog formal subset、RTL、clock/reset/environment assumptions、property、mode、depth、backendに相対的である。CDC、timing、physical/analog behavior、synthesis後netlist、SystemVerilog Assertions全体を自動的には保証しない。
- 一次情報：
  - SymbiYosys公式repository：<https://github.com/YosysHQ/sby>
  - SymbiYosys公式documentation：<https://symbiyosys.readthedocs.io/en/latest/>
  - Quickstart：<https://symbiyosys.readthedocs.io/en/latest/quickstart.html>
  - Reference（mode / engine / task / artifact）：<https://symbiyosys.readthedocs.io/en/latest/reference.html>
  - Yosys公式repository：<https://github.com/YosysHQ/yosys>
  - OSS CAD Suite公式repository：<https://github.com/YosysHQ/oss-cad-suite-build>
  - OSS CAD Suite 2026-07-16公式release：<https://github.com/YosysHQ/oss-cad-suite-build/releases/tag/2026-07-16>
  - Bitwuzla公式repository：<https://github.com/bitwuzla/bitwuzla>

### Tamarin Prover（active adversary下のsymbolic protocol verification）

- 用途：Dolev–Yao攻撃者が通信を制御する下で、秘密性、認証、replay等をtrace lemmaとして検証し、不成立時にattack traceを得る。
- 推奨読者：第13章（通信・暗号プロトコル）、付録B（nightly実行）、付録C（fact / rule / event / lemma対応）
- 実行境界：本書のnightly契約はTamarin Prover 1.12.0と対応Maude 3.5.1の公式Linux x86-64配布物、commit、SHA-256、150秒の内側timeout、180秒のrunner timeout、自動proof modeを固定する。配布binaryはCI artifactやPagesへ再配布しない。
- 保証境界：結果は選択したsymbolic model、equational theory、仮定、lemmaに相対的であり、computational soundness、実装、暗号強度、鍵侵害、side-channelを無条件に保証しない。
- 一次情報：
  - 公式manual（Introduction）：<https://tamarin-prover.com/manual/master/book/001_introduction.html>
  - 公式manual（First Example / authentication）：<https://tamarin-prover.com/manual/master/book/003_example.html>
  - 公式manual（Rules）：<https://tamarin-prover.com/manual/master/book/005_protocol-specification-rules.html>
  - 公式manual（Property Specification）：<https://tamarin-prover.com/manual/master/book/007_property-specification.html>
  - 公式repository：<https://github.com/tamarin-prover/tamarin-prover>
  - 公式examples：<https://github.com/tamarin-prover/tamarin-prover/tree/develop/examples>
  - Tamarin Prover 1.12.0公式release：<https://github.com/tamarin-prover/tamarin-prover/releases/tag/1.12.0>
  - Maude公式配布案内：<https://maude.cs.illinois.edu/get-maude>
  - Maude 3.5.1公式release：<https://github.com/maude-lang/Maude/releases/tag/Maude3.5.1>

### Runtime verification（RTLola / MonPoly / RV-Monitor）

2026-07-16に公式repository、配布ページ、documentationを再確認した比較です。
同じruntime verificationでも、stream specification、metric temporal logic、Java instrumentationでは導入境界が異なります。

| 候補 | 主な適用形態 | 公式配布・保守の観測事実 | 本書での判断 |
| --- | --- | --- | --- |
| RTLola | typed input/output streamとtriggerをonlineまたはoffline eventへ適用 | `rtlola-cli 0.1.2`のcrates.io package、offline CSV、JSON出力、2025年のupstream更新を確認 | **採用**。immutable package digest、埋め込みcommitと`Cargo.lock`、固定Rust、構造化verdictを一つのnightly契約にできる |
| MonPoly | timestamp付きlogをmetric first-order temporal logicへ照合 | SourceForgeの最新配布として1.1.10（2020-11-25）を確認 | 今回は不採用。offline log監視への適合性は高いが、本書のJSON verdict、provenance、現行CI保守契約を追加で設計する必要がある |
| RV-Monitor | specificationからJava monitorを生成し、applicationへinstrumentationする | 公式GitHubにreleaseがなく、確認できる最新commitは2020-12-18、MIT license | 今回は不採用。Java code generation / instrumentationは、固定CSVを再生する最小教材よりbuild・結合範囲が広い |

RTLolaを選んだ理由は機能数の一般比較ではなく、**このrepositoryの固定offline traceと構造化artifact契約に最も小さく接続できた**ためです。
MonPolyやRV-Monitorが劣っているという結論ではなく、対象property、言語、instrumentation方式、運用platformが変われば選択も変わります。

- 実行境界：本書はRTLola CLI 0.1.2、commit `11b6bb080a5fa487645fb023fb3d0baea6874e73`、Rust 1.87.0、相対時刻CSV、JSONの違反出力を固定する。
- 保証境界：正常・違反の二つの架空3-event traceだけを検査し、event収集の完全性、未観測run、online運用、全RTLola機能を保証しない。
- 一次情報：
  - RTLola Interpreter公式repository：<https://github.com/reactive-systems/RTLola-Interpreter>
  - RTLola CLI 0.1.2 documentation：<https://docs.rs/rtlola-cli/0.1.2/rtlola_cli/>
  - RTLola言語・CLI source commit：<https://github.com/reactive-systems/RTLola-Interpreter/commit/11b6bb080a5fa487645fb023fb3d0baea6874e73>
  - MonPoly公式project page：<https://infsec.ethz.ch/research/software/monpoly.html>
  - MonPoly公式配布：<https://sourceforge.net/projects/monpoly/>
  - MonPoly公式source repository：<https://bitbucket.org/monpoly/monpoly/src/master/>
  - RV-Monitor公式repository：<https://github.com/runtimeverification/rv-monitor>

## 3) 定理証明（Rocq / Lean / Isabelle / Agda）

### Rocq（旧称：Coq）

- 用途：証明支援（型理論/カーネルによるチェック）と、証明とプログラムの統合的開発
- 推奨読者：第9章（定理証明の基礎）
- 一次情報：
  - 公式サイト：<https://rocq-prover.org/>
  - changelog：<https://rocq-prover.org/changelog>
  - リリース（例：9.0.0）：<https://rocq-prover.org/releases/9.0.0>
  - Proof mode（`Qed` と `Admitted`）：<https://rocq-prover.org/doc/v9.0/refman/proofs/writing-proofs/proof-mode.html>
  - Core language と kernel：<https://rocq-prover.org/doc/V9.2.0/refman/language/core/index.html>
  - Assumptions（axiom / hypothesis / variable）：<https://rocq-prover.org/doc/master/refman/language/core/assumptions.html>

### Lean（Lean 4）

- 用途：定理証明支援、数学ライブラリ活用、証明の自動化（tactic）
- 推奨読者：第9章（定理証明の基礎）
- 一次情報：
  - 公式サイト：<https://lean-lang.org/>
  - Mathlib use case：<https://lean-lang.org/use-cases/mathlib>
  - GitHub（Lean 4）：<https://github.com/leanprover/lean4>
  - mathlib4：<https://github.com/leanprover-community/mathlib4>
  - Lean Reference: Axioms（`sorryAx` を含む公理境界）：<https://lean-lang.org/doc/reference/latest/Axioms/>
  - Lean Tactic Reference（`admit` / `sorry`、`native_decide` の信頼境界）：<https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/>

### 論理の健全性・完全性と意味論

- 用途：第9章の健全性・完全性を、対象論理、演繹系、意味論に相対的な性質として読む。
- 注意：古典一階述語論理の標準意味論に対する完全性を、標準意味論の二階論理、高階論理、依存型理論へ無条件に一般化しない。
- 理論背景：
  - Stanford Encyclopedia of Philosophy, “Logical Consequence”：<https://plato.stanford.edu/entries/logical-consequence/>
  - Stanford Encyclopedia of Philosophy, “Kurt Gödel”（一階述語論理の完全性定理）：<https://plato.stanford.edu/entries/goedel/>
  - Stanford Encyclopedia of Philosophy, “Second-order and Higher-order Logic”：<https://plato.stanford.edu/entries/logic-higher-order/>

### Isabelle

- 用途：定理証明支援（Isabelle/HOL 等）、証明文書化、ツール統合
- 推奨読者：第9章（定理証明の基礎）
- 一次情報：
  - GitHub（ミラー）：<https://github.com/isabelle-prover/mirror-isabelle>

### Agda

- 用途：依存型に基づく定理証明・プログラム記述
- 推奨読者：第9章（型理論の補助線として）
- 一次情報：
  - ドキュメント：<https://agda.readthedocs.io/en/latest/>

## 4) プログラム検証（Dafny / Frama-C / CBMC / VeriFast / SPARK / Rust検証ツール）

### Dafny

- 用途：仕様（契約）と検証を統合し、SMT と組み合わせて自動検証を行う
- 推奨読者：第10章（プログラム検証）、第12章（自動化）
- 一次情報：
  - 公式サイト：<https://dafny.org/>
  - GitHub：<https://github.com/dafny-lang/dafny>

### Frama-C

- 用途：C言語向けの静的解析/検証（アノテーション、プラグイン）
- 推奨読者：第10章（プログラム検証）
- 一次情報：
  - GitHub（配布/スナップショット）：<https://github.com/Frama-C/Frama-C-snapshot>

### CBMC

- 用途：C/C++の境界付き模型検査（バグ/安全性/アサーション）
- 推奨読者：第8章（模型検査の考え方）、第10章（プログラム検証）
- 一次情報：
  - 公式サイト：<https://www.cprover.org/cbmc/>
  - CBMC Background Concepts（bounded symbolic checking の保証範囲）：<https://diffblue.github.io/cbmc/background-concepts.html>

### VeriFast

- 用途：分離論理に基づく検証（C/Java等）
- 推奨読者：第10章（プログラム検証）
- 一次情報：
  - GitHub：<https://github.com/verifast/verifast>

### SPARK（Ada）

- 用途：高信頼Ada開発向けの契約/静的解析/証明（安全クリティカル）
- 推奨読者：第11章（導入戦略）、第12章（ツール統合）
- 一次情報：
  - 公式サイト：<https://www.adacore.com/sparkpro>

### Kani Rust Verifier

- 用途：Rustコードの模型検査、proof harness、assertion、panic、overflow、`unsafe` 周辺の検査
- 推奨読者：第8章（模型検査）、第10章（プログラム検証）、第12章（CI）
- 一次情報：
  - 公式ドキュメント：<https://model-checking.github.io/kani/>
  - GitHub：<https://github.com/model-checking/kani>

### Verus

- 用途：Rust風の仕様・証明記法と SMT により、低レベルシステムコードの機能的正しさを検証する
- 推奨読者：第9章（型と証明）、第10章（プログラム検証）
- 一次情報：
  - Verus Tutorial and Reference：<https://verus-lang.github.io/verus/guide/>
  - GitHub：<https://github.com/verus-lang/verus>

### Creusot

- 用途：RustコードをWhy3系の検証条件へ接続し、panic、overflow、未定義動作、仕様適合性を演繹検証する
- 推奨読者：第10章（プログラム検証）、第12章（証明義務管理）
- 一次情報：
  - 公式サイト：<https://creusot.rs/>
  - GitHub：<https://github.com/creusot-rs/creusot>

### Prusti

- 用途：Viper検証基盤に基づくRust向け契約検証、panic/overflow/事前条件/事後条件/ループ不変条件の検査
- 推奨読者：第10章（プログラム検証）
- 一次情報：
  - User guide：<https://viperproject.github.io/prusti-dev/user-guide/>
  - GitHub：<https://github.com/viperproject/prusti-dev>

### Aeneas

- 用途：RustプログラムをCharon/LLBC経由で F*、Rocq/Coq、HOL4、Lean などの証明支援系へ接続する
- 推奨読者：第9章（証明支援系）、第10章（プログラム検証）
- 一次情報：
  - 公式サイト：<https://aeneasverif.github.io/>
  - GitHub：<https://github.com/AeneasVerif/aeneas>

## 5) SMT 標準とソルバー（SMT-LIB / Z3 / cvc5）

### SMT-LIB

- 用途：SMT ソルバーへ論理式、理論、ベンチマーク、検査対象を渡す標準形式
- 推奨読者：第10章（プログラム検証）、第12章（ツールと自動化）
- 注意：SMT-LIB v3 は予備提案であり、現行の SMT-LIB 2.7 や各ツールの実務運用を直ちに置き換えるものではない
- 一次情報：
  - SMT-LIB Standard Language（Version 2.7）：<https://smt-lib.org/language.shtml>
  - SMT-LIB Version 3.0 - Preliminary Proposal：<https://smt-lib.org/version3.shtml>

### Z3

- 用途：制約充足/定理証明の基盤（多くの検証器のバックエンド）
- 推奨読者：第10章（プログラム検証）、第12章（ツールと自動化）
- 一次情報：
  - Z3 Guide：<https://microsoft.github.io/z3guide/>
  - Programming Z3：<https://theory.stanford.edu/~nikolaj/programmingz3.html>
  - GitHub：<https://github.com/Z3Prover/z3>
  - GitHub（リリース）：<https://github.com/Z3Prover/z3/releases>

### cvc5（CVC系列の後継。旧：CVC4）

- 用途：SMT ソルバーおよび SyGuS エンジン（検証器バックエンドとして利用されることが多い）
- 推奨読者：第10章（プログラム検証）、第12章（ツールと自動化）
- 一次情報：
  - 公式サイト：<https://cvc5.github.io/>
  - 公式ドキュメント：<https://cvc5.github.io/docs/>
  - GitHub：<https://github.com/cvc5/cvc5>
  - GitHub（リリース）：<https://github.com/cvc5/cvc5/releases>
  - Python bindings（必要時）：<https://pypi.org/project/cvc5/>

### SMT 証明証跡の独立再検査（Alethe / LFSC / DRAT / LRAT）

- 実行境界（本書の pinned contract）：
  - `cvc5 1.3.4` release tag は `cvc5-1.3.4`、release commit は `f3b21c4483d3b88dc63cb7cd3e5eb092eee5e341`、対象 asset は `cvc5-Linux-x86_64-static.zip`、SHA-256 は `dcdbfada0ce493ee98259c0816e0daafc561c223aadb3af298c2968e73ea39c6`
  - `Carcara 1.1.0` 自体の release は参照用だが、cvc5 1.3.4 の `contrib/get-carcara-checker` が固定している互換 commit は `394edbb15ba95c47893f1d821fddde7e016af178`
  - 上記 commit の source archive SHA-256 は `28562432ca7413a662d25f03e328cab4b7b9bf649b2ca69268a255a44a5ddee6`
  - Carcara の build 境界は固定した Rust/Cargo `1.87.0`
- cvc5 1.3.4 の Alethe 文書は、equality with uninterpreted functions、linear arithmetic、bit-vectors、parts of strings を、quantifier の有無を含めて現在の対象として挙げる。これは「普遍互換」を意味せず、solver / checker / logic fragment の組合せごとに確認が必要
- cvc5 1.3.4 の release note は、Alethe について「AUFNIRA に対する CPC fragment の full translation 改善」を述べており、逆に言えば full coverage を一般化してよい根拠にはならない
- cvc5 の LFSC 文書は、supported theories 全体に basic support を述べる一方、未対応の internal proof rule は trust step として出力され得る。strict checker 連携では trust step を成功扱いにしない
- DRAT / LRAT は propositional CNF proof ecosystem であり、CNF 化後の `unsat` 証明を扱う。元の SMT 問題、自然言語仕様、エンコーダ、未モデル化仮定の正しさを直接証明するものではない
- 一次情報：
  - cvc5 Proof Production：<https://cvc5.github.io/docs/cvc5-1.3.4/proofs/proofs.html>
  - cvc5 Alethe 出力：<https://cvc5.github.io/docs/cvc5-1.3.4/proofs/output_alethe.html>
  - cvc5 LFSC 出力：<https://cvc5.github.io/docs/cvc5-1.3.4/proofs/output_lfsc.html>
  - cvc5 `get-carcara-checker`（固定 release 版）：<https://github.com/cvc5/cvc5/blob/cvc5-1.3.4/contrib/get-carcara-checker>
  - Carcara：<https://github.com/ufmg-smite/carcara>
  - DRAT-trim：<https://github.com/marijnheule/drat-trim>

## 6) 分散システム理論（CAP / FLP と仮定変更）

- 読み方：不可能性定理は結論だけでなく、計算モデル、通信仮定、故障モデル、保証対象の組として読む。
- 一次情報：
  - Gilbert and Lynch, CAP theorem：<https://www.cs.princeton.edu/courses/archive/spr22/cos418/papers/cap.pdf>
  - Fischer, Lynch, and Paterson, FLP：<https://groups.csail.mit.edu/tds/papers/Lynch/jacm85.pdf>
  - Dwork, Lynch, and Stockmeyer, partial synchrony：<https://groups.csail.mit.edu/tds/papers/Lynch/jacm88.pdf>
  - Chandra and Toueg, unreliable failure detectors：<https://www.cs.utexas.edu/~lorenzo/corsi/cs380d/papers/p225-chandra.pdf>
  - Ben-Or, randomized asynchronous agreement（DOI: `10.1145/800221.806707`）：<https://cris.huji.ac.il/en/publications/another-advantage-of-free-choice-completely-asynchronous-agreemen/>

## 7) 産業事例（一次・準一次情報）

### パリ地下鉄14号線（B-method）

- 推奨読者：第13章（事例研究）
- 一次・準一次情報：
  - Clearsy（Line 14 / B-method）：<https://www.clearsy.com/en/the-tools/extension-of-line-14-of-the-paris-metro-over-25-years-of-reliability-thanks-to-the-b-formal-method/>
  - Butler ほか（FMICS 2020、Springer chapter）：<https://link.springer.com/chapter/10.1007/978-3-030-58298-2_8>

### Amazon s2n（暗号実装の検証）

- 推奨読者：第13章（事例研究）
- 一次・準一次情報：
  - AWS Security Blog：<https://aws.amazon.com/blogs/security/automated-reasoning-and-amazon-s2n/>
  - Galois（SAWでの検証例）：<https://www.galois.com/articles/verifying-s2n-hmac-with-saw>
  - CAV 2018（s2n/SAWの報告、Springer chapter）：<https://doi.org/10.1007/978-3-319-96142-2_26>
  - s2n-tls（GitHub）：<https://github.com/aws/s2n-tls>

### 産業界における TLA+ 活用

- 推奨読者：第7章（TLA+）、第13章（事例研究）
- 一次・準一次情報：
  - Lamport（Industrial use of TLA+）：<https://lamport.azurewebsites.net/tla/industrial-use.html>
  - Microsoft Learn（Cosmos DB の分散実装と整合性、TLA+ 仕様への導線）：<https://learn.microsoft.com/en-us/azure/cosmos-db/global-dist-under-the-hood>
  - Azure Cosmos DB（TLA+ 高レベル仕様）：<https://github.com/Azure/azure-cosmos-tla>
  - Microsoft Research（Cosmos DB の整合性保証に関する TLA+ 仕様、動画）：<https://www.microsoft.com/en-us/research/video/tla-specifications-of-the-consistency-guarantees-provided-by-cosmos-db/>
  - Hackett（ICSE SEIP 2023、PDF）：<https://fhackett.com/files/icse-seip-23-inconsistency.pdf>

### Cedar / AWS（認可ポリシー検証）

- 推奨読者：第13章（事例研究）、第11章（導入戦略）、第12章（ツール連携）
- 一次・準一次情報：
  - Cedar open source announcement：<https://aws.amazon.com/about-aws/whats-new/2023/05/cedar-open-source-language-access-control/>
  - Amazon Verified Permissions：<https://aws.amazon.com/verified-permissions/>
  - Cedar Analysis announcement：<https://aws.amazon.com/blogs/opensource/introducing-cedar-analysis-open-source-tools-for-verifying-authorization-policies/>
  - How we built Cedar（Amazon Science）：<https://www.amazon.science/blog/how-we-built-cedar-with-automated-reasoning-and-differential-testing>
  - Lean use case: Cedar：<https://lean-lang.org/use-cases/cedar/>
  - Cedar Policy：<https://www.cedarpolicy.com/>
  - Cedar GitHub organization：<https://github.com/cedar-policy>

### Amazon Bedrock Guardrails Automated Reasoning checks

- 推奨読者：第13章（事例研究）、付録F（AI 支援運用）
- 注意：LLM そのものの正しさ証明ではなく、LLM 出力を形式化されたポリシー/ドメイン知識に照らして検査する事例として扱う。対応リージョン、対応言語、API、制限事項は変わるため公式ドキュメントを確認する。
- 一次情報：
  - GA announcement：<https://aws.amazon.com/about-aws/whats-new/2025/08/automated-reasoning-checks-amazon-bedrock-guardrails/>
  - User Guide：<https://docs.aws.amazon.com/bedrock/latest/userguide/guardrails-automated-reasoning-checks.html>
  - Guardrails overview：<https://docs.aws.amazon.com/bedrock/latest/userguide/guardrails.html>

### スマートコントラクト検証（Ethereum / Move / Certora）

- 推奨読者：第10章（プログラム検証）、第12章（自動化）、第13章（事例研究）
- 注意：仕様が誤っていれば、検証は誤った仕様への適合性を示すだけである。探索境界、ソルバーの `unknown`、タイムアウト、未モデル化の環境、外部オラクル、アップグレード権限を証跡に残す。
- 一次情報：
  - Ethereum formal verification：<https://ethereum.org/developers/docs/smart-contracts/formal-verification/>
  - Solidity SMTChecker：<https://docs.soliditylang.org/en/latest/smtchecker.html>
  - Aptos Move Prover：<https://aptos.dev/build/smart-contracts/prover>
  - Certora Prover open source announcement：<https://www.certora.com/blog/certora-goes-open-source>
  - Certora Prover GitHub：<https://github.com/Certora/CertoraProver>
  - Certora User Guide：<https://docs.certora.com/en/latest/docs/user-guide/index.html>
  - Certora Verification Language：<https://docs.certora.com/en/latest/docs/cvl/index.html>

## 8) AI×形式手法（LLM 支援：位置づけと注意点）

LLM は、仕様/証明/反例解釈の「草案生成」や「探索支援」に有用である一方、**最終保証の根拠にはならない**。
本書では、LLM 出力を「未信頼入力」として扱い、必ず機械検証（模型検査/型チェック/SMT 等）で閉じる運用を推奨する。

- 代表的実装・評価基盤：
  - LeanDojo-v2：<https://leandojo.org/leandojo.html>
  - LeanDojo docs：<https://leandojo.readthedocs.io/>
  - Lean Copilot：<https://github.com/lean-dojo/LeanCopilot>
  - Amazon Bedrock Guardrails Automated Reasoning checks：<https://docs.aws.amazon.com/bedrock/latest/userguide/guardrails-automated-reasoning-checks.html>
  - AlphaProof / AlphaGeometry 2 announcement：<https://deepmind.google/blog/ai-solves-imo-problems-at-silver-medal-level/>
  - AlphaProof Nature paper：<https://www.nature.com/articles/s41586-025-09833-y>
  - DeepSeek-Prover-V2（arXiv）：<https://arxiv.org/abs/2504.21801>
  - ProofGym（NeurIPS 2025）：<https://neurips.cc/virtual/2025/131121>
  - APOLLO（arXiv）：<https://arxiv.org/html/2505.05758v5>
  - 自然言語→形式言語（例：EMNLP 2025、PDF）：<https://aclanthology.org/2025.emnlp-main.1586v2.pdf>

<!-- markdown-link-check-disable-next-line -->
- 参考（準一次情報）：How Amazon Web Services Uses Formal Methods (CACM) <https://cacm.acm.org/research/how-amazon-web-services-uses-formal-methods/>
