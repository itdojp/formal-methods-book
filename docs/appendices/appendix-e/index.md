---
layout: book
title: "付録E：参考文献とWebリソース（一次情報への導線）"
locale: "ja"
lang: "ja"
source_path: "src/ja/appendices/appendix-e.md"
---
# 付録E：参考文献とWebリソース（一次情報への導線）

本付録は、本文で扱った形式的手法・ツールについて、**一次情報（公式サイト/公式リポジトリ/公式ドキュメント/公式リリース）**へ到達するための索引である。
2026-06 時点で、名称変更・主流ツールの更新（例：Coq→Rocq、CVC4→cvc5、Alloy 6 系、TLA+ の Apalache / Quint 等）を反映している。

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
  - Community Z Tools (CZT)：<https://czt.sourceforge.net/>
  - SourceForge（CZTプロジェクト）：<https://sourceforge.net/projects/czt/>

### CSP

- 用途：並行プロセスの通信・同期・デッドロック等の性質を扱う
- 推奨読者：第6章（CSP）
- 一次情報（ツール例）：
  - FDR（CSP模型検査ツール情報）：<https://www.cs.ox.ac.uk/projects/fdr/>

## 2) 模型検査（TLC / Apalache / SPIN / NuSMV）

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
  - SPIN Quick Reference（探索方式、weak fairness、bitstate hashing）：<https://spinroot.com/spin/Man/Quick.html>

### NuSMV / nuXmv

- 用途：NuSMV は古典的な記号的模型検査器、nuXmv はその後継・拡張系である。結果を引用するときは、ツール名に加えて、使用したエンジン、fairness constraints、timeout、`unknown`、抽象化を記録する。
- 推奨読者：第8章（模型検査の俯瞰）
- 一次情報：
  - 公式サイト：<https://nusmv.fbk.eu/>
  - nuXmv 公式サイト：<https://nuxmv.fbk.eu/>
  - nuXmv User Manual：<https://nuxmv.fbk.eu/downloads/nuxmv-user-manual.pdf>

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
