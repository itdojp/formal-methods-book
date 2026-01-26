# 付録E：参考文献とWebリソース（一次情報への導線）

本付録は、本文で扱った形式的手法・ツールについて、**一次情報（公式サイト/公式リポジトリ/公式ドキュメント/公式リリース）**へ到達するための索引である。  
2026-01 時点で、名称変更・主流ツールの更新（例：Coq→Rocq、CVC4→cvc5、Alloy 6 系、TLA+の Apalache 等）を反映している。

## 数値の出典ポリシー（本書共通）

- **報告値（実測/事例）**：一次・準一次情報（論文/公式ブログ/公式レポート等）への出典URLを必須とする。
- **例示（仮）**：例示であることを明記し、読者が「一般に成立する値」と誤認しない表現にする。
- **不確実な推定**：推定値は避け、必要なら「不確実である」旨と前提条件（スコープ、計測条件）を併記する。

## 1) 仕様記述（Alloy / TLA+ / Z / CSP）

### Alloy（Alloy 6.x）

- 用途：関係モデルの記述と、有限スコープでの反例探索（モデル発見）
- 推奨読者：第4章（Alloy）、第8章（模型検査の考え方）
- 一次情報：
  - 公式サイト：<https://alloytools.org/>
  - リリース（Alloy 6.x）：<https://github.com/AlloyTools/org.alloytools.alloy/releases>

### TLA+（TLC）

- 用途：分散システム/並行システムの状態遷移仕様と、探索による検証（TLC）
- 推奨読者：第7章（TLA+）、第8章（模型検査）
- 一次情報：
  - TLA+公式（Lamportサイト）：<https://lamport.azurewebsites.net/tla/tla.html>
  - tlaplus/tlaplus リリース（tla2tools.jar）：<https://github.com/tlaplus/tlaplus/releases>

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
  - FDR（CSPモデル検査ツール情報）：<https://www.cs.ox.ac.uk/projects/fdr/>

## 2) 模型検査（TLC / Apalache / SPIN / NuSMV）

### Apalache（TLA+の追加検査：SMTベース）

- 用途：TLA+仕様に対して、SMTベースの探索/制約解決で性質検査を行う（TLCと棲み分け）
- 推奨読者：第7章（TLA+）、第8章（模型検査）、第12章（ツールと自動化）
- 一次情報：
  - 公式サイト：<https://apalache-mc.org/>
  - GitHub（リリース/配布物）：<https://github.com/apalache-mc/apalache/releases>

### SPIN（Promela）

- 用途：並行システムのモデル検査（Promela）と反例トレース
- 推奨読者：第6章（並行性の落とし穴）、第8章（模型検査）
- 一次情報：
  - 公式（spinroot）：<https://spinroot.com/spin/whatispin.html>

### NuSMV

- 用途：状態遷移モデルに対するモデル検査（CTL/LTL等）
- 推奨読者：第8章（模型検査の俯瞰）
- 一次情報：
  - 公式サイト：<https://nusmv.fbk.eu/>

## 3) 定理証明（Rocq / Lean / Isabelle / Agda）

### Rocq（旧称：Coq）

- 用途：証明支援（型理論/カーネルによるチェック）と、証明とプログラムの統合的開発
- 推奨読者：第9章（定理証明の基礎）
- 一次情報：
  - 公式サイト：<https://rocq-prover.org/>
  - リリース（例：9.0.0）：<https://rocq-prover.org/releases/9.0.0>

### Lean（Lean 4）

- 用途：定理証明支援、数学ライブラリ活用、証明の自動化（tactic）
- 推奨読者：第9章（定理証明の基礎）
- 一次情報：
  - 公式サイト：<https://lean-lang.org/>
  - GitHub（Lean 4）：<https://github.com/leanprover/lean4>

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

## 4) プログラム検証（Dafny / Frama-C / CBMC / VeriFast / SPARK）

### Dafny

- 用途：仕様（契約）と検証を統合し、SMTと組み合わせて自動検証を行う
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

- 用途：C/C++の境界付きモデル検査（バグ/安全性/アサーション）
- 推奨読者：第8章（模型検査の考え方）、第10章（プログラム検証）
- 一次情報：
  - 公式サイト：<https://www.cprover.org/cbmc/>

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

## 5) SMTソルバー（Z3 / cvc5）

### Z3

- 用途：制約充足/定理証明の基盤（多くの検証器のバックエンド）
- 推奨読者：第10章（プログラム検証）、第12章（ツールと自動化）
- 一次情報：
  - GitHub（リリース）：<https://github.com/Z3Prover/z3/releases>

### cvc5（CVC系列の後継。旧：CVC4）

- 用途：SMTソルバー（検証器バックエンドとして利用されることが多い）
- 推奨読者：第10章（プログラム検証）、第12章（ツールと自動化）
- 一次情報：
  - GitHub：<https://github.com/cvc5/cvc5>
  - GitHub（リリース）：<https://github.com/cvc5/cvc5/releases>
  - Python bindings（必要時）：<https://pypi.org/project/cvc5/>

## 6) 産業事例（一次・準一次情報）

### パリ地下鉄14号線（B-method）

- 推奨読者：第13章（事例研究）
- 一次・準一次情報：
  - Clearsy（Line 14 / B-method）：<https://www.clearsy.com/en/the-tools/extension-of-line-14-of-the-paris-metro-over-25-years-of-reliability-thanks-to-the-b-formal-method/>
  - Butler ほか（FMICS 2020、DOI）：<https://doi.org/10.1007/978-3-030-58298-2_8>

### Amazon s2n（暗号実装の検証）

- 推奨読者：第13章（事例研究）
- 一次・準一次情報：
  - AWS Security Blog：<https://aws.amazon.com/blogs/security/automated-reasoning-and-amazon-s2n/>
  - Galois（SAWでの検証例）：<https://www.galois.com/articles/verifying-s2n-hmac-with-saw>
  - CAV 2018（s2n/SAWの報告、PDF）：<http://www0.cs.ucl.ac.uk/staff/b.cook/CAV18_s2n.pdf>
  - s2n-tls（GitHub）：<https://github.com/aws/s2n-tls>

### 産業界におけるTLA+活用

- 推奨読者：第7章（TLA+）、第13章（事例研究）
- 一次・準一次情報：
  - Lamport（Industrial use of TLA+）：<https://lamport.azurewebsites.net/tla/industrial-use.html>
  - Microsoft Learn（Cosmos DBの分散実装と整合性、TLA+仕様への導線）：<https://learn.microsoft.com/en-us/azure/cosmos-db/global-dist-under-the-hood>
  - Azure Cosmos DB（TLA+高レベル仕様）：<https://github.com/Azure/azure-cosmos-tla>
  - Microsoft Research（Cosmos DBの整合性保証に関するTLA+仕様、動画）：<https://www.microsoft.com/en-us/research/video/tla-specifications-of-the-consistency-guarantees-provided-by-cosmos-db/>
  - Hackett（ICSE SEIP 2023、PDF）：<https://fhackett.com/files/icse-seip-23-inconsistency.pdf>

## 7) AI×形式手法（LLM支援：位置づけと注意点）

LLMは、仕様/証明/反例解釈の「草案生成」や「探索支援」に有用である一方、**最終保証の根拠にはならない**。  
本書では、LLM出力を「未信頼入力」として扱い、必ず機械検証（模型検査/型チェック/SMT等）で閉じる運用を推奨する。

- 代表的実装・評価基盤：
  - Lean Copilot：<https://github.com/lean-dojo/LeanCopilot>
  - ProofGym（NeurIPS 2025）：<https://neurips.cc/virtual/2025/131121>
  - APOLLO（arXiv）：<https://arxiv.org/html/2505.05758v5>
  - 自然言語→形式言語（例：EMNLP 2025、PDF）：<https://aclanthology.org/2025.emnlp-main.1586v2.pdf>

<!-- markdown-link-check-disable-next-line -->
- 参考（準一次情報）：How Amazon Web Services Uses Formal Methods (CACM) <https://cacm.acm.org/research/how-amazon-web-services-uses-formal-methods/>
