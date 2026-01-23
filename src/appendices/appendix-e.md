# 付録E：参考文献とWebリソース

本付録は、公式ドキュメントを優先しつつ、学習段階や目的に応じた参照先を整理したものです。各セクションに本書の関連章を記載しています。

## E.1 教科書・参考書

関連章: 第1〜3章（全体像・基礎整理）

### 入門レベル

**日本語文献**
1. 荒木啓二郎『形式仕様記述技法Z』（共立出版、1996）
   - Z記法の標準的教科書。基礎から応用まで段階的に学習可能。

2. 青木利晃『ソフトウェア検証』（共立出版、2014）
   - 模型検査と定理証明の基礎を日本語で整理。

**英語文献**
3. Jackson, Daniel. *Software Abstractions: Logic, Language, and Analysis*. MIT Press, 2012.
   - Alloyの作者による軽量形式手法の決定版。

4. Wing, Jeannette M. *A Specifier's Introduction to Formal Methods*. Computer, 1990.
   - 形式的手法の全体像と適用観点を俯瞰。

### 中級レベル

5. Lamport, Leslie. *Specifying Systems*. Addison-Wesley, 2002.
   - TLA+の包括的解説。分散システムの仕様と検証を学べる。

6. Roscoe, A.W. *Understanding Concurrent Systems*. Springer, 2010.
   - CSPの理論と実践。並行システムの検証に有用。

7. Hoare, C.A.R. and He, Jifeng. *Unifying Theories of Programming*. Prentice Hall, 1998.
   - プログラミング理論の統一的視点を提供。

### 上級レベル

8. Pierce, Benjamin C. *Types and Programming Languages*. MIT Press, 2002.
   - 型理論の基盤理解に必須。

9. Nipkow, Tobias, et al. *Isabelle/HOL: A Proof Assistant for Higher-Order Logic*. Springer, 2002.
   - 高階論理の証明支援系の実践。

## E.2 分野別専門書

関連章: 第11〜12章（産業適用・運用設計）

### 安全クリティカルシステム

10. Storey, Neil. *Safety Critical Computer Systems*. Addison-Wesley, 1996.
    - 安全性分析と標準対応の基礎。

11. Knight, John C. *Fundamentals of Dependable Computing for Software Engineers*. CRC Press, 2012.
    - 形式手法の産業適用と信頼性評価。

### セキュリティ

12. Anderson, Ross. *Security Engineering*. Wiley, 2020.
    - セキュリティ設計の体系とプロトコル分析。

13. Meadows, Catherine. *Formal Methods for Cryptographic Protocol Analysis*. Journal of Computer Security, 2003.
    - 暗号プロトコル検証の基礎。

### ソフトウェア工学との統合

14. Ghezzi, Carlo, et al. *Fundamentals of Software Engineering*. Prentice Hall, 2002.
    - 開発プロセスと形式手法の接続に有用。

## E.3 重要な論文

関連章: 第8〜10章（模型検査・定理証明・プログラム検証）

### 基礎理論

15. Floyd, R.W. "Assigning Meanings to Programs." *Proceedings of Symposia in Applied Mathematics*, 1967.
    - プログラム検証の理論的出発点。

16. Dijkstra, E.W. "Guarded Commands, Nondeterminacy and Formal Derivation of Programs." *CACM*, 1975.
    - 最弱事前条件と導出の基礎。

17. Milner, Robin. "A Calculus of Communicating Systems." *Springer*, 1980.
    - プロセス代数の基礎。

### 実用化研究

18. Abrial, J.-R. "Formal Methods in Industry: Achievements, Problems, Future." *ICSE*, 2006.
    - 産業適用の成功/失敗要因を整理。

19. Newcombe, Chris, et al. "How Amazon Web Services Uses Formal Methods." *CACM*, 2015.
    - 大規模システムでのTLA+活用事例。

20. Klein, Gerwin, et al. "seL4: Formal Verification of an OS Kernel." *SOSP*, 2009.
    - OSカーネルの完全検証の代表例。

## E.4 Webリソース

関連章: 第4〜9章（各手法の実装・検証）

### 公式サイト・ドキュメント

**Alloy**
- 公式サイト: https://alloytools.org/ （配布・概要・最新情報）
- チュートリアル: https://alloytools.org/tutorials/ （基礎チュートリアル）
- コミュニティフォーラム: https://groups.google.com/g/alloytools （Q&Aと議論）

**TLA+**
- 公式サイト: https://lamport.azurewebsites.net/tla/ （公式ドキュメントとダウンロード）
- Learn TLA+: https://learntla.com/ （学習ロードマップ）
- TLA+例題集: https://github.com/tlaplus/Examples （公式サンプル）

**SPIN**
- 公式サイト: https://spinroot.com/ （配布・更新情報）
- Promela言語リファレンス: https://spinroot.com/spin/Man/promela.html （言語仕様）
- SPINワークショップ: https://spinroot.com/spin/Workshops/ （研究/実践コミュニティ）

**Coq**
- 公式サイト: https://coq.inria.fr/ （配布・公式ドキュメント）
- Software Foundations: https://softwarefoundations.cis.upenn.edu/ （公式教材）
- Coq'Art: https://www.labri.fr/perso/casteran/CoqArt/ （参考書）

### AI支援開発と形式手法

関連章: 第11〜12章（運用・ガードレール設計）

- Coding Agent（Copilot）概要: https://docs.github.com/en/copilot/concepts/agents/coding-agent/about-coding-agent （エージェントの概念と運用前提）
- Code Review（Copilot）概念: https://docs.github.com/en/copilot/concepts/agents/code-review （レビュー自動化の位置づけ）
- リポジトリ指示ファイル: https://docs.github.com/en/copilot/how-tos/configure-custom-instructions/add-repository-instructions （検証ルールの強制に活用）
- GitHub公式ブログ: https://github.blog/news-insights/company-news/welcome-home-agents/ （エージェント運用の背景）

### オンライン学習リソース

- Logic and Proof: https://leanprover.github.io/logic_and_proof/ （論理と証明の基礎学習）
- Natural Number Game: https://www.ma.imperial.ac.uk/~buzzard/xena/natural_number_game/ （対話型証明入門）

## E.5 ツールとソフトウェア

関連章: 第4〜10章、付録B

### 無料・オープンソースツール

**仕様記述・検証**
- Alloy Analyzer: https://alloytools.org/download.html （軽量モデル検査）
- TLA+ Toolbox: https://github.com/tlaplus/tlaplus （TLA+公式実装）
- SPIN: https://spinroot.com/spin/Src/ （Promela/モデル検査）
- NuSMV: https://nusmv.fbk.eu/ （状態遷移系のモデル検査）

**定理証明器**
- Coq: https://coq.inria.fr/download （証明支援系）
- Lean: https://leanprover.github.io/ （定理証明・形式化）
- Agda: https://wiki.portal.chalmers.se/agda/ （依存型言語）

**プログラム検証**
- Dafny: https://github.com/dafny-lang/dafny （契約ベース検証）
- CBMC: https://www.cprover.org/cbmc/ （Cプログラムのモデル検査）
- Frama-C: https://frama-c.com/ （静的解析/検証）

### 商用ツール

**産業用ツール**
- SCADE Suite (Ansys): https://www.ansys.com/products/embedded-software/ansys-scade-suite （安全クリティカル向け）
- SPARK (AdaCore): https://www.adacore.com/about-spark （Ada向け形式検証）
- Atelier B: https://www.atelierb.eu/ （B手法ツール）

**統合開発環境**
- UPPAAL: https://uppaal.org/ （実時間システムのモデル検査）
- Kind 2: https://kind2-mc.github.io/kind2/ （モデル検査/証明）
- ASTRÉE: https://www.absint.com/astree/ （静的解析）

## E.6 コミュニティとイベント

関連章: 全章（継続学習・実務適用）

### 国際会議

- FM (Formal Methods)：形式手法の国際会議
- CAV (Computer-Aided Verification)：計算機支援検証会議
- ICSE (International Conference on Software Engineering)：ソフトウェア工学国際会議
- POPL (Principles of Programming Languages)：プログラミング言語原理会議

### ワークショップ

- ABZ：ASM, Alloy, B, TLA, VDM, Zの統合会議
- SEFM：Software Engineering and Formal Methods
- FMICS：Formal Methods for Industrial Critical Systems

### 専門組織

- ACM SIGSOFT：ソフトウェア工学特別興味グループ
- IEEE Computer Society：計算機学会
- Formal Methods Europe：欧州形式手法協会

### 日本国内

- 情報処理学会ソフトウェア工学研究会
- 日本ソフトウェア科学会
- 電子情報通信学会

### オンラインコミュニティ

- Stack Overflow（formal-methods タグ）
- Reddit（r/compsci, r/ProgrammingLanguages）
- Zulip Chat（Lean Community）
- coq-club@inria.fr（Coqメーリングリスト）
- tlaplus@googlegroups.com（TLA+メーリングリスト）

## E.7 継続学習のパス

関連章: 第1章（導入）、付録D（演習）

### レベル別学習計画

**初級者（6ヶ月）**
1. Jackson "Software Abstractions" でAlloy学習
2. 本書の演習問題を解答
3. 小規模プロジェクトでの実践適用

**中級者（1年）**
1. Lamport "Specifying Systems" でTLA+習得
2. Coqチュートリアル完了
3. オープンソースプロジェクトへの貢献

**上級者（継続的）**
1. 国際会議での論文発表
2. 新しいツール・手法の調査研究
3. 産業界での知見共有

### 実践的な学習方法

**プロジェクトベース学習**
- GitHubでの形式手法プロジェクト参加
- ハッカソンでの形式手法アプローチ
- オープンソースツールの機能拡張

**コミュニティ参加**
- 地域の形式手法勉強会
- 国際会議への参加・発表
- オンライン議論への積極的参加

本付録を起点に、理論の学習と実践的適用のバランスを保ちながら、自分の関心領域で継続的に深化させてください。
