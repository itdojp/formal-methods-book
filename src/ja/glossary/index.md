# 用語集（Glossary）

本書で頻出する専門用語・略語を、参照しやすい形でまとめます。定義は「本書での用法（最小）」を優先し、厳密な差分が必要な場合は付録A/付録Cや一次情報を参照してください。

## 0) 略語（Acronyms）

- **SAT**：命題充足可能性問題（Satisfiability）。Alloy 等が内部で利用することがある。
- **SMT**：充足可能性の判定を、等式/算術/配列などの理論と統合して扱う枠組み（Satisfiability Modulo Theories）。
- **SMT-LIB**：SMT ソルバーへ問題を渡すための標準形式。2026年時点の公式標準は 2.7 系で、v3 は予備提案として扱う。
- **LTL / CTL**：時相論理（Linear Temporal Logic / Computation Tree Logic）。模型検査で性質を記述する。
- **DTMC / CTMC / MDP**：離散時間Markov連鎖、連続時間Markov連鎖、Markov decision process。PRISMではそれぞれstep確率、遷移rate、非決定的choiceと確率分布の組合せを表す。
- **PCTL / CSL**：確率的な到達・時間・定常性等を記述する時相論理。PCTLは主にDTMC / MDP、CSLはCTMCのpropertyを読む基礎になる。
- **CI**：継続的インテグレーション（Continuous Integration）。PR/夜間/リリース前の検証ゲートに利用する。
- **RMW**：Read-Modify-Write。並行実行で競合（lost update）を生む典型パターン。

## A

**Alloy**：軽量形式的手法の代表的なツール。関係中心のモデリング言語と反例探索器から構成される。→第4章

**Alloy 6**：Alloy に `var`、prime、時相演算子、`steps` 指定を導入し、関係モデル上で状態遷移トレースを直接探索しやすくした系列。→第4章

**Alethe**：SMT-LIB 系の SMT 証明証跡形式。proof-producing solver が出力した `unsat` 証跡を、Carcara や再構成系で独立再検査するための交換形式として使われる。対応理論や checker 互換性は組合せ依存。→第12章/付録E

**AlphaProof**：Google DeepMind が発表した、Lean 上で形式化された数学問題に対して証明または反証を探索する研究システム。競技数学での成果を、一般の仕様妥当性保証と混同しない。→第9章

**AlphaGeometry 2**：Google DeepMind の幾何問題向け neuro-symbolic システム。AlphaProof と同じく、対象領域、形式化、計算資源、評価条件の制約を確認して読む。→第9章

**Apalache**：TLA+ 仕様を SMT にエンコードして有界模型検査や不変条件検査を行う検査器。TLC の上位互換ではなく、構文サポート、有限構造、探索境界、SMT ソルバ依存を確認して使う。→第7章/第8章/第12章

**assume / assert / cover（RTL formal）**：`assume`は対象環境traceを制限し、`assert`は全対象traceで破れてはならない性質を置き、`cover`は条件へ到達するtraceを一つ探す。強すぎる`assume`による空虚性と、`cover`を安全性証明と誤読することを避ける。→第8章/付録C

**アサーション（Assertion）**：成立すべき性質を表明する文。Alloy では `assert`、プログラム検証では実装上のチェック点として用いる。→第4章/第10章

**Aeneas**：Rustプログラムを Charon/LLBC 経由で F*、Rocq/Coq、HOL4、Lean などの証明支援系へ接続する検証ツールチェーン。変換対象と未対応機能を確認して使う。→第10章

**Amazon Bedrock Guardrails Automated Reasoning checks**：LLM 出力を、形式化されたポリシーやドメイン知識に照らして検査する Amazon Bedrock Guardrails の機能。LLM そのものの正しさ証明ではなく、ポリシー範囲、自然言語から論理への変換、対応言語、API制限を確認して使う。→第13章/付録E

**Amazon Verified Permissions**：Cedar ポリシー言語を利用する AWS のマネージド認可サービス。認可ロジックをアプリケーションから分離し、細粒度の権限管理と監査を行う文脈で扱う。→第13章/付録E

**attack trace（攻撃トレース）**：Dolev–Yao攻撃者の知識獲得、message操作、protocol eventを含む性質違反trace。Tamarin等では、falsified lemmaの原因を読む成果物になる。→第13章/付録C

## B

**BDD（Binary Decision Diagram）**：論理関数を効率的に表現するデータ構造。シンボリック模型検査で使用される。→第8章

## C

**CAP 定理**：メッセージ損失によるネットワーク分断を許す非同期モデルでは、分断中に線形化可能な一貫性と、非故障ノードへの全要求に応答する可用性を同時保証できないという結果。平常時を含め常に三つから一つを選ぶという標語ではない。→第7章/付録E

**完全性（Completeness）**：対象の演繹系と意味論について、その意味論で妥当な式を演繹系で証明できるというメタ性質。一階述語論理の標準意味論に対する完全性を、高階論理や依存型理論へ無条件に一般化しない。→第9章

**Cedar**：アプリケーションの認可ロジックをポリシーとして分離して記述するためのオープンソースの言語および認可エンジン。何をポリシー、評価器、解析変換器として検証しているかを区別して扱う。→第13章/付録E

**Cedar Analysis**：Cedar ポリシーを数理式へ変換し、SMT ソルバーで等価性、意図しない許可、冗長・矛盾などを解析するツールキット。解析結果の保証範囲は、形式化された Cedar ポリシーと変換の範囲に依存する。→第13章/付録E

**Certora Prover**：スマートコントラクトと CVL などの仕様ルールを検証条件へ変換し、SMT ソルバーで証明または反例を得る形式検証ツール。仕様ルールの妥当性と未モデル化範囲を別途レビューする。→第13章/付録E

**CSP（Communicating Sequential Processes）**：並行システムを、プロセスと通信の合成として表現する枠組み。→第6章

**CTL（Computation Tree Logic）**：分岐時間論理の一種。到達性や分岐の性質を表現する。→第8章

**cvc5**：CVC4 の後継で、SMT と SyGuS を扱うオープンソースの自動定理証明器/SMT ソルバー。検証ツールのバックエンドとして使う場合は、バージョン、timeout、`unknown`、ログを CI 証跡として残す。→第10章/第12章

**Creusot**：Rust向け演繹検証器。RustコードをWhy3系の検証条件へ接続し、panic、overflow、仕様適合性などを検査する。→第10章

**カリー・ハワード対応**：命題と型、証明とプログラムが対応するという見方。→第9章

## D

**DeepSeek-Prover-V2**：Lean 4 向け形式証明生成を対象とする大規模モデルの研究例。ベンチマーク結果は、形式化済み問題、評価設定、計算資源に依存する。→第9章

**Dolev–Yao攻撃者モデル**：攻撃者が通信を盗聴・改変・再送・合成し、既知鍵で暗号操作できる一方、未知鍵なしに暗号を破らないとするsymbolic network model。鍵侵害やside-channelは別途モデル化する。→第13章/付録E

**DRAT**：命題 CNF の `unsat` を clausal proof で示す proof ecosystem / format。DRAT-trim などの checker は DIMACS CNF と proof を照合するが、元の SMT 問題や自然言語仕様を直接検証するわけではない。→第12章/付録E

**デッドロック**：複数のプロセスが互いに待機し合い、進行できない状態。→第6章/第8章

## F

**FLP 不可能性定理**：完全非同期、決定論的プロセス、最大一つの停止故障という仮定の下で、すべての許容実行における合意の終了を保証できないという結果。部分同期、故障検出器、乱択は仮定を変更して問題を扱う。→第7章/付録E

**不変条件（Invariant）**：常に成り立つべき性質。模型検査では反例として破れ方が示される。→第3章/第7章/第8章

**公平性（Fairness）**：活性を論じる際の実行選択に関する仮定。TLA+ の弱公平性は継続して可能な action を永遠に無視する実行を、強公平性は無限回可能になる action を回避し続ける実行を除外する。実装が自動的に公平になる保証ではなく、強すぎる仮定は「見かけ上の活性」を生む。→第7章

## G

**ghost code（ゴーストコード）**：検証や証明のために導入する補助状態・補助関数・証明用コード。実行時の振る舞いと切り分け、仕様・証明義務・未検証仮定のどこに使ったかを記録する。→第10章/第12章/付録C

## H

**Hoare 論理**：プログラムの正しさを推論するための論理体系。事前条件・プログラム・事後条件の三項組で表現する。→第10章

**Hoare 三項組**：`{P} S {Q}` の形式。Pが事前条件、Sがプログラム、Qが事後条件。→第10章

**harness / proof harness**：検証対象関数を特定条件で呼び出し、assertionや不変条件を検査するための検証入口。テスト harness と似ているが、Kani などでは探索範囲内の全入力に対する模型検査の入口になる。→第10章/付録C

## K

**Kani**：Rust向け模型検査器。`#[kani::proof]` harness、assertion、panic、overflow、`unsafe` 周辺を検査できるが、結果は探索境界と到達範囲に依存する。→第10章/第12章

**k-induction**：有限のbase caseと、性質がk step成り立つなら次stepでも成り立つという帰納stepを組み合わせる証明法。成功は初期化、transition relation、property、assumption、engine設定に相対的である。→第8章/付録C

## L

**Lean 4**：依存型理論に基づくプログラミング言語かつ証明支援系。証明候補や tactic 自動化は、最終的に小さなカーネルで検査される。→第9章

**LeanDojo**：Lean リポジトリから証明状態、tactic、前提情報などを抽出し、学習ベースの定理証明器を訓練・評価する基盤。証明候補生成の実験環境であり、最終判定は Lean の検査に置く。→第9章

**LTL（Linear Temporal Logic）**：線形時間論理。時間の流れに沿った性質を表現する。→第7章/第8章

**LFSC**：LF logical framework に計算的 side condition を加えた proof format / checking framework。cvc5 は LFSC 出力を持つが、未対応 internal rule が trust step として残る場合がある。→第12章/付録E

**LRAT**：命題 CNF 向けの `unsat` 証跡形式。DRAT より checker 向けヒントを明示しやすいが、やはり CNF 後の問題に対する証跡である。→第12章/付録E

**ループ不変条件**：ループ実行中に常に成り立つ条件。部分正しさ/完全正しさの証明に使用する。→第10章

## M

**mathlib**：Lean のコミュニティ主導の形式化数学ライブラリ。既存定理の再利用基盤になるが、ライブラリ更新と依存関係は CI で管理する。→第9章

**model / witness（モデル / 証人）**：`sat` のときに solver が返す具体的な割当てや到達例。エンコード済み制約に対する充足例であり、自然言語要件や元仕様の妥当性そのものは別途レビューする。→第12章/付録C

**Move Prover**：Move スマートコントラクトに形式仕様を付け、論理的性質を自動検証するツール。資産・権限・不変条件の検査に有用だが、仕様誤りや未モデル化範囲は別途管理する。→第13章/付録E

**模型検査（Model Checking）**：指定したモデルの状態空間を探索し、指定した性質を検査する手法。網羅性はモデル、性質、探索設定、fairness、完走状態の範囲に相対的であり、実世界全体の正しさを意味しない。→第8章

**明示的状態探索（Explicit-state search）**：状態を具体的に列挙して探索する模型検査の方式。TLC のような探索では、状態数、fingerprint、workers、探索深さを証跡として残す。→第8章/第12章

**有界探索（Bounded analysis）**：要素数、探索深さ、steps などの境界を固定し、その範囲で反例や証跡を探す方法。境界外の一般性は別途検討する。→第4章/第8章

**有界模型検査（Bounded Model Checking）**：遷移回数や入力範囲を有限に制限し、その範囲で性質違反を探索する模型検査。Alloy の`steps`、Apalache/Kaniの探索境界などは、一般証明ではなく境界付き結果として読む。→第4章/第8章/第12章

## P

**プライム記法（TLA+）**：action の中で、`x` を現在状態の値、`x'` を次状態の値として2状態を関係づける記法。LTL の next-time 演算子 `X` / `○` とは別である。→第7章

**PRISM**：DTMC、CTMC、MDPの確率的・定量的propertyを検査する模型検査器。結果は模型仮定、scheduler、engine、数値精度に相対的であり、実世界の確率妥当性を自動的には保証しない。→第8章/付録B/付録E

**確率的模型検査（Probabilistic model checking）**：確率またはrateを持つ状態遷移模型について、到達確率、閾値、定常確率、期待rewardを計算・判定する手法。ランダムpathだけを標本抽出するstatistical model checkingとは区別する。→第8章

**Prusti**：Viper検証基盤に基づくRust向け契約検証器。safe Rust の事前条件、事後条件、ループ不変条件、panic/overflowの検査を扱う。→第10章

**proof certificate（証明証跡 / 証明書）**：`unsat` を別実装で再検査するために solver が出力する機械可読証跡。何を保証するかは format と checker に依存し、自然言語要件までは自動的に保証しない。→第12章/付録E

**proof checker**：proof certificate や proof term を、入力問題と format の規則に照らして機械検査する checker / kernel。checker 成功は encoded statement に対する成功であり、要件妥当性レビューの代替ではない。→第12章/付録E

## Q

**Quint**：TLA+ の意味論に基づく型付き仕様言語。CLI、REPL、simulation、`verify` により Apalache / TLC と連携できるが、TLA+ 本体や既存教材の完全な置換ではない。→第7章/第8章/第12章

## R

**refinement（詳細化）**：抽象仕様から具体仕様へ設計を進め、refinement mapping と内部変数の隠蔽を考慮した具体仕様が抽象仕様を満たすことを示す手続き。含意は概念的に `ConcreteSpec => AbstractSpec` の方向になる。→第3章/第5章/第7章

**reward property**：状態や遷移へ付けたattempt数、時間、energy、cost等の値について、累積値や到達までの期待値を問う確率property。未到達pathが正の確率で残る場合は無限大になり得る。→第8章/付録C

**Rocq（旧称 Coq）**：依存型理論に基づく証明支援系。2025年以降は The Rocq Prover が公式名称だが、既存資料では Coq 名も残るため併記して扱う。→第9章

## S

**健全性（Soundness）**：対象の演繹系と意味論について、証明可能な式がその意味論で妥当であるというメタ性質。単独で「すべて真」と定義せず、どの論理と意味論に対する性質かを明示する。→第9章

**scheduler / adversary**：MDPの非決定的choiceを履歴に応じて解消する方策。最良・最悪の確率や期待値はschedulerのclassと`min` / `max`の向きに依存する。→第8章/付録C

**statistical model checking**：ランダムに生成したpathの標本からpropertyを近似する手法。sample数、信頼度、誤差幅、最大path長に依存し、MDPのworst-case schedulerを自動的には表さない。→第8章

**記号的模型検査（Symbolic model checking）**：状態を明示列挙せず、論理式や SMT/BDDなどの記号表現で状態集合や遷移を扱う模型検査。ソルバー、抽象化、timeout、`unknown` の扱いを証跡に含める。→第8章/第12章

**sorry / admit**：Lean や Rocq 系で証明を一時的に未完了にするために使われることがある穴埋め。CI では失敗または例外台帳対象として扱う。→第9章/第12章/付録F

**Solidity SMTChecker**：Solidity の形式検証機能。`require` を仮定、`assert` を証明対象として扱い、反例、警告、`unknown` を確認する。仕様が目的に合っているかは別途レビューする。→第13章/付録E

**スマートコントラクト検証**：資産移転、残高、不変条件、権限、清算条件などを形式仕様として記述し、実装が満たすかを検査する実務領域。検証済み表示だけでなく、仕様、仮定、対象コミット、ツールログを確認する。→第13章/付録E

**安全性（Safety）**：「悪いことが起きない」性質。不変条件として表現されることが多い。→第8章

**活性（Liveness）**：「良いことがいつか起きる」性質。過度な前提（公平性）に依存しやすい。→第8章

**SPIN**：Promela言語による並行システムの模型検査ツール。→第6章/第8章

**SymbiYosys（sby）**：Yosysを中心とするopen-source RTL formal flowのfront end。BMC、prove、coverをengine/backendへ接続し、結果はRTL、property、assumption、mode、depth、toolchainに相対的である。→第8章/付録B/付録E

**SMT-LIB v3**：SMT-LIB 3.0 の予備提案。高階論理、ポリモーフィズム、依存型的な方向を含むが、SMT-LIB 2.x を直ちに置き換えるものではない。→第12章

**状態空間（State Space）**：システムが取りうる状態の集合。状態爆発が主要課題。→第8章

**状態爆発問題**：状態数が指数的に増大して検証が困難になる問題。→第8章

**時相演算子（Temporal operator）**：トレース上の性質を表す演算子。Alloy 6 の `always` / `eventually` / `after` / `until` や TLA+ の `[]` / `<>` / `~>` などが該当する。TLA+ のプライムは action 内の次状態値を表す別の記法である。→第4章/第7章/第8章

## T

**Tamarin Prover**：multiset rewriting rules、facts、events、trace lemmasで、active attacker下のセキュリティプロトコルをsymbolicに検証するツール。結果はequational theory、仮定、lemma、proof設定に相対的である。→第13章/付録B/付録E

**TLA+**：分散・並行システムを、現在状態と次状態の関係である action、および振る舞い上の時相式として記述する仕様言語。通常はスタッタリングを許す仕様を基本とし、LTL の next-time 演算子とプライムを同一視しない。→第7章

**TLC**：TLA+ 仕様を具体化した有限モデルの到達可能状態を列挙する明示的状態模型検査器。TLA+ は一般的な静的型システムを持たず、`TypeOK` / `TypeInvariant` などの不変条件で値の集合を明示する。結果は `.cfg`、性質、fairness、状態制約、完走状態に依存する。→第7章/第8章

**trusted kernel（信頼核）**：証明項を基礎論理と現在の環境の下で検査する小さな中核。保証には kernel だけでなく、追加公理、未完了穴、外部 solver の接続方法、抽出・コード生成などの信頼基盤も関係する。→第9章

**trusted computing base（TCB）**：最終保証に関与する信頼前提の集合。kernel に加え、追加公理、未検証変換、外部 solver 連携、proof reconstruction、抽出、コード生成、運用例外まで含み得る。→第9章/第12章

**トレース（Trace）**：状態遷移の列。反例はトレースとして提示され、セキュリティプロトコル検証では攻撃者操作を含むattack traceとして読むことがある。→第4章/第8章/第13章

**ラッソトレース（Lasso trace）**：有限個の状態列の末尾が以前の状態へ戻る形で、無限トレースを有限表現する方法。Alloy 6 の時相解析結果を読む際に重要である。→第4章

## U

**unknown**：SMT ソルバーや検証器が、与えられた設定・制限時間・論理断片では結論を返せなかった状態。成功でも反例なしでもなく、CI では調査対象として扱う。→第12章

## V

**vacuity（空虚性）**：性質が実質的な対象traceを検査したからではなく、強すぎる仮定や到達不能な前提によって自明に成立する状態。assumption reviewと意味のあるcoverで検出を補助する。→第8章/付録C

**Verus**：Rust風の仕様・証明記法と SMT を用いて、低レベルシステムコードの機能的正しさや不変条件を静的に検証するツール。→第10章

## Z

**Z3**：Microsoft Research 由来の定理証明器/SMT ソルバー。多くの検証・解析ツールでバックエンドまたはAPIとして使われる。→第10章/第12章

**Z記法**：状態ベースの形式仕様記述言語。スキーマで状態と操作を表現する。→第5章

---

## 関連リンク

- [付録A：数学的基礎の復習]({{ '/appendices/appendix-a/' | relative_url }})
- [付録C：記法対照表]({{ '/appendices/appendix-c/' | relative_url }})
