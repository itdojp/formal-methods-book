---
layout: book
title: "付録C：記法対照表"
description: "Z記法、Alloy、TLA+ 等の記号や構文の一覧表"
locale: "ja"
lang: "ja"
source_path: "src/ja/appendices/appendix-c.md"
---
# 付録C：記法対照表

本付録では、形式的手法で頻出する用語・記号の最小セットと、AI 時代のDoDチェックリストをまとめます。

## C.1 用語集（Glossary）

- **invariant（不変条件）**：常に成り立つべき性質。反例が出たら仕様/実装の破綻を示す。
- **safety（安全性）**：悪いことが起きない性質（例：二重引き落としが起きない）。
- **liveness（活性）**：良いことがいつか起きる性質（例：要求がいつか処理される）。
- **refinement（詳細化）**：抽象仕様から具体仕様へ設計を進めつつ、refinement mapping と内部変数の隠蔽を考慮した具体仕様の振る舞いが抽象仕様を満たすことを示す手続き。含意は概念的に `ConcreteSpec => AbstractSpec` の方向になる。
- **contract（契約）**：事前条件/事後条件を明文化した実行時/検証時のガード。
- **trace（トレース）**：状態遷移の列。反例はトレースとして提示される。
- **counterexample（反例）**：性質が破れる最小の実行例。設計修正の入口。
- **authentication（認証）**：受理した相手、message、session等が対応する正規eventに結び付くというtrace property。non-injectiveかinjectiveかを明示する。
- **attack trace（攻撃トレース）**：攻撃者の知識獲得、message操作、protocol eventを含む性質違反trace。

## C.2 AI 時代のDoDチェックリスト

AI 支援開発では、出力の正当性を検証器で担保することが前提です。

- 仕様差分がある場合、対応する形式仕様も更新されている
- 検証ログに seed/深さ/スコープ/実行コマンドが含まれている
- 反例が出た場合、修正履歴と再検証ログが残っている
- 例外承認の理由・代替策・フォローアップ期限が明記されている

## C.3 記法対照表（Z / Alloy / CSP / TLA+）

以下は「同じ概念」を各記法でどう表現するかの最小対応表です。章内の表記（第4章 Alloy、第5章Z、第6章CSP、第7章 TLA+）と整合する範囲で記載します。

コードブロックのラベル：
- **ツール準拠（そのまま動く）**：そのままツール/CLIへ貼り付けて実行できることを意図した記法（環境差により追加設定が必要な場合あり）。
- **文脈依存スニペット**：構文自体は実ツールに沿うが、前提となる宣言・モデル・ハーネス・対話コンテキストを別途必要とする断片。
- **擬似記法**：説明用に数学記法・省略表記・出力例等を含む記法（ツール入力としての厳密性を保証しない）。

注意：
- **ツール準拠（そのまま動く）**のコードフェンス内には、ツール入力として有効な文字列のみを記載する（出力例・図示・自然言語説明は入れない）。
- 変数宣言・`MODULE main`・検証ハーネス・対話コンテキストなど、周辺の必須要素を別の場所に置く場合は **文脈依存スニペット** を使う。
- 周辺の必須要素を本文や参照先で明示している断片は **文脈依存スニペット**、参照先を明示していない断片や数学記法・省略・自然言語を含む断片は **擬似記法** として扱う。
- 図示/出力例/擬似コードは **擬似記法** を使用する。

### C.3.1 概念の対応（最小セット）

| 概念 | Z記法（本書） | Alloy（Alloy Analyzer 6想定） | CSP（本書/ツール） | TLA+（TLC 想定） |
| --- | --- | --- | --- | --- |
| 集合（型） | `A : ℙ X` | `A: set X` | 事象集合 `{a, b}` / 同期集合 `X` | `A ∈ SUBSET X` |
| 要素所属 | `x ∈ A` | `x in A` | （事象）`a ∈ X` | `x ∈ A` |
| 関係 | `R : X ↔ Y` | `R: X -> Y` | （通常は直接は書かない） | `R ⊆ X × Y` |
| 全関数 | `f : X → Y` | `f: X -> one Y` | （通常は直接は書かない） | `f ∈ [X -> Y]` |
| 部分関数 | `f : X ⇸ Y` | `f: X -> lone Y` | （通常は直接は書かない） | （必要なら部分関数として表現） |
| 状態 | 状態スキーマ | Alloy 6 では `var sig` / `var` field、旧スタイルでは時刻（ステップ）を明示 | プロセス（状態は遷移に埋め込む） | 変数 `v` と次状態 `v'` |
| 初期状態 | `InitState` | `fact init { ... }` または `pred Init[...]` | 初期プロセス `P0` | `Init == ...` |
| 遷移/操作 | `ΔState` | `Trash' = Trash + f` のようにprimeで次状態を参照 | 前置 `a → P`（ツールでは `a -> P`） | `Next == ...` |
| 不変条件（安全性） | スキーマ制約 | `fact` / `assert` | refinement / assertions（ツール依存） | `Invariant == ...` / `[]P` |
| 活性/公平性 | （拡張が必要） | （トレース上で表現） | （ツール依存） | `<>P`, `P ~> Q`, `WF_vars(A)`, `SF_vars(A)` |

注記：
- Zの `↔/→/⇸/↦` は第5章の記号体系に合わせています。
- CSPは本文では数学記法として `→, □, ⊓` を用い、ツール（FDR/CSPM）では代表的に `->, [], |~|` を用います。

### C.3.2 Z記法：主要記号（読みの目安）

| 記号 | 意味 | 読み（例） |
| --- | --- | --- |
| `ℙ X` | 冪集合 | power set of X |
| `x ∈ A` | 要素所属 | x is in A |
| `R : X ↔ Y` | 関係 | relation from X to Y |
| `f : X → Y` | 全関数 | (total) function from X to Y |
| `f : X ⇸ Y` | 部分関数 | partial function from X to Y |
| `x ↦ y` | maplet（ペア） | x maps to y |
| `dom R`, `ran R` | 定義域/値域 | domain/range |

### C.3.3 Alloy：主要記号（Alloy Analyzer 6）

| 記号 | 意味 | 例 |
| --- | --- | --- |
| `sig` / フィールド | 集合と関係 | `sig User { files: set File }` |
| 多重度 `one/lone/some/set` | 要素数制約 | `owner: one User` |
| `fact` | 常に成り立つ制約 | `fact { ... }` |
| `assert` + `check` | 性質検証（反例探索） | `check Inv for 5` |
| `run` | 充足例探索 | `run { ... } for 5` |
| `.` / `~` / `^` | 結合/転置/推移閉包 | `u.files`, `~r`, `^parent` |
| `var` | 状態により変化するシグネチャ/フィールド | `var sig Trash in File {}` |
| `'`（prime） | 次状態の値 | `Trash' = Trash + f` |
| `always` / `eventually` | 常に / いつか | `always Inv`, `eventually some Done` |
| `once` | 過去に一度でも成立 | `restore[f] implies once delete[f]` |
| `after` / `until` | 次状態 / ある条件まで継続 | `after P`, `P until Q` |
| `for ... steps` | トレース長の探索範囲 | `check Inv for 3 but 6 steps` |

補足：Alloy 6 の時相演算子はトレース上で評価されます。
Visualizer や CLI の結果を読むときは、得られた lasso trace、シグネチャのスコープ、`steps` の範囲を合わせて記録してください。

### C.3.4 CSP：主要記号（本文/ツール）

| 概念 | 本書表記（数学記法） | ツール表記（CSPM/FDRの代表例） |
| --- | --- | --- |
| 前置（prefix） | `a → P` | `a -> P` |
| 外部選択 | `P □ Q` | `P [] Q` |
| 内部選択 | `P ⊓ Q` | <code>P &#124;~&#124; Q</code> |
| 同期並行（同期集合X） | <code>P [&#124; X &#124;] Q</code> | <code>P [&#124; X &#124;] Q</code> |
| インタリーブ | <code>P &#124;&#124;&#124; Q</code> | <code>P &#124;&#124;&#124; Q</code> |
| 隠蔽（hiding） | `P \ X` | `P \\ X` |
| リネーム | `P[[ a ← b ]]` | `P[[ a <- b ]]` |

注記：ツール表記は代表例です。プロジェクトでは使用ツール（FDR版、CSP dialect）に合わせて確認してください。

### C.3.5 TLA+：主要記号（TLC）

| 記号 | 意味 | 例 |
| --- | --- | --- |
| `v'` | action 内で参照する次状態の値（LTL の `X` / `○` とは別） | `x' = x + 1` |
| `[]P` / `<>P` | 常に / いつか | `[]Inv`, `<>Goal` |
| `P ~> Q` | `P` が成り立つたびに、その後いつか `Q` が成り立つ | `request ~> response` |
| `WF_vars(A)` / `SF_vars(A)` | action `A` に対する弱 / 強公平性仮定 | `WF_vars(Receive)` |
| `.cfg` | TLC 設定 | 初期状態/不変条件/探索制約 |

`WF_vars(A)` / `SF_vars(A)` は `vars` と `Next` の subaction である action `A` の宣言、および `Init /\ [][Next]_vars` を含む仕様の文脈を必要とするため、単独では「そのまま動く」例ではありません。refinement の説明用含意も、refinement mapping と隠蔽を具体化するまでは擬似記法です。

補足：
- Alloy は有限範囲の反例探索が中心。状態遷移を扱う場合は、時間（ステップ）を明示してモデル化する
- TLA+ は状態遷移と時相論理が中心。action のプライムで現在状態と次状態を関係づけ、`[]` / `<>` / `~>` と公平性で振る舞いの性質を記述する
- Zは状態/操作（スキーマ）で要件を厳密化し、実装へ詳細化する

### C.3.6 Quint：TLA+ 概念との最小対応

Quint は TLA+ の意味論に基づく型付き仕様言語であり、構文はよりプログラミング言語に近い。
本表は章間の読み替えのための概念対応であり、実ツールで使う場合は公式ドキュメントとバージョンを確認する。

| 概念 | TLA+ | Quint（代表例） | 証跡として残すこと |
| --- | --- | --- | --- |
| モジュール | `---- MODULE M ----` | `module M { ... }` | ファイル名、module名、CLI版 |
| 型/定数 | `CONSTANT N` | `const N: int` | 型注釈、override値 |
| 状態変数 | `VARIABLE x` | `var x: int` | 初期値、状態変数一覧 |
| 初期化 | `Init == x = 0` | `val init = x == 0` | init predicate名、unprimed変数であること |
| 次状態関係 | `Next == x' = x + 1` | `action step = x' = x + 1` | next/action名、trace出力 |
| 不変条件 | `Inv == x >= 0` | `val inv = x >= 0` | invariant名、探索長 |
| 時相性質 | `[]P`, `<>P` | `always(P)`, `eventually(P)` | backend、境界、fairness仮定 |
| 有効性 | `ENABLED A` | `enabled(A)` | actionの前提、deadlock扱い |

### C.3.7 Lean / Rocq：定理証明の概念対応

Lean と Rocq はどちらも、定理文と証明を機械的に検査する証明支援系である。
LLM が生成した証明スクリプトや補題は、最終的に各証明器のカーネル/型検査器で受理されたものだけを成果物として扱う。

| 概念 | Lean 4 | Rocq（旧称 Coq） | 注意点 |
| --- | --- | --- | --- |
| 定理/補題 | `theorem` / `lemma` | `Theorem` / `Lemma` | 名称よりも前提と結論の対応をレビューする |
| 証明本体 | tactic script / term | tactic script / term | tactic成功は要求妥当性の証明ではない |
| 未完了穴 | `sorry` / `admit` | `Admitted.` 等 | CI で検出し、例外なら期限と理由を残す |
| 公理・仮定 | `axiom`, `assume`相当 | `Axiom`, `Parameter` 等 | trust boundaryを広げるため棚卸しする |
| 依存ライブラリ | mathlib / Lake | opam package等 | lockfile、ライブラリrevision、toolchainを記録する |

### C.3.8 Rust検証ツール：契約・ハーネス・ghostの対応

Rust検証では、Rustコンパイラの所有権・借用検査だけでなく、追加の仕様・証明義務・模型検査を使う。
ツールごとに構文とサポート範囲が異なるため、下表は概念対応として使う。

| 概念 | Kani | Verus | Creusot / Prusti / Aeneas | 証跡として残すこと |
| --- | --- | --- | --- | --- |
| 検証入口 | proof harness | 仕様付き関数/証明関数 | 契約付き関数、変換対象関数 | 対象関数、対象コミット |
| 事前条件 | harness内の入力制約、contract | `requires` | `requires` / precondition | 入力範囲、除外ケース |
| 事後条件 | `assert!`、contract | `ensures` | `ensures` / postcondition | 仕様レビュー結果 |
| 不変条件 | ループ/状態のassertion | invariant / proof | loop invariant | 未証明部分、timeout |
| ghost code | 通常はモデル/補助値で代替 | ghost/spec/proof code | ghost / Pearlite / 変換先証明 | 実行コードとの分離 |
| 未検証仮定 | `assume`、unwind不足 | `assume`、未証明補題 | trusted/assume/外部仕様 | 例外台帳、影響範囲 |
| 結果 | 成功/反例/リソース切れ | VC成功/失敗 | VC成功/失敗/反例 | solver版、境界、ログ |

### C.3.9 LTL / CTLと確率propertyの概念対応

通常のLTL / CTLは、対象pathまたは計算木で性質が成り立つかを主に真偽で表す。
PRISMのPCTL / CSL系propertyは、同じ到達・継続・長期挙動へ確率、閾値、期待rewardを加える。
下表は読み替えの入口であり、論理間の同値変換表ではない。

| 問いたいこと | 通常のLTL / CTLでの見方 | PRISMの定量的な見方 | 追加で固定すること |
| --- | --- | --- | --- |
| 成功へ到達するか | LTL `F success`、CTL `EF success` / `AF success` | `P=? [ F "success" ]` | 初期状態、確率分布、対象scheduler |
| 到達確率が基準を満たすか | 真偽だけでは確率massを表さない | `P>=0.99 [ F "success" ]` | thresholdの根拠、丸め・許容差 |
| 長期に正常である割合 | 単純な`G` / `AG`は「常に」であり時間割合ではない | `S=? [ "operational" ]` | 定常性、初期分布、吸収class |
| 完了までのcost | trace上のevent数を別途集計 | `R{"cost"}=? [ F "done" ]` | rewardの単位、付与位置、未到達path |
| 環境選択を含む境界 | fairness等を仮定してpathを制約 | MDPの`Pmin` / `Pmax`、`Rmin` / `Rmax` | scheduler / adversary class |
| 不成立時の説明 | 反例trace | 確率値、scheduler、代表path、critical subsystem | 生成方法と網羅範囲 |

特に`P>=1 [ F "success" ]`を機械的に`AF success`と同一視してはいけない。
DTMC、CTMC、MDPではpath measureとnondeterminismの意味が異なり、確率1でもmeasure 0のpathをどう扱うかという境界が残る。
論理式を比較するときは、模型種別、初期状態、scheduler、公平性、時間境界を先にそろえる。

### C.3.10 Tamarin：セキュリティプロトコル検証の最小対応

Tamarinは通常の状態変数中心の記法ではなく、protocol状態と攻撃者知識をmultiset rewritingで表す。
次の表は第13章の例を読むための対応であり、全記法の一覧ではない。

| Tamarin概念 | 本書での読み方 | 第13章例 | 証跡として残すこと |
| --- | --- | --- | --- |
| fact | protocol状態、鍵、message、攻撃者知識 | `!SharedKey`、`OpenChallenge`、`In` / `Out` | persistent / linear、引数、生成rule |
| rule | factを消費・生成するprotocol step | challenge発行、応答送信、受理 | 前提、結果、action fact |
| action fact / event | lemmaがtrace上で参照する観測点 | `ResponseSent`、`ResponseAccepted` | 主体、session data、順序 |
| lemma | executability、秘密性、認証等のtrace property | `Shared_Key_Secrecy`、`Response_Authentication`、`No_Replay` | quantifier、仮定、proof mode、status |
| attack trace | falsified lemmaを破る具体的実行 | 同じ暗号文の二重受理 | 対象lemma、step、攻撃者のmessage操作 |
| equational theory | 暗号演算をsymbolicに簡約する等式 | `sdec(senc(m,k),k)=m` | built-in、未モデル化演算、代数的仮定 |

`Response_Authentication`のようなnon-injective correspondenceと、一つの送信へ一つの受理だけを対応させるinjective propertyは区別する。
symbolicな`verified`を、暗号実装や計算量的安全性の無条件な証明へ読み替えてはいけない。

### C.3.11 SymbiYosys：同期RTL formalの最小対応

SymbiYosysは、RTLとpropertyをYosysで形式模型へ変換し、指定したengineとsolverでBMC、証明、到達性探索を実行するfront endである。
次の表は第8章のarbiter例を読むための対応であり、SystemVerilog Assertions全体の構文表ではない。

| RTL/formal概念 | 第8章例での表現 | 検査上の意味 | 証跡として残すこと |
| --- | --- | --- | --- |
| clock edge | `always_ff @(posedge clk)` | register遷移の1 step | clock、mode、depth |
| reset contract | 最初のedgeだけ`rst`を`assume` | 意図した初期化系列へ環境を制限 | reset極性、assert期間、仮定 |
| safety property | `assert(!(grant0 && grant1))` | 両grant同時assertの禁止 | property位置、PASS / FAIL |
| environment constraint | `assume(...)` | solverが列挙するinput traceを制限 | 全assumptionと根拠 |
| reachability target | `cover(...)` | 関心状態へ至る実行を一つ探す | 到達step、witness VCD |
| BMC | `mode bmc`, `depth 6` | 深さ6以内のassertion違反探索 | bound、counterexample VCD |
| k-induction | `mode prove`, `depth 6` | base caseとtemporal induction | 両phaseのstatus、engine |
| sampled prior value | `$past(req0)` | 前clock edgeのrequest | 初回sampleのguard |

`assert`が`PASS`しても、強すぎる`assume`が欠陥traceを除外していれば主張は空虚になり得る。
同時requestのような重要環境条件を`cover`で到達確認し、到達不能なcoverを安全性成功と同一視しない。
