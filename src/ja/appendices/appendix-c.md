# 付録C：記法対照表

本付録では、形式的手法で頻出する用語・記号の最小セットと、AI時代のDoDチェックリストをまとめます。

## C.1 用語集（Glossary）

- **invariant（不変条件）**：常に成り立つべき性質。反例が出たら仕様/実装の破綻を示す。
- **safety（安全性）**：悪いことが起きない性質（例：二重引き落としが起きない）。
- **liveness（活性）**：良いことがいつか起きる性質（例：要求がいつか処理される）。
- **refinement（詳細化）**：抽象仕様から実装仕様へ段階的に具体化する手続き。
- **contract（契約）**：事前条件/事後条件を明文化した実行時/検証時のガード。
- **trace（トレース）**：状態遷移の列。反例はトレースとして提示される。
- **counterexample（反例）**：性質が破れる最小の実行例。設計修正の入口。

## C.2 AI時代のDoDチェックリスト

AI支援開発では、出力の正当性を検証器で担保することが前提です。

- 仕様差分がある場合、対応する形式仕様も更新されている
- 検証ログに seed/深さ/スコープ/実行コマンドが含まれている
- 反例が出た場合、修正履歴と再検証ログが残っている
- 例外承認の理由・代替策・フォローアップ期限が明記されている

## C.3 記法対照表（Z / Alloy / CSP / TLA+）

以下は「同じ概念」を各記法でどう表現するかの最小対応表です。章内の表記（第4章Alloy、第5章Z、第6章CSP、第7章TLA+）と整合する範囲で記載します。

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

| 概念 | Z記法（本書） | Alloy（Alloy Analyzer 6想定） | CSP（本書/ツール） | TLA+（TLC想定） |
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
| 活性/公平性 | （拡張が必要） | （トレース上で表現） | （ツール依存） | `<>P`, `WF_vars(A)`, `SF_vars(A)` |

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
| `v'` | 次状態の値 | `x' = x + 1` |
| `[]P` / `<>P` | 常に / いつか | `[]Inv`, `<>Goal` |
| `WF_vars(A)` / `SF_vars(A)` | 公平性仮定 | `WF_vars(Next)` |
| `.cfg` | TLC設定 | 初期状態/不変条件/探索制約 |

補足：
- Alloyは有限範囲の反例探索が中心。状態遷移を扱う場合は、時間（ステップ）を明示してモデル化する
- TLA+は状態遷移と時相論理が中心。実装詳細を詰める前に、高レベルで性質（不変/活性）を固定する
- Zは状態/操作（スキーマ）で要件を厳密化し、実装へ詳細化する

### C.3.6 Quint：TLA+概念との最小対応

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
LLMが生成した証明スクリプトや補題は、最終的に各証明器のカーネル/型検査器で受理されたものだけを成果物として扱う。

| 概念 | Lean 4 | Rocq（旧称Coq） | 注意点 |
| --- | --- | --- | --- |
| 定理/補題 | `theorem` / `lemma` | `Theorem` / `Lemma` | 名称よりも前提と結論の対応をレビューする |
| 証明本体 | tactic script / term | tactic script / term | tactic成功は要求妥当性の証明ではない |
| 未完了穴 | `sorry` / `admit` | `Admitted.` 等 | CIで検出し、例外なら期限と理由を残す |
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
