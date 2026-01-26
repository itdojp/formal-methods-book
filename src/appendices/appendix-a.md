# 付録A：数学的基礎の復習

本書で頻出する記法を「読み直せる場所」として、集合・論理・関係・写像・帰納の最小セットを整理します。

## A.1 集合（set）

- 要素所属：`x \in A`
- 部分集合：`A \subseteq B`
- 和集合：`A \cup B`
- 共通部分：`A \cap B`
- 差集合：`A \setminus B`
- べき集合：`SUBSET A`（TLA+の表記。数学では `\mathcal{P}(A)` ）

用法（例）：
- 「状態集合」や「許容される値の集合」を宣言して、仕様の前提条件を明確化する
- 「不変条件（安全性）」として、状態が満たすべき集合的制約を列挙する

## A.2 論理（logic）

### 命題論理（最小）

- 否定：`~P` / `\lnot P`
- 連言：`P /\ Q`
- 選言：`P \/ Q`
- 含意：`P => Q`（「PならばQ」）
- 同値：`P <=> Q`

実務上の要点：
- 仕様の「曖昧語（可能/適切/通常）」は、論理式（前提条件・不変条件・活性）へ落とし込んでから議論する
- 含意（`=>`）は「前提が真のときだけ主張する」ため、前提の過不足が検証結果に直結する

### 述語論理（最小）

- 全称量化：`\A x \in S : P(x)`（TLA+の書き方。数学では `\forall x \in S`）
- 存在量化：`\E x \in S : P(x)`（数学では `\exists x \in S`）

## A.3 関係（relation）

関係は、直積集合 `X \times Y` の部分集合として捉えます：`R \subseteq X \times Y`。

- 関係の合成（概念）：`R ; S`
- 逆関係（概念）：`R^{-1}`

Alloyでは「関係（relation）」が中核であり、`sig` とフィールド（`->`）で構造を表現します。Z記法でも、状態や操作を関係として記述する見方が有効です。

## A.4 写像（function / mapping）

写像（関数）は、入力に対して出力が一意に決まる関係です。

- 全域関数：`f : X -> Y`（全ての `x \in X` に `f(x)` が定義される）
- 単射（injective）/ 全射（surjective）/ 全単射（bijective）：データ整合や参照制約の議論で頻出

TLA+では関数集合を `f \in [X -> Y]` のように表します。更新は `EXCEPT` 構文で表現できます（詳細は第7章）。

## A.5 帰納法（induction）

有限状態の性質や再帰的定義に対して、「帰納（induction）」は最小の証明スキーマです。

### 数学的帰納法（テンプレ）

1. 基底（base）：`P(0)`（または最小ケース）が成り立つ
2. 帰納ステップ（step）：`P(n)` が成り立つと仮定して `P(n+1)` を示す
3. よって任意の `n` で `P(n)` が成り立つ

模型検査（TLC等）は「反例探索」に強く、定理証明は「一般化（任意n）」に強い、という役割分担の理解につながります。

## A.6 本書内の参照（章リンク）

- 関係中心モデリング（Alloy）：第4章 <https://itdojp.github.io/formal-methods-book/chapters/chapter04/>
- 状態/操作の厳密化（Z記法）：第5章 <https://itdojp.github.io/formal-methods-book/chapters/chapter05/>
- 集合・関数・状態遷移（TLA+）：第7章 <https://itdojp.github.io/formal-methods-book/chapters/chapter07/>
- 模型検査（状態空間・反例）：第8章 <https://itdojp.github.io/formal-methods-book/chapters/chapter08/>
- 定理証明と帰納（証明の再現性）：第9章 <https://itdojp.github.io/formal-methods-book/chapters/chapter09/>
- Hoare論理（事前/事後条件）：第10章 <https://itdojp.github.io/formal-methods-book/chapters/chapter10/>

補足：本付録は導入用の最小セットです。厳密な定義や証明は、離散数学/論理学の教科書を参照してください。
