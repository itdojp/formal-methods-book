# 第9章　定理証明の基礎

## 9.1 証明の機械化：数学者とコンピュータの協調

### 証明という人類の知的営み

数学的証明は、人類の知的活動の最高峰の一つです。古代ギリシャのユークリッドから現代の数学者まで、厳密な論理的推論により真理を確立してきました。しかし、数学的証明は完全に信頼できるものでしょうか？

歴史を振り返ると、有名な数学者による証明にも誤りが発見されています。アッペル・ハーケンによる四色定理の証明（1976年）では、コンピュータによる大量の場合分けが必要でした。この証明は数学界に衝撃を与えました。なぜなら、人間が完全に検証することが困難な証明だったからです。

現代では、数学的証明はますます複雑になり、人間の認知能力の限界に挑戦しています。分類定理、フェルマーの最終定理の証明、ポアンカレ予想の解決など、これらの証明は数百ページに及び、完全に理解できる数学者は世界でも数人という状況です。

### 機械による証明検査の必要性

ソフトウェアシステムの証明では、この問題はさらに深刻です。実用的なプログラムの正しさを証明するには、膨大な詳細を扱う必要があります。人間が手作業で行うには、現実的ではありません。

機械による証明検査（Proof Checking）は、この限界を克服する方法です。人間が証明の大筋を構成し、機械が詳細を検証し、論理的な正しさを保証します。これにより、人間の創造性と機械の精密性を組み合わせることができます。

### 証明支援系の基本思想

証明支援系（Proof Assistant）は、数学的証明の構築と検証を支援するツールです。単なる計算機ではなく、論理的推論を行う「思考の道具」として設計されています。

証明支援系の核心的なアイデアは、「型理論」です。プログラムの型システムを拡張し、命題を型として、証明をプログラムとして表現します。これにより、「証明を書くこと」と「プログラムを書くこと」が統一されます。

```coq
Theorem addition_commutative : forall n m : nat, n + m = m + n.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - simpl. rewrite <- plus_n_O. reflexivity.
  - simpl. rewrite IHn'. rewrite plus_n_Sm. reflexivity.
Qed.
```

この例では、自然数の加法の交換律を証明しています。証明は、人間が理解できる形で記述されていますが、同時に機械が検証できる厳密な形式を持っています。

### 第8章模型検査との相補的関係

定理証明と模型検査は、相補的な検証手法です。第8章で学んだ模型検査が「有限の範囲での完全性」を提供するのに対し、定理証明は「無限の範囲での厳密性」を提供します：

**模型検査の特徴**：
- 自動的な検証
- 反例の提供
- 有限状態システム向け
- 学習コストが相対的に低い

**定理証明の特徴**：
- 数学的な厳密性
- 無限システムの扱い
- 構成的な証明
- 高い学習コスト、高い保証

両手法を組み合わせることで、包括的な検証戦略を構築できます。

### カリー・ハワード対応の深い意味

カリー・ハワード対応（Curry-Howard Correspondence）は、論理と計算の深い関係を示す発見です。この対応により、以下のような等価性が成り立ちます：

- **命題** ↔ **型**
- **証明** ↔ **プログラム**
- **証明の正規化** ↔ **プログラムの実行**

この対応は単なる類推ではありません。実際に、論理的な推論規則とプログラムの型規則が同じ構造を持っています。

例：含意の導入規則
```
論理：P → Q を証明するには、P を仮定して Q を証明する
型理論：型 P → Q の値を構築するには、型 P の値を受け取って型 Q の値を返す関数を定義する
```

### 構成的数学と古典数学

証明支援系では、しばしば「構成的数学」の枠組みが使われます。これは、存在証明において実際にその存在物を構築することを要求する数学です。

**古典的証明**：「√2 は無理数である」
証明：背理法により、√2 が有理数であると仮定して矛盾を導く

**構成的証明**：「アルゴリズムAは、入力nに対して条件Pを満たす出力を生成する」
証明：実際にアルゴリズムAを定義し、その正しさを示す

構成的証明からは、実際に使用可能なアルゴリズムが抽出できます。これは、単に正しさを保証するだけでなく、実用的な価値も提供します。

### 人間と機械の役割分担

効果的な定理証明では、人間と機械の適切な役割分担が重要です。

**人間の役割**：
- 証明戦略の立案
- 重要な補題の発見
- 抽象化レベルの決定
- 直観的理解の提供

**機械の役割**：
- 詳細な推論ステップの検証
- 膨大な場合分けの処理
- 型チェックと整合性確認
- 自動的な証明探索

この協調により、人間の創造性を保ちながら、機械の精密性を活用できます。

### 信頼性の確立

証明支援系自体の信頼性も重要な問題です。証明支援系にバグがあれば、検証された証明も信頼できません。

この問題に対する解決策は、「小さな信頼核（Trusted Kernel）」の設計です。証明支援系の中核部分を可能な限り小さく、シンプルに保ち、その部分のみの正しさを保証すれば十分です。

例えば、Coqの信頼核は数千行程度のOCamlコードです。これに対し、全体のシステムは数十万行に及びます。大部分の機能（自動証明、便利な記法など）は信頼核の外で実装され、最終的には信頼核による検証を受けます。

### 証明の再利用と蓄積

機械化された証明の重要な利点は、再利用可能性です。一度証明された定理は、ライブラリとして蓄積され、他の証明で活用できます。

現在、数学の主要な分野で大規模な形式化プロジェクトが進行中です：

- **mathlib**（Lean）：現代数学の広範囲な形式化
- **Mathematical Components**（Coq）：代数的構造の体系的形式化
- **Archive of Formal Proofs**（Isabelle/HOL）：様々な分野の定理の集積

これらのライブラリにより、複雑な数学的結果も、既存の証明を組み合わせて比較的容易に証明できるようになりつつあります。

### 教育への影響

証明支援系は、数学教育にも大きな影響を与える可能性があります。学生が証明を学ぶ際、証明支援系を使うことで：

- 論理的推論の厳密性を体験できる
- 証明の各ステップを明確に理解できる
- 誤った推論を即座に発見できる
- 複雑な証明を段階的に構築できる

実際に、いくつかの大学では、数学の授業に証明支援系が導入されています。

### 産業界での活用

証明支援系は、学術的な研究だけでなく、産業界でも重要な役割を果たし始めています：

- **CompCert**：C コンパイラの完全な正しさ証明
- **seL4**：マイクロカーネルの機能的正しさ証明
- **Amazon s2n**：TLS 実装の暗号プロトコル証明

これらの成功事例は、定理証明が実用的な技術として成熟しつつあることを示しています。

## 9.2 論理の基礎：推論の規則

### 形式論理という言語

論理学は、正しい推論の規則を研究する学問です。日常的な議論では、しばしば曖昧さや感情が入り込みますが、形式論理では、純粋に構造的な推論規則のみを扱います。これにより、機械的に検証可能な推論が可能になります。

形式論理を理解することは、証明支援系を使う上で不可欠です。なぜなら、証明支援系の背後にある推論規則は、すべて形式論理に基づいているからです。

### 命題論理：論理の出発点

命題論理は、論理学の最も基本的な部分です。原子命題（分割できない基本的な命題）と論理結合子から構成されます。

**基本的な論理結合子**：
- **∧** (論理積, AND): P ∧ Q は「Pかつ Q」
- **∨** (論理和, OR): P ∨ Q は「Pまたは Q」
- **¬** (否定, NOT): ¬P は「Pではない」
- **→** (含意, IMPLIES): P → Q は「PならばQ」
- **↔** (同値, IF AND ONLY IF): P ↔ Q は「PとQは同値」

これらの結合子の意味は、真理表により完全に定義されます：

```
P | Q | P∧Q | P∨Q | P→Q | P↔Q
--+---+-----+-----+-----+-----
T | T |  T  |  T  |  T  |  T
T | F |  F  |  T  |  F  |  F  
F | T |  F  |  T  |  T  |  F
F | F |  F  |  F  |  T  |  T
```

### 自然演繹：人間的な推論の形式化

自然演繹（Natural Deduction）は、人間の自然な推論過程を形式化した証明体系です。ゲルハルト・ゲンツェンにより開発されたこの体系は、現代の証明支援系の基礎となっています。

**含意の導入規則（→I）**：
```
[P]
 ⋮
 Q
---
P→Q
```

「Pを仮定してQが証明できれば、P→Qが証明できる」

**含意の除去規則（→E, Modus Ponens）**：
```
P→Q  P
------
  Q
```

「P→QとPが両方証明できれば、Qが証明できる」

**論理積の導入規則（∧I）**：
```
P  Q
----
P∧Q
```

**論理積の除去規則（∧E）**：
```
P∧Q     P∧Q
----  or ----
 P        Q
```

### 証明の構造：証明木

自然演繹では、証明は「証明木」として表現されます。葉が仮定または公理、内部ノードが推論規則の適用、根が証明したい結論になります。

**例：((P→Q)∧(Q→R))→(P→R) の証明**：
```
[P→Q]¹  [P]³   [Q→R]¹  [P→Q]¹  [P]³
------------- ----------------------
      Q                Q       [Q→R]¹
      -------------------------
                   R
                 -----
                 P→R                 ³
           ------------------
           (P→Q)∧(Q→R)→(P→R)         ¹
```

この証明木は、三段論法の正しさを示しています。

### 述語論理：より表現力豊かな論理

命題論理では、命題を分割不可能な単位として扱います。しかし、実際の数学的推論では、「すべての自然数nについて」「ある実数xが存在して」といった量化が必要です。

述語論理（First-Order Logic）は、量詞を導入することで、この表現力を実現します：

**全称量詞（∀）**：∀x. P(x) は「すべてのxについて P(x)」
**存在量詞（∃）**：∃x. P(x) は「ある x が存在して P(x)」

**例**：
- ∀n:ℕ. even(n) ∨ odd(n) 「すべての自然数は偶数または奇数」
- ∃x:ℝ. x² = 2 「平方根が2の実数が存在する」

### 量詞の推論規則

**全称量詞の導入（∀I）**：
```
P(a)  (aは新しい変数)
----------------
    ∀x. P(x)
```

「任意の要素aについてP(a)が証明できれば、∀x. P(x)が証明できる」

**全称量詞の除去（∀E）**：
```
∀x. P(x)
--------
  P(t)
```

「∀x. P(x)が証明できれば、任意の項tについてP(t)が証明できる」

**存在量詞の導入（∃I）**：
```
P(t)
--------
∃x. P(x)
```

**存在量詞の除去（∃E）**：
```
∃x. P(x)  [P(a)]
            ⋮     (aは新しい変数)
            Q
-----------------
        Q
```

### 等式の推論

数学的推論では、等式が重要な役割を果たします。等式には以下の基本的な性質があります：

**反射性（Reflexivity）**：
```
-------
t = t
```

**対称性（Symmetry）**：
```
t₁ = t₂
-------
t₂ = t₁
```

**推移性（Transitivity）**：
```
t₁ = t₂  t₂ = t₃
---------------
    t₁ = t₃
```

**置換性（Substitution）**：
```
t₁ = t₂  P(t₁)
-------------
    P(t₂)
```

### 高階論理への拡張

一階述語論理では、量化は個体変数についてのみ行えます。しかし、数学では関数や関係についても量化したい場合があります。

**高階論理（Higher-Order Logic）**では、関数や述語についても量化できます：

```coq
Definition continuous (f : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x y, |x - y| < δ → |f(x) - f(y)| < ε

Theorem exists_continuous_function : ∃ f : ℝ → ℝ, continuous f.
```

### 型理論：論理と計算の統一

現代の証明支援系では、「型理論」が論理の基礎として使われることが多くなっています。型理論では、命題と型が統一され、より自然に数学的概念を表現できます。

**依存型（Dependent Types）**：
```coq
Definition Vector (A : Type) (n : nat) : Type := 
  { l : list A | length l = n }.

Definition head {A : Type} {n : nat} (v : Vector A (S n)) : A :=
  match v with
  | exist _ (x :: _) _ => x
  end.
```

この例では、長さが型に含まれたベクトル型を定義しています。型システムにより、空でないベクトルのみが `head` 関数に渡されることが保証されます。

### 推論規則の健全性と完全性

論理体系の重要な性質として、「健全性」と「完全性」があります：

**健全性（Soundness）**：推論規則により証明できるものは、すべて真である
**完全性（Completeness）**：真であるものは、すべて推論規則により証明できる

これらの性質により、論理体系の正しさが保証されます。証明支援系では、健全性が特に重要です。なぜなら、誤った定理を証明できてしまっては、システム全体の信頼性が崩れるからです。

### 直観主義論理と古典論理

証明支援系では、しばしば「直観主義論理」が採用されます。これは、古典論理よりも制限的な論理体系です。

**主な違い**：
- **排中律の扱い**：古典論理では P ∨ ¬P が常に成り立つが、直観主義論理では成り立たない
- **二重否定の除去**：古典論理では ¬¬P から P が導けるが、直観主義論理では導けない

直観主義論理の利点は、証明から実際の計算（アルゴリズム）を抽出できることです。存在証明から実際にその存在物を構築する手順が得られ、実用的な価値があります。

### 論理の実装：証明支援系での表現

実際の証明支援系では、これらの論理規則がどのように実装されているかを理解することも重要です。

**Coq での例**：
```coq
Lemma modus_ponens : forall P Q : Prop, P -> (P -> Q) -> Q.
Proof.
  intros P Q HP HPQ.
  apply HPQ.
  exact HP.
Qed.
```

この証明は、含意の除去規則（modus ponens）の証明です。`intros` タクティックで仮定を導入し、`apply` タクティックで含意の除去を適用し、`exact` タクティックで仮定を使用しています。

論理の基礎を理解することで、証明支援系を効果的に使用し、数学的に厳密な証明を構築できるようになります。

## 9.3 型理論：プログラムと証明の統一

### 型という概念の進化

プログラミング言語における「型」は、単にメモリレイアウトを指定するためのものから始まりました。しかし、型理論の発展により、型は論理的性質を表現する強力な道具へと進化しました。現代の型理論では、型とプログラムが密接に結びつき、「正しいプログラムを書くこと」と「定理を証明すること」が同じ活動になります。

この統一により、従来は別々に扱われていた「計算」と「論理」が、統一的な枠組みで理解できるようになりました。これは、コンピュータサイエンスにおける最も美しい発見の一つです。

### 単純型付きλ計算

型理論の出発点は、単純型付きλ計算です。これは、関数を第一級の値として扱う計算体系に、型システムを追加したものです。

**基本型**：
- Base types: `Bool`, `Nat`, `String` など
- 関数型: `A → B` （Aを受け取ってBを返す関数）

**型付き λ式の例**：
```
id : A → A = λx:A. x                 (* 恒等関数 *)
compose : (B → C) → (A → B) → (A → C) = λf:B→C. λg:A→B. λx:A. f(g(x))
```

この体系では、「型付け可能なプログラムは実行時エラーを起こさない」という重要な性質が成り立ちます。

### カリー・ハワード対応の詳細

カリー・ハワード対応は、論理と型理論の間の深い関係を示します：

**命題と型の対応**：
```
論理                型理論
P ∧ Q      ↔      P × Q        (直積型)
P ∨ Q      ↔      P + Q        (直和型)
P → Q      ↔      P → Q        (関数型)
⊤ (真)     ↔      Unit         (単位型)
⊥ (偽)     ↔      Empty        (空型)
∀x:A. P(x) ↔      (x:A) → P(x) (依存関数型)
∃x:A. P(x) ↔      (x:A) × P(x) (依存対型)
```

**証明と項の対応**：
```
論理的推論               プログラム構築
P ∧ Q の導入   ↔   対 (p, q) の構築
P ∧ Q の除去   ↔   射影 fst(pair), snd(pair)
P → Q の導入   ↔   λ抽象 λx:P. body
P → Q の除去   ↔   関数適用 f(argument)
```

### 依存型：型の表現力の革命

依存型（Dependent Types）は、値に依存して決まる型です。これにより、プログラムの性質を型レベルで表現できます。

**長さ付きリストの例**：
```coq
Inductive vec (A : Type) : nat → Type :=
| nil : vec A 0
| cons : ∀ n, A → vec A n → vec A (S n).

Definition head {A : Type} {n : nat} (v : vec A (S n)) : A :=
  match v with
  | cons _ x _ => x
  end.
```

この定義では、`head` 関数は空でないリスト（長さが `S n` = n+1）にのみ適用できます。型システムにより、実行時エラーが防がれます。

### 帰納型：データ構造の表現

帰納型（Inductive Types）は、再帰的なデータ構造を定義するための機構です。

**自然数の定義**：
```coq
Inductive nat : Type :=
| O : nat
| S : nat → nat.
```

これは、「自然数は 0 であるか、他の自然数の後継である」という定義です。

**リストの定義**：
```coq
Inductive list (A : Type) : Type :=
| nil : list A
| cons : A → list A → list A.
```

**二分木の定義**：
```coq
Inductive tree (A : Type) : Type :=
| leaf : tree A
| node : A → tree A → tree A → tree A.
```

### 帰納法の原理

帰納型の定義から、自動的に帰納法の原理が生成されます。

**自然数の帰納法**：
```coq
nat_ind : ∀ P : nat → Prop,
  P 0 →                           (* base case *)
  (∀ n, P n → P (S n)) →         (* inductive step *)
  ∀ n, P n                       (* conclusion *)
```

**リストの帰納法**：
```coq
list_ind : ∀ (A : Type) (P : list A → Prop),
  P nil →                                    (* base case *)
  (∀ (a : A) (l : list A), P l → P (cons a l)) →  (* inductive step *)
  ∀ l : list A, P l                         (* conclusion *)
```

### 等式型：同一性の表現

等式型（Equality Type）は、二つの値が等しいことを型レベルで表現します。

```coq
Inductive eq (A : Type) (x : A) : A → Prop :=
| eq_refl : eq A x x.

Notation "x = y" := (eq _ x y).
```

この定義により、`x = y` の証明は、`x` と `y` が定義的に等しい場合のみ構築できます。

### 依存パターンマッチング

依存型を持つデータに対するパターンマッチングでは、各分岐で型が変化します。

```coq
Definition vector_case {A : Type} {n : nat} (v : vec A n) :
  match n with
  | 0 => unit
  | S _ => A
  end :=
  match v with
  | nil _ => tt
  | cons _ _ x _ => x
  end.
```

この例では、`v` の型に応じて、戻り値の型が `unit` または `A` に変化します。

### 証明の関連性（Proof Relevance）

型理論では、「証明の関連性」という概念があります。これは、同じ命題の異なる証明を区別するかどうかという問題です。

**Proof Irrelevance（証明非関連性）**：
```coq
Axiom proof_irrelevance : ∀ (P : Prop) (p1 p2 : P), p1 = p2.
```

この公理は、同じ命題の証明はすべて等しいとするものです。

**Proof Relevance（証明関連性）**：
異なる証明を区別し、証明自体に計算的内容を持たせることができます。

### 宇宙（Universe）階層

型理論では、「型の型」を扱う必要があります。これにより、無限の階層構造が生まれます。

```coq
Type₀ : Type₁ : Type₂ : Type₃ : ...
```

**例**：
```coq
nat : Type₀
Type₀ : Type₁
(Type₀ → Type₀) : Type₁
```

この階層により、ラッセルのパラドックスのような矛盾を回避できます。

### 構成的数学と計算

型理論に基づく証明支援系では、証明から実際の計算プログラムを抽出できます。

```coq
Fixpoint gcd (a b : nat) {struct a} : nat :=
  match a with
  | 0 => b
  | S a' => gcd (b mod S a') (S a')
  end.

Theorem gcd_correct : ∀ a b : nat, 
  gcd a b = greatest_common_divisor a b.
```

この証明からは、実際に使用可能な最大公約数計算アルゴリズムが抽出されます。

### 種々の型理論

現代では、様々な型理論が研究・実装されています：

**Calculus of Constructions（構成の計算）**：
- Coq の基礎理論
- 依存型 + 多相性 + 高階型

**Martin-Löf 型理論**：
- 構成的数学の基礎
- 等式の反射的扱い

**Homotopy Type Theory（ホモトピー型理論）**：
- 等式に幾何学的解釈を与える
- ユニヴァレンス公理の導入

**Cubical Type Theory**：
- ホモトピー型理論の計算的実現
- 計算的ユニヴァレンス

### 実践的な型設計

実際の証明支援系では、適切な型設計が重要です。

**エラーハンドリングの型**：
```coq
Inductive result (A E : Type) : Type :=
| Ok : A → result A E
| Error : E → result A E.
```

**状態を持つ計算の型**：
```coq
Definition State (S A : Type) : Type := S → A × S.
```

**資源管理の型**：
```coq
Inductive linear (A : Type) : Type :=
| use_once : A → linear A.
```

型理論は、プログラムと証明を統一し、より安全で表現力豊かなプログラミングを可能にします。この理論的基盤により、証明支援系は数学的厳密性と計算的効率性を両立できるのです。

## 9.4 証明支援系の実践

### Coq：構成の計算に基づく証明支援系

Coq は、フランス国立情報学自動制御研究所（INRIA）で開発された証明支援系です。構成の計算（Calculus of Constructions）という型理論に基づき、数学的証明とプログラム開発を統一的に扱うことができます。

Coq の特徴は、証明とプログラムが同じ言語で記述され、型チェッカーが証明の正しさを自動的に検証することです。これにより、証明にバグが含まれる可能性を排除できます。

### 基本的な証明の構築

まず、最も基本的な論理的性質から証明を始めてみましょう。

**含意の推移性**：
```coq
Theorem implication_transitivity : 
  forall P Q R : Prop, (P -> Q) -> (Q -> R) -> (P -> R).
Proof.
  intros P Q R H1 H2 H3.
  apply H2.
  apply H1.
  exact H3.
Qed.
```

この証明では：
- `intros` で仮定を導入
- `apply` で仮定や既知の定理を適用
- `exact` で完全に一致する証拠を提供

**論理積の交換律**：
```coq
Theorem and_commutative : forall P Q : Prop, P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
  - exact HQ.
  - exact HP.
Qed.
```

分解パターン `[HP HQ]` により、論理積の仮定を要素に分解できます。

### 帰納法による証明

数学的帰納法は、自然数や帰納的データ構造の性質を証明する基本的な手法です。

**自然数の性質**：
```coq
Fixpoint plus (n m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Theorem plus_O_n : forall n : nat, plus O n = n.
Proof.
  intro n.
  simpl.
  reflexivity.
Qed.

Theorem plus_n_O : forall n : nat, plus n O = n.
Proof.
  intro n.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.
```

`induction` タクティックにより、自動的に帰納法の構造が生成されます。

### 等式の扱いと書き換え

等式は数学的証明において中心的な役割を果たします。Coq では、等式の性質を活用して証明を進めることができます。

**加法の結合律**：
```coq
Theorem plus_assoc : forall n m p : nat, plus (plus n m) p = plus n (plus m p).
Proof.
  intros n m p.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.
```

`rewrite` タクティックにより、等式を使って項を書き換えることができます。

**加法の交換律（より複雑な例）**：
```coq
Lemma plus_n_Sm : forall n m : nat, S (plus n m) = plus n (S m).
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem plus_comm : forall n m : nat, plus n m = plus m n.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - simpl. rewrite plus_n_O. reflexivity.
  - simpl. rewrite IHn'. rewrite plus_n_Sm. reflexivity.
Qed.
```

複雑な証明では、補題（Lemma）を先に証明して、メインの定理で使用します。

### リストに関する証明

リストは実用的なデータ構造であり、その性質を証明することで実際のプログラムの正しさを保証できます。

```coq
Fixpoint app (l1 l2 : list nat) : list nat :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.

Theorem app_assoc : forall l1 l2 l3 : list nat,
  app (app l1 l2) l3 = app l1 (app l2 l3).
Proof.
  intros l1 l2 l3.
  induction l1 as [| h1 t1 IHt1].
  - simpl. reflexivity.
  - simpl. rewrite IHt1. reflexivity.
Qed.

Fixpoint length (l : list nat) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Theorem app_length : forall l1 l2 : list nat,
  length (app l1 l2) = plus (length l1) (length l2).
Proof.
  intros l1 l2.
  induction l1 as [| h1 t1 IHt1].
  - simpl. reflexivity.
  - simpl. rewrite IHt1. reflexivity.
Qed.
```

### 高階関数の証明

高階関数（関数を引数として取る関数）の性質も証明できます。

```coq
Fixpoint map (f : nat -> nat) (l : list nat) : list nat :=
  match l with
  | nil => nil
  | h :: t => (f h) :: (map f t)
  end.

Theorem map_app : forall (f : nat -> nat) (l1 l2 : list nat),
  map f (app l1 l2) = app (map f l1) (map f l2).
Proof.
  intros f l1 l2.
  induction l1 as [| h1 t1 IHt1].
  - simpl. reflexivity.
  - simpl. rewrite IHt1. reflexivity.
Qed.

Theorem map_length : forall (f : nat -> nat) (l : list nat),
  length (map f l) = length l.
Proof.
  intros f l.
  induction l as [| h t IHt].
  - simpl. reflexivity.
  - simpl. rewrite IHt. reflexivity.
Qed.
```

### 証明の自動化

Coq では、定型的な証明を自動化するタクティックが豊富に用意されています。

**auto と eauto**：
```coq
Theorem trivial_example : forall P Q : Prop, P -> P.
Proof.
  auto.
Qed.

Theorem simple_transitivity : forall P Q R : Prop, 
  (P -> Q) -> (Q -> R) -> (P -> R).
Proof.
  eauto.
Qed.
```

**omega（算術の自動証明）**：
```coq
Require Import Omega.

Theorem arithmetic_example : forall n m : nat, 
  n <= m -> n <= m + 1.
Proof.
  intros n m H.
  omega.
Qed.
```

**tauto（命題論理の自動証明）**：
```coq
Theorem propositional_example : forall P Q R : Prop,
  (P /\ Q) -> (P \/ R).
Proof.
  tauto.
Qed.
```

### 型クラスと証明の構造化

型クラス（Type Classes）を使うことで、証明を構造化し、再利用性を高めることができます。

```coq
Class Monoid (A : Type) := {
  id : A;
  op : A -> A -> A;
  left_id : forall a, op id a = a;
  right_id : forall a, op a id = a;
  assoc : forall a b c, op (op a b) c = op a (op b c)
}.

Instance nat_plus_monoid : Monoid nat := {
  id := 0;
  op := plus;
  left_id := plus_O_n;
  right_id := plus_n_O;
  assoc := plus_assoc
}.
```

### 証明項の抽出

Coq の重要な特徴の一つは、証明から実際の計算プログラムを抽出できることです。

```coq
Fixpoint div2 (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => S (div2 n')
  end.

Theorem div2_correct : forall n : nat, 
  div2 n <= n /\ n < 2 * div2 n + 2.
Proof.
  intro n.
  induction n as [| n' [IH1 IH2]].
  - split; simpl; auto with arith.
  - destruct n' as [| n''].
    + split; simpl; auto with arith.
    + split; simpl in *; omega.
Qed.

(* この証明から、実際に使用可能な除算アルゴリズムが抽出される *)
Extraction div2.
```

### 実践的な証明戦略

効果的な証明を構築するためのガイドライン：

**1. 段階的構築**：
- 簡単な補題から始める
- 複雑な定理は小さな部分に分割
- 各ステップで証明の正しさを確認

**2. 適切な帰納法の選択**：
- データ構造に応じた帰納法を選択
- 強帰納法や相互帰納法の活用
- well-founded帰納法の利用

**3. 証明の可読性**：
- 意味のある補題名の選択
- 証明の意図を説明するコメント
- 論理的な構造の明確化

**4. 自動化の適切な使用**：
- 定型的な部分は自動化タクティックを使用
- 重要な洞察が必要な部分は手動で証明
- デバッグしやすい証明の構築

### エラーの診断と修正

Coq での証明では、型エラーや証明の穴を適切に診断することが重要です。

```coq
Theorem example_with_error : forall n : nat, n + 0 = n.
Proof.
  intro n.
  (* simpl. *) (* これをコメントアウトすると型エラー *)
  reflexivity.
Qed.
```

エラーメッセージを理解し、適切な修正を行うスキルが、効率的な証明開発には不可欠です。

証明支援系の実践を通じて、数学的推論の厳密性と計算的思考を両立させることができます。これにより、理論的な正しさと実用的な価値を持つプログラムを開発できるようになります。

## 9.5 証明の戦略と技法

### 証明戦略の体系的アプローチ

証明支援系での証明は、単なるタクティックの適用ではありません。効果的な証明には、明確な戦略と体系的なアプローチが必要です。熟練した証明者は、問題の構造を理解し、適切な手法を選択し、段階的に解決に向かう技術を持っています。

証明戦略は、パズル解法や問題解決の一般的な手法と共通点を持ちます。しかし、数学的厳密性の要求により、より体系的で論理的なアプローチが必要になります。

### 前進推論と後退推論

証明には二つの基本的な方向性があります：

**前進推論（Forward Reasoning）**：
仮定から出発して、目標に向かって進む方法です。

```coq
Theorem forward_example : forall n m : nat, 
  n <= m -> m <= n -> n = m.
Proof.
  intros n m H1 H2.
  (* 前進推論：仮定から事実を導出 *)
  assert (H3 : n <= m /\ m <= n). { split; [exact H1 | exact H2]. }
  (* antisymmetry を適用 *)
  apply Nat.le_antisymm; [exact H1 | exact H2].
Qed.
```

**後退推論（Backward Reasoning）**：
目標から出発して、それを満たすために必要な条件を遡る方法です。

```coq
Theorem backward_example : forall n : nat, n + 0 = n.
Proof.
  intro n.
  (* 後退推論：目標を満たすために何が必要かを考える *)
  induction n as [| n' IHn'].
  - (* ベースケース：0 + 0 = 0 を示す *)
    simpl. reflexivity.
  - (* 帰納ステップ：S n' + 0 = S n' を示す *)
    simpl. rewrite IHn'. reflexivity.
Qed.
```

実際の証明では、前進推論と後退推論を組み合わせて使用することが多くあります。

### 帰納法の選択と適用

帰納法は数学的証明の基本的な手法ですが、適切な帰納の変数と構造を選択することが重要です。

**構造帰納法**：
データ構造の定義に従った最も基本的な帰納法です。

```coq
Fixpoint reverse (l : list nat) : list nat :=
  match l with
  | nil => nil
  | h :: t => reverse t ++ [h]
  end.

Theorem reverse_involutive : forall l : list nat, 
  reverse (reverse l) = l.
Proof.
  intro l.
  induction l as [| h t IHt].
  - simpl. reflexivity.
  - simpl. rewrite reverse_app. rewrite IHt. simpl. reflexivity.
Qed.
```

**強帰納法**：
より小さなすべての要素についての仮定を使える帰納法です。

```coq
Require Import Arith.

Theorem strong_induction_example : forall n : nat, 
  n >= 2 -> exists a b : nat, a >= 2 /\ b >= 2 /\ n = a * b \/ prime n.
Proof.
  intro n.
  pattern n. apply strong_nat_ind.
  (* 強帰納法による証明 *)
Admitted. (* 実際の証明は複雑なので省略 *)
```

**相互帰納法**：
相互に定義されたデータ構造や関数に対する帰納法です。

```coq
Fixpoint even (n : nat) : bool :=
  match n with
  | O => true
  | S n' => odd n'
  end
with odd (n : nat) : bool :=
  match n with
  | O => false
  | S n' => even n'
  end.

Theorem even_odd_exclusive : forall n : nat, 
  even n = true -> odd n = false.
Proof.
  intro n.
  functional induction (even n); simpl; auto.
  (* 相互帰納法による証明 *)
Qed.
```

### 場合分けと網羅性

複雑な問題では、適切な場合分けが証明の鍵となります。

**論理的場合分け**：
```coq
Theorem case_analysis_example : forall n : nat, 
  n = 0 \/ n > 0.
Proof.
  intro n.
  destruct n as [| n'].
  - left. reflexivity.
  - right. apply Nat.lt_0_succ.
Qed.
```

**データ構造による場合分け**：
```coq
Theorem list_empty_or_not : forall (A : Type) (l : list A),
  l = nil \/ exists h t, l = h :: t.
Proof.
  intros A l.
  destruct l as [| h t].
  - left. reflexivity.
  - right. exists h, t. reflexivity.
Qed.
```

### 補題の戦略的使用

複雑な証明では、適切な補題を設定することで、証明を簡潔にできます。

**一般化補題**：
```coq
Lemma app_nil_r : forall (A : Type) (l : list A), 
  l ++ nil = l.
Proof.
  intros A l.
  induction l as [| h t IHt].
  - simpl. reflexivity.
  - simpl. rewrite IHt. reflexivity.
Qed.

(* この補題を使用したメインの定理 *)
Theorem reverse_app : forall (A : Type) (l1 l2 : list A),
  reverse (l1 ++ l2) = reverse l2 ++ reverse l1.
Proof.
  intros A l1 l2.
  induction l1 as [| h t IHt].
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. rewrite IHt. rewrite app_assoc. reflexivity.
Qed.
```

**技術的補題**：
```coq
Lemma S_injective : forall n m : nat, S n = S m -> n = m.
Proof.
  intros n m H.
  injection H. intro H'. exact H'.
Qed.

Lemma nat_case : forall n : nat, n = 0 \/ exists k, n = S k.
Proof.
  intro n.
  destruct n as [| k].
  - left. reflexivity.
  - right. exists k. reflexivity.
Qed.
```

### 反射と計算の活用

Coq では、計算による簡約を活用して証明を簡潔にできます。

**計算による証明**：
```coq
Example computation_proof : 2 + 3 = 5.
Proof.
  reflexivity. (* 計算により自動的に証明される *)
Qed.

Example boolean_computation : 
  let b1 := true in
  let b2 := false in
  b1 && b2 = false.
Proof.
  simpl. reflexivity.
Qed.
```

**反射的証明（Proof by Reflection）**：
```coq
Fixpoint beq_nat (n m : nat) : bool :=
  match n, m with
  | O, O => true
  | S n', S m' => beq_nat n' m'
  | _, _ => false
  end.

Lemma beq_nat_refl : forall n : nat, beq_nat n n = true.
Proof.
  intro n.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. exact IHn'.
Qed.

(* 反射を使った証明 *)
Theorem reflection_example : forall n m : nat,
  beq_nat n m = true -> n = m.
Proof.
  (* 反射的証明による効率的な証明 *)
Admitted. (* 詳細は省略 *)
```

### 抽象化と一般化

具体的な問題から一般的な原理を抽出することで、再利用可能な証明を構築できます。

**パラメータ化された証明**：
```coq
Section Parametric_Proofs.
  Variable A : Type.
  Variable R : A -> A -> Prop.
  Hypothesis R_refl : forall x, R x x.
  Hypothesis R_sym : forall x y, R x y -> R y x.
  Hypothesis R_trans : forall x y z, R x y -> R y z -> R x z.

  Theorem equivalence_relation_property : forall x y z : A,
    R x y -> R y z -> R z x.
  Proof.
    intros x y z Hxy Hyz.
    apply R_sym.
    apply R_trans with y; [exact Hyz | exact Hxy].
  Qed.
End Parametric_Proofs.
```

### エラー回復と証明のデバッグ

証明の構築中にエラーが発生した場合の対処法：

**型エラーの診断**：
```coq
Theorem type_error_example : forall n : nat, n + 0 = n.
Proof.
  intro n.
  (* Check (n + 0). (* 型を確認 *) *)
  (* Check (@eq nat). (* 等式の型を確認 *) *)
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. 
    (* Show Proof. (* 現在の証明項を表示 *) *)
    rewrite IHn'. reflexivity.
Qed.
```

**証明状態の確認**：
```coq
Theorem debugging_example : forall n m : nat, n <= m -> m <= n -> n = m.
Proof.
  intros n m H1 H2.
  (* Show. (* 現在の証明状態を表示 *) *)
  assert (H3 : n <= m /\ m <= n). { split; assumption. }
  (* Show. (* アサート後の状態を確認 *) *)
  apply Nat.le_antisymm; assumption.
Qed.
```

### 証明の最適化とリファクタリング

効率的で読みやすい証明にするための技法：

**タクティックの組み合わせ**：
```coq
Theorem optimized_proof : forall n : nat, n + 0 = n.
Proof.
  intro n; induction n as [| n' IHn']; simpl; [reflexivity | rewrite IHn'; reflexivity].
Qed.

(* より読みやすい版 *)
Theorem readable_proof : forall n : nat, n + 0 = n.
Proof.
  intro n.
  induction n as [| n' IHn'].
  - (* Base case *) 
    simpl. reflexivity.
  - (* Inductive step *)
    simpl. rewrite IHn'. reflexivity.
Qed.
```

**自動化の活用**：
```coq
Theorem automated_proof : forall n m p : nat, 
  n + (m + p) = (n + m) + p.
Proof.
  induction n; simpl; [reflexivity | intro; rewrite IHn; reflexivity].
Qed.
```

これらの戦略と技法を組み合わせることで、複雑な数学的性質でも体系的に証明できるようになります。重要なのは、問題の構造を理解し、適切な手法を選択することです。

## 9.6 実用的プログラム検証：ツールと方法論

### 産業界での定理証明の現実

定理証明は、学術的な研究から実用的な技術へと進化しています。航空宇宙、自動車、金融、セキュリティといった安全性やセキュリティが重要な分野で、実際のソフトウェアシステムの検証に使用されています。

しかし、実用的なプログラム検証は、理論的な数学定理の証明とは異なる挑戦があります。実際のプログラムは複雑で、ハードウェアの詳細、並行性、入出力、例外処理など、多くの実装詳細を含んでいます。

### CompCert：検証されたCコンパイラ

CompCertは、定理証明を用いて完全に検証されたCコンパイラです。このプロジェクトは、実用的なプログラム検証の可能性を示す画期的な成果です。

**CompCertの特徴**：
- Cのサブセットから複数のアセンブリ言語への変換
- コンパイル過程の各段階の正しさをCoqで証明
- 実際の産業用途での使用実績

```coq
(* CompCertでの検証例（簡略版） *)
Theorem compile_correctness : forall p : C_program,
  well_typed p ->
  forall t : execution_trace,
    C_semantics p t <-> Assembly_semantics (compile p) t.
```

この定理は、「正しくコンパイルされたプログラムは、元のCプログラムと同じ動作をする」ことを保証しています。

### seL4：検証されたマイクロカーネル

seL4は、機能的正しさが完全に証明されたマイクロカーネルです。この プロジェクトは、低レベルシステムソフトウェアの検証可能性を実証しました。

**seL4の検証内容**：
```isabelle
(* Isabelle/HOLでの検証例 *)
theorem kernel_correctness:
  "system_call_interface ⊆ abstract_specification"

theorem security_properties:
  "∀ p1 p2. isolation(p1, p2) → ¬(p1 can_access data_of p2)"
```

### プログラム検証の階層

実用的なプログラム検証では、複数の抽象化レベルでの検証が必要です。

**1. アルゴリズムレベル**：
```coq
Fixpoint quicksort (l : list nat) : list nat :=
  match l with
  | nil => nil
  | pivot :: rest =>
    let smaller := filter (fun x => x <=? pivot) rest in
    let larger := filter (fun x => pivot <? x) rest in
    quicksort smaller ++ [pivot] ++ quicksort larger
  end.

Theorem quicksort_correct : forall l : list nat,
  Permutation l (quicksort l) /\ sorted (quicksort l).
```

**2. データ構造レベル**：
```coq
Definition binary_search_tree_invariant (t : tree nat) : Prop :=
  forall x left right,
    In_tree x left -> In_tree x right ->
    t = Node x left right ->
    (forall y, In_tree y left -> y <= x) /\
    (forall y, In_tree y right -> x <= y).
```

**3. メモリレベル**：
```c
/*@ requires \valid(array + (0..n-1));
  @ ensures \forall integer i; 0 <= i < n ==>
  @   \exists integer j; 0 <= j < n && array[i] == \old(array[j]);
  @ ensures sorted(array, 0, n-1);
  */
void sort_array(int *array, int n);
```

### ACSL：C言語の形式仕様

ACSL（ANSI/ISO C Specification Language）は、C言語プログラムに形式的仕様を付加するための言語です。

**基本的な仕様記述**：
```c
/*@ requires n >= 0;
  @ requires \valid(a + (0..n-1));
  @ ensures \result == \sum(0, n-1, \lambda integer i; a[i]);
  */
int sum_array(int a[], int n) {
  int result = 0;
  /*@ loop invariant 0 <= i <= n;
    @ loop invariant result == \sum(0, i-1, \lambda integer k; a[k]);
    @ loop assigns i, result;
    @ loop variant n - i;
    */
  for (int i = 0; i < n; i++) {
    result += a[i];
  }
  return result;
}
```

### Dafny：検証指向プログラミング言語

Dafnyは、プログラムの正しさの証明を設計時から考慮したプログラミング言語です。

```dafny
method BinarySearch(a: array<int>, key: int) returns (index: int)
  requires a.Length > 0
  requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures 0 <= index ==> index < a.Length && a[index] == key
  ensures index < 0 ==> forall i :: 0 <= i < a.Length ==> a[i] != key
{
  var low := 0;
  var high := a.Length;
  
  while low < high
    invariant 0 <= low <= high <= a.Length
    invariant forall i :: 0 <= i < low ==> a[i] < key
    invariant forall i :: high <= i < a.Length ==> a[i] > key
  {
    var mid := (low + high) / 2;
    if a[mid] < key {
      low := mid + 1;
    } else if a[mid] > key {
      high := mid;
    } else {
      return mid;
    }
  }
  
  return -1;
}
```

### SPARK：Adaの検証サブセット

SPARKは、Adaのサブセットに契約ベースの仕様を追加した言語です。航空宇宙産業で広く使用されています。

```ada
procedure Increment (X : in out Integer)
  with Pre  => X < Integer'Last,
       Post => X = X'Old + 1;

procedure Increment (X : in out Integer) is
begin
   X := X + 1;
end Increment;
```

### 実用検証のワークフロー

実際のプロジェクトでの検証ワークフロー：

**1. 要求分析と仕様記述**：
```
非形式的要求 → 形式的仕様 → 検証可能な性質
```

**2. 段階的実装と検証**：
```
抽象アルゴリズム → 具体的実装 → 最適化
      ↓              ↓           ↓
   証明1          証明2       証明3
```

**3. 統合と全体検証**：
```
コンポーネント検証 → システム統合 → エンドツーエンド検証
```

### 自動化ツールとの統合

実用的な検証では、自動化ツールの活用が重要です。

**SMTソルバーの活用**：
```dafny
// Dafnyは自動的にZ3 SMTソルバーを使用
lemma ArithmeticProperty(x: int, y: int)
  ensures x + y == y + x
{
  // 証明は自動的に完了
}
```

**静的解析ツールとの連携**：
```c
// PolySpaceによる実行時エラー検出と
// ACSlによる関数契約の組み合わせ
/*@ requires \valid(ptr);
  @ ensures \result != NULL;
  */
char* safe_malloc_wrapper(size_t size);
```

### 性能とのトレードオフ

実用的な検証では、検証の完全性と開発効率のバランスが重要です。

**段階的検証アプローチ**：
1. **クリティカル部分の完全検証**：安全性に直結する部分
2. **重要部分の部分検証**：主要な機能の正しさ
3. **一般部分の軽量検証**：テストと静的解析の組み合わせ

**検証コストの見積もり**：
```
検証工数 ≈ 実装工数 × (2-10)
ただし、検証の複雑さと要求水準に大きく依存
```

### 組織的な導入戦略

実用的なプログラム検証の組織への導入：

**段階的導入**：
1. **パイロットプロジェクト**：小規模で検証の価値を実証
2. **ツールと手法の標準化**：組織での共通手法の確立
3. **教育と訓練**：チーム全体の能力向上
4. **継続的改善**：フィードバックに基づく手法の改善

**成功要因**：
- 経営陣のコミットメント
- 適切な問題領域の選択
- 段階的なスキル構築
- 外部専門家との協力

### 将来の展望

プログラム検証技術の発展方向：

**AI支援検証**：
機械学習を活用した証明の自動生成や、証明戦略の推薦システム

**クラウドベース検証**：
大規模な検証タスクをクラウドで分散実行

**継続的検証**：
CI/CDパイプラインに統合された自動検証

実用的プログラム検証は、理論と実践の橋渡しにより、より安全で信頼性の高いソフトウェアシステムの開発を可能にします。適切なツールの選択と段階的な導入により、実際のプロジェクトでも活用できる技術として成熟しつつあります。

---

## 章末課題

**AI利用時の提出ルール（共通）**
- AIの出力は提案として扱い、合否は検証器で判定する
- 提出物: 使用プロンプト / 生成仕様・不変条件 / 検証コマンドとログ（seed/深さ/スコープ） / 反例が出た場合の修正履歴
- 詳細なテンプレは付録D・付録Fを参照する


### 基礎理解演習1：論理推論の形式化

以下の日常的な推論を自然演繹の推論規則で形式化してください：

**推論1**: 「雨が降っているならば地面が濡れる。雨が降っている。したがって地面が濡れている。」

**推論2**: 「すべての鳥は飛ぶことができる。ペンギンは鳥である。したがってペンギンは飛ぶことができる。」（この推論の問題点も指摘してください）

**推論3**: 「AまたはBである。Aでない。したがってBである。」

各推論について：
1. 命題の形式化（記号による表現）
2. 推論規則の適用順序
3. 証明木の構築
4. 推論の妥当性の評価

### 基礎理解演習2：Coqでの基本証明

Coqを使用して以下の基本的な論理性質を証明してください：

```coq
(* 論理演算子の基本性質 *)
Theorem and_commutative : forall P Q : Prop, P /\ Q -> Q /\ P.

Theorem or_commutative : forall P Q : Prop, P \/ Q -> Q \/ P.

Theorem implication_chain : forall P Q R : Prop, 
  (P -> Q) -> (Q -> R) -> (P -> R).

(* 量詞の性質 *)
Theorem forall_and_dist : forall (A : Type) (P Q : A -> Prop),
  (forall x, P x /\ Q x) -> (forall x, P x) /\ (forall x, Q x).

Theorem exists_or_dist : forall (A : Type) (P Q : A -> Prop),
  (exists x, P x \/ Q x) -> (exists x, P x) \/ (exists x, Q x).
```

### 実践演習1：データ構造の証明

リスト操作に関する重要な性質をCoqで証明してください：

```coq
(* リストの定義と基本操作 *)
Fixpoint append (l1 l2 : list nat) : list nat :=
  match l1 with
  | nil => l2
  | h :: t => h :: append t l2
  end.

Fixpoint reverse (l : list nat) : list nat :=
  match l with
  | nil => nil
  | h :: t => append (reverse t) [h]
  end.

(* 証明すべき性質 *)
Theorem append_assoc : forall l1 l2 l3 : list nat,
  append (append l1 l2) l3 = append l1 (append l2 l3).

Theorem reverse_append : forall l1 l2 : list nat,
  reverse (append l1 l2) = append (reverse l2) (reverse l1).

Theorem reverse_involutive : forall l : list nat,
  reverse (reverse l) = l.

(* より高度な性質 *)
Fixpoint length (l : list nat) : nat :=
  match l with
  | nil => 0
  | h :: t => S (length t)
  end.

Theorem length_append : forall l1 l2 : list nat,
  length (append l1 l2) = length l1 + length l2.
```

### 実践演習2：アルゴリズムの正しさ証明

ソートアルゴリズムの正しさをCoqで証明してください：

```coq
(* 挿入ソートの実装 *)
Fixpoint insert (x : nat) (l : list nat) : list nat :=
  match l with
  | nil => [x]
  | h :: t => if x <=? h then x :: l else h :: insert x t
  end.

Fixpoint insertion_sort (l : list nat) : list nat :=
  match l with
  | nil => nil
  | h :: t => insert h (insertion_sort t)
  end.

(* ソート済みの定義 *)
Fixpoint sorted (l : list nat) : Prop :=
  match l with
  | nil => True
  | [x] => True
  | x :: y :: rest => x <= y /\ sorted (y :: rest)
  end.

(* 証明すべき性質 *)
Theorem insert_sorted : forall x l,
  sorted l -> sorted (insert x l).

Theorem insertion_sort_sorted : forall l,
  sorted (insertion_sort l).

(* 順列の定義と証明 *)
Inductive Permutation : list nat -> list nat -> Prop :=
| perm_nil : Permutation [] []
| perm_skip : forall x l l', Permutation l l' -> 
    Permutation (x::l) (x::l')
| perm_swap : forall x y l, 
    Permutation (y::x::l) (x::y::l)
| perm_trans : forall l l' l'', 
    Permutation l l' -> Permutation l' l'' -> 
    Permutation l l''.

Theorem insertion_sort_permutation : forall l,
  Permutation l (insertion_sort l).
```

### 発展演習：実用的検証プロジェクト

より実用的なシステムの検証を行ってください。以下のいずれかを選択：

#### オプション1：簡単な暗号システム

```coq
(* シーザー暗号の実装と証明 *)
Definition caesar_encrypt (shift : nat) (c : ascii) : ascii :=
  (* 実装を完成させる *).

Definition caesar_decrypt (shift : nat) (c : ascii) : ascii :=
  (* 実装を完成させる *).

(* 証明すべき性質 *)
Theorem caesar_decrypt_encrypt : forall shift c,
  caesar_decrypt shift (caesar_encrypt shift c) = c.

Theorem caesar_encrypt_decrypt : forall shift c,
  caesar_encrypt shift (caesar_decrypt shift c) = c.
```

#### オプション2：バランス二分木

```coq
(* AVL木の実装と不変条件の証明 *)
Inductive tree : Type :=
| Leaf : tree
| Node : nat -> tree -> tree -> tree.

Fixpoint height (t : tree) : nat :=
  (* 高さの計算 *).

Definition balanced (t : tree) : Prop :=
  (* バランス条件の定義 *).

Fixpoint insert (x : nat) (t : tree) : tree :=
  (* 挿入操作の実装 *).

(* 証明すべき性質 *)
Theorem insert_preserves_balance : forall x t,
  balanced t -> balanced (insert x t).

Theorem insert_preserves_bst : forall x t,
  is_bst t -> is_bst (insert x t).
```

#### オプション3：並行データ構造

```coq
(* ロックフリースタックの仕様と正しさ *)
(* SPARKまたはDafnyでの実装も可 *)

Definition atomic_compare_and_swap (old new : nat) (location : nat) : bool :=
  (* CAS操作の抽象化 *).

(* スタック操作の仕様 *)
Definition push_spec (x : nat) (pre_state post_state : stack_state) : Prop :=
  (* push操作の事前条件と事後条件 *).

Definition pop_spec (pre_state post_state : stack_state) (result : option nat) : Prop :=
  (* pop操作の事前条件と事後条件 *).

(* 証明すべき性質 *)
Theorem push_pop_correctness : forall x s,
  (* pushしてからpopすると元の値が取得できる *).

Theorem linearizability : forall operations,
  (* 並行実行が何らかの逐次実行と等価 *).
```

### 評価基準

各演習について以下の観点で評価してください：

1. **正しさ**: 証明が論理的に正しく完成している
2. **理解度**: 使用した推論規則や戦略の理解
3. **効率性**: 証明の簡潔さと可読性
4. **実用性**: 実際の問題への応用可能性

これらの演習を通じて、定理証明の理論的基礎と実践的応用の両方を身につけ、次章でのプログラム検証への準備を整えてください。特に発展演習では、実際のソフトウェア開発で直面する問題に対する形式的アプローチを体験することが重要です。