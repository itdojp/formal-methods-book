---
layout: book
title: "第5章　状態ベース仕様記述 - Z記法の基礎"
chapter: chapter05
order: 5
---

# 第5章　状態ベース仕様記述 - Z記法の基礎

ミニ要約：
- 状態/操作スキーマで事前/事後と不変を統合
- 合成で性質を保全し実装整合を図る
- 図5-1と第10章の往復で検証可能性を設計

## 5.1 Z記法の世界：状態とスキーマの思想

### オックスフォードが生んだ厳密性の文化

Z記法は、1970年代後半から80年代にかけて、オックスフォード大学コンピューティング研究所で開発されました。その背景には、ソフトウェアシステムがますます複雑化し、従来の非形式的な手法では品質を保証できないという深刻な認識がありました。

Z記法の開発者たちは、数学の厳密性をソフトウェア仕様に持ち込むことで、この問題を解決しようと考えました。しかし、単に数学記号を使うだけではありません。実用的なソフトウェア開発で使える形で、数学的厳密性を提供することが目標でした。

その結果生まれたZ記法は、「読みやすい数学」とも呼べる特徴を持っています。複雑な数学的概念を、構造化された形で表現することで、数学者でない実務者でも理解し、活用できる記法を実現しました。

### 状態中心の世界観

Z記法の最も重要な特徴は、「状態」を中心とした世界観です。システムを「状態」と「状態を変化させる操作」の組み合わせとして捉えます。この視点は、データベース設計や状態機械の考え方に近いものです。

状態中心の思考では、まずシステムが持つべき情報（状態変数）を明確にし、次にその情報に対する制約（不変条件）を定義し、最後に状態を変化させる操作を記述します。この順序は偶然ではありません。状態の理解なしに操作の正しさを論じることはできないからです。
（プログラム側の検証との往復関係は第10章参照）

例えば、図書館システムを考えてみましょう。従来のオブジェクト指向アプローチでは「本オブジェクト」「利用者オブジェクト」から考え始めるかもしれません。しかしZ記法では、「図書館の状態とは何か」から考え始めます。どの本が所蔵されているか、どの本が貸し出されているか、誰がどの本を借りているか。これらの情報とその関係が、システムの状態を構成します。

### スキーマという構造化の智慧

Z記法の最も革新的な概念の一つが「スキーマ（schema）」です。スキーマは、関連する情報をひとまとまりとして構造化するための仕組みです。これは、単なる記法上の工夫ではなく、複雑性を管理するための深い智慧を表しています。

![図5-1: Z記法のスキーマ構造と状態ベース仕様記述](../../assets/images/diagrams/z-notation-schema-structure.svg)
（読み取りポイント：状態・操作スキーマで不変と更新を分離し整合）

（読み取りポイント：図5-1参照）
- 状態スキーマ: 変数宣言と不変条件を同居させることで一貫性を担保
- 操作スキーマ: 事前/事後状態（'）と事前条件/事後条件の分離
- 合成: 複合操作はスキーマ合成で性質を維持

### 章末課題（抜粋）

解答の骨子・採点観点は[付録D]({{ '/appendices/appendix-d/' | relative_url }})を参照。

1. 状態スキーマに不変条件を2つ追加した場合、操作スキーマに与える影響（事前/事後条件の観点）を箇条書きで述べよ。
2. スキーマ合成で不変が破れる典型的なケースを1つ挙げ、修正方針を50–80字で述べよ。

＜解答の方向性（骨子）＞
- 問1: 事前条件の強化/事後条件の充足性の確認、'変数の整合が焦点。
- 問2: 暗黙の前提の漏れ（境界/整合）→前提追加や操作分割で保全。

人間の認知能力には限界があります。心理学の研究によると、人間が同時に把握できる概念の数は7±2個程度です。しかし、現実のソフトウェアシステムには、数十から数百の要素が存在します。スキーマは、この認知限界を克服するための抽象化メカニズムなのです。

スキーマにより、関連する変数と制約をグループ化し、一つの概念単位として扱えます。これにより、複雑なシステムを理解可能な単位に分解できます。また、スキーマは再利用可能で、類似した構造を持つ部分で共通化できます。

### 数学的基盤の実用化

Z記法は、集合論、論理学、関数論といった確立された数学的基盤の上に構築されています。しかし、これらの概念をそのまま使うのではなく、ソフトウェア仕様に適した形で実用化しています。

例えば、関数の概念は数学では抽象的ですが、Z記法では「部分関数」「全関数」「単射」「全射」といった具体的な分類を提供し、それぞれがソフトウェアシステムのどのような側面を表現するかを明確にしています。

また、Z記法は「型」の概念を重視します。これは、プログラミング言語の型システムに近いものですが、より表現力が豊富です。型により、記述の誤りを早期に発見でき、仕様の理解も容易になります。

### 産業界での成功と学び

Z記法は、学術的な研究だけでなく、産業界でも多くの成功事例を持っています。特に、安全性が重要なシステム（交通制御、航空宇宙、原子力など）での活用が顕著です。

これらの成功事例から得られた重要な学びの一つは、「段階的適用」の重要性です。システム全体をいきなりZ記法で記述するのではなく、最も重要な部分から始めて、段階的に範囲を拡大していく方法が効果的であることが分かりました。

また、「チーム内での共通理解」がZ記法の成功に不可欠であることも明らかになりました。記法自体の習得だけでなく、その記法を使ってコミュニケーションを行う文化の構築が重要なのです。

## 5.2 数学的記法の体系：集合と論理の実用化

### 記号という共通言語の力

数学的記法の最大の価値は、「解釈の一意性」にあります。自然言語では「大きい」「小さい」「多い」「少ない」といった表現が曖昧性を持ちますが、数学記号 ≤、≥、∈、⊆ などは世界中どこでも同じ意味を持ちます。

Z記法は、この数学記号の力を活用しながら、ソフトウェア仕様記述に特化した記法体系を構築しています。重要なのは、記号を覚えることではなく、その記号が表現する概念を理解することです。

### 基本型と構成型

Z記法では、まず基本的な型を定義し、それらを組み合わせてより複雑な型を構成します。

**基本型の例：**
```z
[Person, BookID, Date]
```

角括弧で囲まれた名前は「基本型」を表します。これは、それ以上分解しない基本的な要素の集合を表現します。

**構成型の例：**
```z
Name == seq Char
Status ::= available | borrowed | reserved
Address == [street: seq Char; city: seq Char; zipcode: Nat]
```

構成型は、基本型から新しい型を作る方法を提供します。シーケンス（seq）、自由型（::=）、レコード型（[]）などの構成子があります。

### 集合演算の実用的活用

集合論の演算子は、ソフトウェアの仕様記述において自然で強力な表現力を提供します。

**基本的な集合演算：**
- ∈ (membership): 要素の所属関係
- ⊆ (subset): 部分集合関係  
- ∪ (union): 和集合
- ∩ (intersection): 積集合
- \ (difference): 差集合
- ℙ (power set): 冪集合

**実用例：図書館の蔵書管理**
```z
availableBooks == allBooks \ borrowedBooks
overdueBooks == {b: borrowedBooks | dueDate(b) < today}
popularBooks == {b: allBooks | #borrowers(b) > threshold}
```

これらの表現は、自然言語よりもはるかに正確で、プログラムコードよりもはるかに理解しやすい仕様を提供します。

### 関係と関数の階層

Z記法では、関係と関数を明確に区別し、それぞれの特性に応じた記法を提供します。

**関係の種類：**
- ↔ (relation): 一般的な関係
- → (function): 部分関数
- ⤖ (partial function): 明示的な部分関数
- ↣ (total function): 全関数  
- ⤏ (injection): 単射
- ↠ (surjection): 全射
- ⤖ (bijection): 全単射

**実用例：学生の履修管理**
```z
enrollment: Student ↔ Course           // 多対多の関係
advisor: Student ⤏ Teacher             // 各学生に最大1人の指導教員
teaches: Teacher ↣ ℙ Course           // 各教師は複数科目を担当
studentID: Student ⤖ StudentNumber    // 学生IDは一意
```

### 述語論理の実践的応用

述語論理の量詞（∀, ∃）は、ソフトウェアの仕様記述において非常に重要な役割を果たします。

**全称量詞の活用：**
```z
∀ s: Student • #(s.courses) ≤ maxCourses
// すべての学生の履修科目数は上限以下

∀ b: BorrowedBook • b.dueDate ≥ b.borrowDate + 14
// すべての貸出図書の返却期限は借用日から14日以上後
```

**存在量詞の活用：**
```z
∃ a: Admin • a.isActive = true
// 少なくとも1人のアクティブな管理者が存在

∃! p: Person • p.email = targetEmail
// 指定されたメールアドレスを持つ人がちょうど1人存在
```

### スキーマ内での記法統合

Z記法の真価は、これらの数学的概念をスキーマ内で統合することで発揮されます。

```z
LibrarySystem
├─ books: ℙ Book
├─ members: ℙ Member  
├─ loans: Member ⤏ ℙ Book
├─ dueDate: Book ⤏ Date
├─────────────────────────
├─ dom loans ⊆ members
├─ ran loans ⊆ books
├─ ∀ m: Member • #(loans(m)) ≤ maxLoans
└─ ∀ b: ran loans • dueDate(b) > today
```

このスキーマは、図書館システムの状態を数学的に厳密に記述していますが、同時に直感的に理解できる構造を持っています。

### 記法の読み方と発音

Z記法を実践で活用するには、記号を正しく読める必要があります。これは、チーム内でのコミュニケーションにおいて重要です。

**主要記号の読み方：**
- x ∈ S: "x belongs to S" または "x is in S"
- A ⊆ B: "A is a subset of B"
- f: X → Y: "f is a function from X to Y"  
- ∀ x: X • P(x): "for all x in X, P of x"
- ∃ x: X • P(x): "there exists x in X such that P of x"

正確な読み方を習得することで、Z記法の仕様を口頭で議論でき、チーム内での理解共有が促進されます。

## 5.3 スキーマによる状態の記述

### 状態の構造化という根本思想

複雑なシステムの状態を人間が理解するためには、適切な構造化が不可欠です。Z記法のスキーマは、この構造化のための強力なメカニズムを提供します。単に変数をグループ化するだけでなく、関連する制約も一緒に管理することで、状態の整合性を保証します。

スキーマの構造化により、「このシステムの有効な状態とは何か」という根本的な問題に対して、数学的に厳密な答えを提供できます。これは、単なる記述技法を超えて、システム設計の質を向上させる概念的なツールなのです。

### 基本的なスキーマの構造

Z記法のスキーマは、宣言部と制約部から構成されます。宣言部では状態変数とその型を定義し、制約部では変数間の関係と制約を記述します。

```z
┌─ BankAccount ─────────────────────┐
│ accountNumber: AccountID          │
│ balance: ℕ                        │
│ owner: Person                     │
│ isActive: 𝔹                       │
├───────────────────────────────────┤
│ balance ≤ creditLimit             │
│ isActive ⇒ owner ∈ validCustomers │
└───────────────────────────────────┘
```

この表記法では、水平線の上が宣言部、下が制約部です。制約部は、常に満たされるべき不変条件を記述します。

### 複合状態の表現

実際のシステムでは、複数のエンティティが相互に関連する複合的な状態を扱います。Z記法では、これを自然に表現できます。

```z
┌─ Library ─────────────────────────┐
│ books: ℙ Book                     │
│ members: ℙ Member                 │
│ catalogue: Book ⤖ BookInfo        │
│ loans: Member ⇀ ℙ Book            │
│ reservations: Member ⇀ ℙ Book     │
├───────────────────────────────────┤
│ dom catalogue = books             │
│ dom loans ⊆ members               │
│ ran loans ⊆ books                 │
│ ∀ m: Member • #(loans(m)) ≤ 5     │
│ loans ∩ reservations = ∅          │
└───────────────────────────────────┘
```

このスキーマは、図書館システムの複雑な状態構造を表現しています。各制約は、システムの整合性を保証する重要な条件です。

### 階層的スキーマ設計

大規模システムでは、スキーマを階層的に組織化することが重要です。下位レベルのスキーマを組み合わせて、上位レベルのスキーマを構築します。

```z
┌─ PersonalInfo ───────────────────┐
│ name: Name                       │
│ address: Address                 │
│ phoneNumber: PhoneNumber         │
├─────────────────────────────────┤
│ name ≠ ""                       │
│ isValidPhone(phoneNumber)        │
└─────────────────────────────────┘

┌─ BankingInfo ────────────────────┐
│ accountNumbers: ℙ AccountID      │
│ creditRating: CreditRating       │
│ lastTransaction: Date            │
├─────────────────────────────────┤
│ #accountNumbers ≥ 1             │
│ creditRating ∈ {A, B, C, D, E}  │
└─────────────────────────────────┘

┌─ Customer ───────────────────────┐
│ PersonalInfo                     │
│ BankingInfo                      │
├─────────────────────────────────┤
│ lastTransaction ≤ today          │
└─────────────────────────────────┘
```

この階層化により、各レベルで適切な抽象化を維持しながら、全体の複雑性を管理できます。

### 状態不変条件の表現

状態不変条件は、システムの整合性を保証する最も重要な要素です。Z記法では、これを数学的に厳密に表現できます。

```z
┌─ OnlineStore ────────────────────┐
│ products: ℙ Product              │
│ inventory: Product → ℕ           │
│ orders: ℙ Order                  │
│ orderItems: Order → ℙ Product    │
│ reservedStock: Product → ℕ       │
├─────────────────────────────────┤
│ dom inventory = products         │
│ dom reservedStock = products     │
│ ∀ p: Product •                  │
│   reservedStock(p) ≤ inventory(p)│
│ ∀ o: orders; p: orderItems(o) •  │
│   p ∈ products                   │
└─────────────────────────────────┘
```

これらの不変条件は、どのような操作を行っても保持されるべき性質です。在庫の整合性、注文の妥当性など、ビジネスロジックの核心を表現しています。

### 条件付き状態の表現

システムの状態は、しばしば条件に依存します。Z記法では、条件付きの制約を自然に表現できます。

```z
┌─ FlightBookingSystem ────────────┐
│ flights: ℙ Flight                │
│ bookings: ℙ Booking              │
│ passengers: Booking → ℙ Passenger│
│ flightStatus: Flight → Status     │
│ capacity: Flight → ℕ             │
├─────────────────────────────────┤
│ ∀ f: flights •                  │
│   flightStatus(f) = cancelled ⇒  │
│     ¬∃ b: bookings • b.flight = f│
│ ∀ f: flights; b: bookings •      │
│   b.flight = f ⇒                │
│     #(passengers(b)) ≤ capacity(f)│
│ ∀ b: bookings •                 │
│   b.isPaid ∨ b.paymentDue ≤ today│
└─────────────────────────────────┘
```

### 時間依存状態の考慮

動的システムでは、時間の経過により状態が変化します。Z記法では、これを明示的にモデル化できます。

```z
┌─ TimedSystem ────────────────────┐
│ currentTime: Time                │
│ events: ℙ Event                  │
│ schedule: Event → Time           │
│ completed: ℙ Event               │
├─────────────────────────────────┤
│ completed ⊆ events              │
│ ∀ e: completed •                │
│   schedule(e) ≤ currentTime      │
│ ∀ e: events \ completed •        │
│   schedule(e) > currentTime      │
└─────────────────────────────────┘
```

### スキーマの可読性設計

効果的なスキーマ設計では、可読性が重要な要素です。記述の順序、命名規則、制約の grouping により、理解しやすさが大きく変わります。

**良い設計の原則：**

1. **関連する変数を近くに配置する**
2. **制約を論理的な順序で記述する**
3. **意味のある変数名を使用する**
4. **複雑な制約は複数行に分割する**

```z
┌─ WebServer ──────────────────────┐
│ // 接続管理                      │
│ activeConnections: ℙ Connection  │
│ maxConnections: ℕ                │
│                                  │
│ // リソース管理                  │
│ availableMemory: ℕ               │
│ usedMemory: ℕ                    │
│ totalMemory: ℕ                   │
├─────────────────────────────────┤
│ // 接続数制限                    │
│ #activeConnections ≤ maxConnections│
│                                  │
│ // メモリ整合性                  │
│ usedMemory + availableMemory = totalMemory│
│ usedMemory ≥ 0                   │
│ availableMemory ≥ 0              │
└─────────────────────────────────┘
```

このような構造化により、スキーマの理解と保守が容易になります。

## 5.4 操作スキーマ：状態変化の記述

### 操作としての状態変換

Z記法において、操作は「状態変換」として理解されます。操作前の状態から操作後の状態への数学的な関数として、操作の意味を厳密に定義します。この視点により、操作の正しさを数学的に証明でき、操作間の関係も明確になります。

操作スキーマは、「現在の状態」「次の状態」「入力」「出力」の関係を記述します。これにより、操作が何をするかだけでなく、何をしないかも明確になります。

### Delta記法とXi記法

Z記法では、操作を記述するための特別な記法が用意されています。

**Delta記法（Δ）**: 状態が変化する操作
```z
ΔLibrary
≙ Library ∧ Library'
```
これは、操作前の状態（Library）と操作後の状態（Library'）の両方を含むことを意味します。

**Xi記法（Ξ）**: 状態が変化しない操作（問い合わせ操作）
```z
ΞLibrary
≙ ΔLibrary ∧ θLibrary = θLibrary'
```
状態のすべての要素が操作前後で同じであることを表現します。

### 貸出操作の詳細記述

図書館システムの本の貸出操作を例に、操作スキーマの構造を理解しましょう。

```z
┌─ BorrowBook ─────────────────────┐
│ ΔLibrary                         │
│ member?: Member                  │
│ book?: Book                      │
│ result!: RESPONSE                │
├─────────────────────────────────┤
│ // 事前条件                      │
│ member? ∈ members                │
│ book? ∈ books                    │
│ book? ∉ ran loans               │
│ #(loans(member?)) < maxLoans     │
│                                  │
│ // 事後条件                      │
│ loans' = loans ∪ {member? ↦ book?}│
│ books' = books                   │
│ members' = members               │
│ result! = success                │
└─────────────────────────────────┘
```

入力変数は `?` で、出力変数は `!` で標識されます。事前条件は操作が正常に実行されるための条件、事後条件は操作後の状態を記述します。

### エラー処理の形式化

実際のシステムでは、エラー処理が重要です。Z記法では、正常ケースとエラーケースを同じ枠組みで記述できます。

```z
┌─ BorrowBookError ────────────────┐
│ ΞLibrary                         │
│ member?: Member                  │
│ book?: Book                      │
│ result!: RESPONSE                │
├─────────────────────────────────┤
│ member? ∉ members ∨              │
│ book? ∉ books ∨                 │
│ book? ∈ ran loans ∨             │
│ #(loans(member?)) ≥ maxLoans     │
│                                  │
│ result! ∈ {memberNotFound,       │
│            bookNotFound,          │
│            alreadyBorrowed,       │
│            loanLimitExceeded}     │
└─────────────────────────────────┘
```

エラーケースでは状態が変化しない（Ξ記法）ことに注意してください。

### 完全な操作定義

完全な操作は、正常ケースとエラーケースを統合したものです。

```z
CompleteBorrowBook ≙ BorrowBook ∨ BorrowBookError
```

この定義により、すべての可能な入力に対して操作の振る舞いが定義されます。

### 複雑な操作の構造化

より複雑な操作では、段階的な記述が有効です。

```z
┌─ ProcessPurchase ────────────────┐
│ ΔOnlineStore                     │
│ customer?: Customer              │
│ items?: ℙ Product               │
│ paymentInfo?: Payment            │
│ result!: RESPONSE                │
├─────────────────────────────────┤
│ // 第1段階：在庫確認             │
│ ∀ item: items? • item ∈ products │
│ ∀ item: items? •                │
│   inventory(item) ≥ requested(item)│
│                                  │
│ // 第2段階：支払い処理           │
│ ValidatePayment                  │
│ ProcessPayment                   │
│                                  │
│ // 第3段階：在庫更新             │
│ ∀ item: items? •                │
│   inventory'(item) =             │
│     inventory(item) - requested(item)│
│                                  │
│ // 第4段階：注文記録             │
│ CreateOrder                      │
│                                  │
│ result! = orderConfirmed         │
└─────────────────────────────────┘
```

### 操作の前後関係

操作スキーマでは、操作前後の状態の関係を明確に記述します。これにより、操作の影響範囲と副作用を正確に把握できます。

```z
┌─ TransferFunds ──────────────────┐
│ ΔBankingSystem                   │
│ fromAccount?: AccountID          │
│ toAccount?: AccountID            │
│ amount?: ℕ                       │
│ result!: RESPONSE                │
├─────────────────────────────────┤
│ // 事前条件                      │
│ fromAccount? ∈ accounts          │
│ toAccount? ∈ accounts            │
│ fromAccount? ≠ toAccount?        │
│ balance(fromAccount?) ≥ amount?  │
│                                  │
│ // 状態変化                      │
│ balance'(fromAccount?) =         │
│   balance(fromAccount?) - amount?│
│ balance'(toAccount?) =           │
│   balance(toAccount?) + amount?  │
│                                  │
│ // 不変部分                      │
│ ∀ acc: accounts \ {fromAccount?, toAccount?} •│
│   balance'(acc) = balance(acc)   │
│ accounts' = accounts             │
│                                  │
│ result! = transferComplete       │
└─────────────────────────────────┘
```

「不変部分」の明示により、操作が他の口座に影響しないことが保証されます。

### 操作の合成と順序

複数の操作を組み合わせる場合、その順序と依存関係を明確にする必要があります。

```z
BookReservationProcess ≙ 
  CheckAvailability ⨾ 
  ReserveBook ⨾ 
  NotifyMember ⨾ 
  UpdateCatalogue
```

⨾ 記号は操作の順次合成を表します。各操作の出力が次の操作の入力になります。

### 条件付き操作

状況に応じて異なる処理を行う操作も記述できます。

```z
┌─ ProcessReturn ──────────────────┐
│ ΔLibrary                         │
│ member?: Member                  │
│ book?: Book                      │
│ returnDate?: Date                │
│ fine!: ℕ                         │
├─────────────────────────────────┤
│ member? ↦ book? ∈ loans         │
│                                  │
│ returnDate? > dueDate(book?) ⇒   │
│   fine! = calculateFine(book?, returnDate?)│
│                                  │
│ returnDate? ≤ dueDate(book?) ⇒   │
│   fine! = 0                      │
│                                  │
│ loans' = loans \ {member? ↦ book?}│
│ members' = members               │
│ books' = books                   │
└─────────────────────────────────┘
```

この記述により、期限内返却と延滞の両方のケースを統一的に扱えます。

## 5.5 スキーマ演算：複雑な操作の構成

### 操作の代数的構造

Z記法の真の力は、基本的な操作を組み合わせて複雑な操作を構築できることにあります。これは、数学の代数的構造に似ており、操作を「演算子」として扱い、新しい操作を「計算」により導出できます。

この代数的アプローチにより、システムの操作を階層的に構築でき、再利用性と理解可能性が大幅に向上します。また、操作間の関係を数学的に分析することも可能になります。

### スキーマ合成：基本操作の組み合わせ

最も基本的なスキーマ演算は「合成」です。複数のスキーマを論理演算子で組み合わせることで、新しいスキーマを作成できます。

**論理積（∧）による合成：**
```z
AuthenticatedOperation ≙ 
  UserAuthentication ∧ 
  SystemOperation
```

これは、ユーザー認証とシステム操作の両方の制約を満たす操作を定義します。

**論理和（∨）による合成：**
```z
FlexiblePayment ≙ 
  CreditCardPayment ∨ 
  BankTransferPayment ∨ 
  DigitalWalletPayment
```

複数の支払い方法のいずれかを選択できる操作を表現します。

### 操作の順次合成

実世界の多くの操作は、複数の段階に分かれています。Z記法では、これを順次合成（⨾）により表現できます。

```z
CompleteBooking ≙ 
  ValidateRequest ⨾ 
  CheckAvailability ⨾ 
  ProcessPayment ⨾ 
  ConfirmReservation ⨾ 
  SendConfirmation
```

各段階の出力が次の段階の入力になり、全体として一つの複合操作を形成します。

### 条件分岐の表現

操作における条件分岐は、条件付きスキーマ演算により表現できます。

```z
ProcessOrder ≙ 
  (InStock ∧ ImmediateDelivery) ∨
  (OutOfStock ∧ BackOrder) ∨
  (SpecialOrder ∧ CustomProcessing)
```

この表現により、在庫状況に応じた異なる処理フローを統一的に記述できます。

### エラー処理の統合

実用的なシステムでは、各操作にエラー処理が必要です。スキーマ演算により、正常処理とエラー処理を統合できます。

```z
RobustOperation ≙ 
  (Preconditions ∧ NormalProcessing) ∨
  (¬Preconditions ∧ ErrorHandling)
```

より具体的な例：
```z
┌─ SafeWithdrawal ─────────────────┐
│ (ValidAccount ∧ SufficientFunds  │
│  ∧ WithinDailyLimit ∧ ProcessWithdrawal) │
│ ∨                                │
│ (¬ValidAccount ∧ AccountError)   │
│ ∨                                │
│ (¬SufficientFunds ∧ InsufficientFundsError)│
│ ∨                                │
│ (¬WithinDailyLimit ∧ LimitExceededError)│
└─────────────────────────────────┘
```

### 並行操作の表現

並行実行される操作も、スキーマ演算により表現できます。

```z
ParallelProcessing ≙ 
  DatabaseUpdate ∥ 
  CacheRefresh ∥ 
  LogEntry
```

∥ 記号は並行合成を表し、複数の操作が同時に実行されることを示します。

### 操作の抽象化と具体化

スキーマ演算により、抽象的な操作から具体的な操作への段階的な詳細化も可能です。

**抽象レベル：**
```z
PaymentProcess ≙ 
  ValidatePayment ⨾ 
  ProcessTransaction ⨾ 
  UpdateRecords
```

**具体化レベル：**
```z
CreditCardPayment ≙ 
  (ValidateCreditCard ∧ CheckCreditLimit) ⨾
  (ContactPaymentGateway ∧ ProcessCreditTransaction) ⨾
  (UpdateAccountBalance ∧ RecordTransaction ∧ SendReceipt)
```

### 変更操作の最小化

フレーム問題への対処として、「変更する部分」と「変更しない部分」を明確に分離できます。

```z
┌─ MinimalUpdate ──────────────────┐
│ ΔSystemState                     │
│ targetField?: FieldID            │
│ newValue?: Value                 │
├─────────────────────────────────┤
│ // 指定フィールドのみ更新        │
│ state'(targetField?) = newValue? │
│                                  │
│ // その他のフィールドは不変      │
│ ∀ field: dom state \ {targetField?} •│
│   state'(field) = state(field)   │
└─────────────────────────────────┘
```

### 操作の可逆性

一部の操作では、逆操作（undo）が重要です。スキーマ演算により、操作とその逆操作の関係を表現できます。

```z
UndoableOperation ≙ 
  (DoAction ∧ SaveUndoInfo) ∨
  (UndoAction ∧ RestorePreviousState)

// 具体例：ファイル削除と復元
FileManagement ≙ 
  (DeleteFile ∧ MoveToTrash) ∨
  (RestoreFile ∧ MoveFromTrash)
```

### 権限制御の統合

セキュリティ要求の多いシステムでは、すべての操作に権限制御が必要です。

```z
SecureOperation[X] ≙ 
  AuthorizeUser ∧ 
  CheckPermissions ∧ 
  X ∧ 
  LogAccess
```

この汎用パターンにより、任意の操作Xに対してセキュリティ制御を追加できます。

```z
SecureFileAccess ≙ SecureOperation[ReadFile]
SecureDataModification ≙ SecureOperation[UpdateDatabase]
```

### 操作の性能特性

スキーマ演算は、操作の性能特性の分析にも活用できます。

```z
EfficientOperation ≙ 
  (SmallDataSet ∧ LinearSearch) ∨
  (LargeDataSet ∧ IndexedSearch)

OptimizedQuery ≙ 
  CacheCheck ⨾ 
  (CacheHit ∧ ReturnCachedResult) ∨
  (CacheMiss ∧ DatabaseQuery ∧ UpdateCache)
```

このような記述により、性能要求も仕様の一部として形式化できます。

## 5.6 実世界への適用：エレベーター制御システム

### システム要求の分析

エレベーター制御システムは、形式的手法の適用において古典的な例題です。このシステムは、安全性が重要で、並行性と実時間性を持ち、複雑な状態遷移があるため、Z記法の能力を発揮する理想的な対象です。

まず、システムの基本要求を整理しましょう：

**機能要求：**
- 乗客の呼び出しに応答する
- 効率的な運行スケジュールを決定する
- 指定された階で停止する
- ドアの開閉を制御する

**安全要求：**
- ドアが開いている間は移動しない
- 定員を超過しない
- 機械的故障時は安全な状態で停止する

**性能要求：**
- 平均待機時間を最小化する
- エネルギー効率を最適化する

### 基本的な状態モデル

エレベーターシステムの状態を段階的にモデル化していきます。

**基本型の定義：**
```z
[FloorNumber, PassengerID, Time]

Direction ::= up | down | stationary
DoorState ::= open | closed | opening | closing
ElevatorState ::= moving | stopped | maintenance
```

**基本状態スキーマ：**
```z
┌─ ElevatorStatus ─────────────────┐
│ currentFloor: FloorNumber        │
│ direction: Direction             │
│ doorState: DoorState             │
│ elevatorState: ElevatorState     │
│ passengers: ℙ PassengerID        │
│ capacity: ℕ                      │
├─────────────────────────────────┤
│ #passengers ≤ capacity          │
│ elevatorState = moving ⇒         │
│   doorState = closed             │
│ doorState ∈ {open, opening} ⇒    │
│   elevatorState = stopped        │
└─────────────────────────────────┘
```

### 呼び出し管理システム

エレベーターの呼び出し管理は、システムの中核的な機能です。

```z
┌─ CallSystem ─────────────────────┐
│ upCalls: ℙ FloorNumber           │
│ downCalls: ℙ FloorNumber         │
│ cabinCalls: ℙ FloorNumber        │
│ minFloor: FloorNumber            │
│ maxFloor: FloorNumber            │
├─────────────────────────────────┤
│ upCalls ⊆ minFloor .. maxFloor-1 │
│ downCalls ⊆ minFloor+1 .. maxFloor│
│ cabinCalls ⊆ minFloor .. maxFloor │
│ minFloor < maxFloor              │
└─────────────────────────────────┘
```

### 統合システム状態

個別のコンポーネントを統合して、完全なシステム状態を定義します。

```z
┌─ ElevatorSystem ─────────────────┐
│ ElevatorStatus                   │
│ CallSystem                       │
│ currentTime: Time                │
│ lastMaintenance: Time            │
│ totalTrips: ℕ                    │
├─────────────────────────────────┤
│ elevatorState = maintenance ⇒    │
│   passengers = ∅                │
│ currentFloor ∈ minFloor .. maxFloor│
│ lastMaintenance ≤ currentTime    │
└─────────────────────────────────┘
```

### 基本操作：呼び出し登録

外部からの呼び出しを登録する操作を定義します。

```z
┌─ RegisterUpCall ─────────────────┐
│ ΔElevatorSystem                  │
│ floor?: FloorNumber              │
│ result!: RESPONSE                │
├─────────────────────────────────┤
│ floor? ∈ minFloor .. maxFloor-1  │
│ elevatorState ≠ maintenance      │
│                                  │
│ upCalls' = upCalls ∪ {floor?}   │
│ downCalls' = downCalls           │
│ cabinCalls' = cabinCalls         │
│ ΞElevatorStatus                  │
│                                  │
│ result! = callRegistered         │
└─────────────────────────────────┘
```

同様に、下り呼び出しとキャビン内呼び出しの操作も定義します。

### 複雑な操作：スケジューリング

エレベーターの移動先を決定するスケジューリング操作は、システムの知的な部分です。

```z
┌─ DetermineNextFloor ─────────────┐
│ ΞElevatorSystem                  │
│ nextFloor!: FloorNumber          │
│ newDirection!: Direction         │
├─────────────────────────────────┤
│ elevatorState = stopped          │
│ upCalls ∪ downCalls ∪ cabinCalls ≠ ∅│
│                                  │
│ // 現在方向での最優先フロア      │
│ direction = up ⇒                 │
│   nextFloor! = min({f: upCalls ∪ cabinCalls │
│                    | f > currentFloor})     │
│                                  │
│ direction = down ⇒               │
│   nextFloor! = max({f: downCalls ∪ cabinCalls│
│                    | f < currentFloor})     │
│                                  │
│ direction = stationary ⇒         │
│   nextFloor! = min({f: upCalls ∪ downCalls ∪│
│                         cabinCalls │        │
│                    | f ≠ currentFloor})     │
│                                  │
│ // 新しい方向の決定              │
│ nextFloor! > currentFloor ⇒ newDirection! = up│
│ nextFloor! < currentFloor ⇒ newDirection! = down│
│ nextFloor! = currentFloor ⇒ newDirection! = stationary│
└─────────────────────────────────┘
```

### 安全性重視の操作：ドア制御

ドアの開閉は、安全性に直接関わる重要な操作です。

```z
┌─ OpenDoor ───────────────────────┐
│ ΔElevatorSystem                  │
│ result!: RESPONSE                │
├─────────────────────────────────┤
│ // 事前条件：安全性チェック      │
│ elevatorState = stopped          │
│ direction = stationary           │
│ doorState = closed               │
│                                  │
│ // 停止階に呼び出しがある        │
│ currentFloor ∈ upCalls ∪ downCalls ∪ cabinCalls│
│                                  │
│ // 状態更新                      │
│ doorState' = opening             │
│ elevatorState' = elevatorState   │
│ currentFloor' = currentFloor     │
│ direction' = direction           │
│ passengers' = passengers         │
│                                  │
│ // 呼び出しクリア                │
│ upCalls' = upCalls \ {currentFloor}│
│ downCalls' = downCalls \ {currentFloor}│
│ cabinCalls' = cabinCalls \ {currentFloor}│
│                                  │
│ result! = doorOpening            │
└─────────────────────────────────┘
```

### 緊急時操作

安全クリティカルなシステムでは、緊急時の操作も重要です。

```z
┌─ EmergencyStop ──────────────────┐
│ ΔElevatorSystem                  │
│ reason?: EmergencyReason         │
├─────────────────────────────────┤
│ reason? ∈ {fire, earthquake,     │
│            powerFailure, mechanical}│
│                                  │
│ // 即座に停止                    │
│ elevatorState' = maintenance     │
│ direction' = stationary          │
│                                  │
│ // ドアの状態制御                │
│ reason? = fire ⇒ doorState' = open│
│ reason? ≠ fire ⇒ doorState' = closed│
│                                  │
│ // 呼び出しクリア                │
│ upCalls' = ∅                     │
│ downCalls' = ∅                   │
│ cabinCalls' = ∅                  │
│                                  │
│ // その他の状態保持              │
│ currentFloor' = currentFloor     │
│ passengers' = passengers         │
└─────────────────────────────────┘
```

### システムレベルの性質検証

完成したモデルに対して、重要な性質を検証します。

**安全性の性質：**
```z
SafetyInvariant ≙ 
  ∀ ElevatorSystem •
    (doorState ∈ {open, opening} ⇒ elevatorState = stopped) ∧
    (#passengers ≤ capacity) ∧
    (elevatorState = moving ⇒ doorState = closed)
```

**活性の性質：**
```z
LivenessProperty ≙ 
  ∀ ElevatorSystem •
    (upCalls ∪ downCalls ∪ cabinCalls ≠ ∅) ⇒
    ∃ ElevatorSystem' •
      (upCalls' ∪ downCalls' ∪ cabinCalls') ⊂ 
      (upCalls ∪ downCalls ∪ cabinCalls)
```

この活性性質は、呼び出しがあれば最終的に処理されることを保証します。

### 性能特性の形式化

形式的手法は、機能性だけでなく性能特性も記述できます。

```z
┌─ PerformanceMetrics ─────────────┐
│ averageWaitTime: ℝ               │
│ energyConsumption: ℝ             │
│ totalDistance: ℕ                 │
├─────────────────────────────────┤
│ averageWaitTime ≤ maxAcceptableWait│
│ energyConsumption ≤ energyBudget │
│ // 効率性制約                    │
│ ∀ trip: TripSequence •          │
│   optimizeRoute(trip)            │
└─────────────────────────────────┘
```

このエレベーター制御システムの例により、Z記法が実際の複雑なシステムの仕様記述に、どのように活用できるかが理解できます。安全性、機能性、性能のすべてを統一的な枠組みで記述し、検証可能な形で表現できることが、Z記法の大きな価値です。

---

## 章末課題

### 基礎理解演習1：スキーマの読解と分析

以下のZ記法スキーマを読んで、表現されているシステムの構造と制約を説明してください：

```z
┌─ UniversityDatabase ─────────────┐
│ students: ℙ Student              │
│ courses: ℙ Course                │
│ lecturers: ℙ Lecturer            │
│ enrollment: Student ↔ Course     │
│ teaching: Lecturer ↔ Course      │
│ grades: Student ⤇ Course → Grade │
├─────────────────────────────────┤
│ dom enrollment ⊆ students       │
│ ran enrollment ⊆ courses        │
│ dom teaching ⊆ lecturers        │
│ ran teaching ⊆ courses          │
│ ∀ c: courses • ∃ l: lecturers • │
│   l ↦ c ∈ teaching              │
│ dom(dom grades) ⊆ students      │
│ ran(dom grades) ⊆ courses       │
└─────────────────────────────────┘
```

説明すべき内容：
1. 各変数の意味と型
2. 制約条件の意味とその妥当性
3. このモデルで表現できる状況の例
4. 表現できない要求があるとすれば何か

### 基礎理解演習2：操作スキーマの作成

前の演習の大学システムについて、以下の操作のスキーマを作成してください：

**学生の履修登録操作**
- 学生が新しい科目を履修登録する
- 事前条件：学生と科目が存在する、既に履修していない
- 事後条件：履修関係に追加される
- エラーケース：学生不存在、科目不存在、重複履修

1. 正常ケースの操作スキーマ
2. エラーケースの操作スキーマ  
3. 完全な操作定義（正常+エラー）

### 実践演習1：銀行システムのモデル化

以下の要求を満たす銀行システムをZ記法でモデル化してください：

**基本要素：**
- 顧客（氏名、住所、電話番号）
- 口座（口座番号、残高、種類、所有者）
- 取引（取引ID、口座、金額、日時、種類）

**制約：**
- 口座残高は非負
- すべての口座には所有者がいる
- 取引は存在する口座に対してのみ
- 口座番号は一意

**操作：**
- 口座開設
- 預金
- 引き出し
- 口座間送金

1. 状態スキーマの定義
2. 各操作の操作スキーマ
3. 重要な不変条件の特定

### 実践演習2：スキーマ演算の活用

前の銀行システムについて、スキーマ演算を使用して以下を実現してください：

1. **セキュアな操作の定義**
   - すべての操作に認証チェックを追加
   - ログ記録を自動化

2. **エラー処理の統合**
   - 各操作の正常ケースとエラーケースを統合
   - 一貫したエラーレスポンス

3. **取引の原子性**
   - 送金操作を「引き出し+預金」の組み合わせで表現
   - 途中でエラーが発生した場合のロールバック

### 発展演習：実時間システムの仕様化

時間の概念を含む交通信号制御システムをZ記法でモデル化してください：

**要求：**
- 4方向の交差点（南北・東西）
- 各方向に車両用信号と歩行者用信号
- 安全性：対向する方向が同時に青にならない
- 効率性：最小青時間と最大赤時間の制約
- 歩行者要求：ボタン押下による歩行者信号要求

**モデル化すべき要素：**
1. 信号の状態（赤・黄・青）
2. 時間の概念（タイマー、時刻）
3. 車両検知センサー
4. 歩行者要求ボタン
5. 信号変更操作

**検証すべき性質：**
1. 安全性：危険な信号状態が発生しない
2. 活性：すべての方向が最終的に青信号になる
3. 公平性：長時間待機状態にならない

これらの演習を通じて、Z記法による実践的なシステムモデリング能力を身につけ、次章でのプロセス中心記述への準備を整えてください。
