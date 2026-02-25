---
layout: book
title: "第4章　軽量形式的手法入門 - Alloyで始める仕様記述"
nav_order: 4
---

# 第4章　軽量形式的手法入門 - Alloyで始める仕様記述

ミニ要約：
- 関係中心モデリングで構造整合を迅速検査
- 小スコープ反例で短サイクル改善
- 図4-1/図8-1/図10-1で検証レベルを設計
- 戻り先: [付録A（数学的基礎）]({{ '/appendices/appendix-a/' | relative_url }}) / [付録C（記法対照）]({{ '/appendices/appendix-c/' | relative_url }})
- 用語の確認: [用語集]({{ '/glossary/' | relative_url }})

## 4.1 Alloyの哲学：軽量だが強力なアプローチ

### 「軽量」の真の意味

形式的手法の世界に「軽量（Lightweight）」という概念を持ち込んだのは、MITのDaniel Jacksonです。しかし、この「軽量」とは何を意味するのでしょうか。単にツールが使いやすいということではありません。それは、形式的手法に対する根本的に異なるアプローチを表しています。

従来の「重量級」形式的手法では、システムの完全な証明を目指していました。すべての性質を数学的に証明し、100%の正しさを保証することが目標でした。しかし、この完璧主義的アプローチには大きな問題がありました。学習コストが高く、適用に長期間を要し、実際のプロジェクトで使われることが稀だったのです。

Alloyの「軽量」アプローチは、完璧性よりも実用性を重視します。「完全な証明」の代わりに「反例の発見」に焦点を当てます。すべての場合を証明するのではなく、問題のある場合を見つけることで、設計の改善を図るのです。

### 反例駆動の発見的手法

Alloyの核心にあるのは、「反例駆動」の思想です。これは、科学における仮説検証の方法論に似ています。科学者は理論を完全に証明することはできませんが、その理論に矛盾する事実を見つけることで理論を改善していきます。

ソフトウェア設計においても同様です。設計が完璧であることを証明するのは困難ですが、設計に問題があることを示す具体例を見つけることは比較的容易です。Alloyは、この「問題の発見」を自動化します。

例えば、アクセス制御システムを設計しているとします。「権限のあるユーザーのみがファイルにアクセスできる」という性質を確保したいとき、従来の手法では数学的証明を構築します。しかしAlloyでは、「権限のないユーザーがファイルにアクセスできる状況」が存在するかどうかを探索します。そのような状況が見つかれば、設計に問題があることが判明し、修正の指針が得られます。

### 有限範囲での完全探索

Alloyのもう一つの重要な特徴は、「有限範囲での完全探索」です。実世界のシステムは無限の可能性を持ちますが、多くの問題は小さな例で発見できます。Alloyは、指定された範囲内（例：ユーザー数3人以下、ファイル数5個以下）ですべての可能な状況を探索します。

この制限は一見弱点のように見えますが、実際には大きな利点があります。小さな範囲であっても、その範囲内では数学的に厳密な検証が行われます。そして経験的に、多くの設計上の問題は小さな例で発見できることが知られています。

例えば、データベースのトランザクション設計で、デッドロックの可能性を調べるとき、2つのトランザクションと2つのリソースがあれば、多くのデッドロック問題を発見できます。数百のトランザクションを考える必要はありません。

### 探索的設計の支援

Alloyは「証明ツール」ではなく「探索ツール」です。設計者が様々な仮説を立て、それをすばやく検証できる環境を提供します。これにより、設計の初期段階での反復的な改善が可能になります。

従来の開発では、設計上の問題は実装段階やテスト段階で発見されることが多く、修正コストが高くなっていました。Alloyを使えば、設計段階で多くの問題を発見でき、早期修正によるコスト削減が実現できます。

### MITでの開発背景と影響

Alloyは、MITのSoftware Design Groupで開発されました。Daniel Jacksonは、ソフトウェア設計における「概念モデル」の重要性を強調していました。多くのソフトウェアの問題は、実装技術の問題ではなく、基本的な概念設計の問題だという洞察です。

この洞察から生まれたAlloyは、実装の詳細を抜きにして、システムの本質的な構造と振る舞いをモデル化することに特化しています。プログラミング言語の詳細、性能の最適化、具体的なアルゴリズムなどは扱わず、「何をするシステムか」「どのような制約があるか」という高レベルの設計に焦点を当てます。

### 産業界での受容と成功事例

Alloyは学術的なツールとして始まりましたが、設計段階での**反例探索（bounded checking）**により、仕様の穴や整合性違反を早期に発見する目的で実務でも利用されています。

Alloy Analyzerが提供するのは「スコープで有界な探索」であり、得られる保証は「そのスコープ内で反例が存在しない」ことです。スコープ外の一般性を主張する場合は、抽象化の妥当性（小スコープ仮説など）を別途説明する必要があります。

参考（一次・公式情報）：
- Alloy Tools（公式）: <https://alloytools.org/>
- Daniel Jackson, “Alloy: A lightweight object modelling notation” (2002): <https://people.csail.mit.edu/dnj/publications/alloy-journal.pdf>

![図4-1：Alloyによる軽量形式的手法の全体像](../../assets/images/diagrams/alloy-modeling-approach.svg)
（読み取りポイント：関係中心・小さなスコープ・反例駆動）

（読み取りポイント：図4-1参照）
- 関係中心: データは集合と関係で表現し、制約は論理式で定義
- スコープ設計: 小さなスコープで反例探索→設計初期の高速フィードバック
- 反例駆動: 反例から仕様/モデルを短サイクルで改善

### 章末課題（抜粋）

**AI利用時の提出ルール（共通）**
- AIの出力は提案として扱い、合否は検証器で判定する
- 提出物: 使用プロンプト / 生成仕様・不変条件 / 検証コマンドとログ（seed/深さ/スコープ） / 反例が出た場合の修正履歴
- 詳細なテンプレは付録D・付録Fを参照する


解答の骨子・採点観点は[付録D]({{ '/appendices/appendix-d/' | relative_url }})を参照。

1. 図4-1の観点を用いて、あなたのドメインの概念を2つ（集合/関係）で表し、重要な制約を1つ日本語で記述せよ。
2. 反例が得られた場合に、スコープ・制約・抽象度のどれを先に見直すべきか、理由を50–80字で述べよ。

＜解答の方向性（骨子）＞
- 問1: 核となる関係（例: 所有/包含/順序）と不変条件（例: 反射性/非循環）が望ましい。
- 問2: まず制約の適正化（過不足）→スコープ調整→抽象度の見直しの順で診断。

## 4.2 Alloyの世界観：関係中心のモデリング

### オブジェクトから関係へのパラダイムシフト

多くのプログラマーは、オブジェクト指向の世界観に慣れ親しんでいます。「オブジェクトがあり、オブジェクトには属性とメソッドがあり、オブジェクト間でメッセージをやり取りする」という考え方です。この世界観は強力ですが、システムの構造を理解するには、時として制限となることがあります（自動探索と反例の教育的価値は第8章参照）。

Alloyは、異なる世界観を提示します。「関係中心」の世界観です。システムを「要素（atom）の集合」と「要素間の関係（relation）」として捉えます。この視点により、システムの構造をより抽象的に、より本質的に理解できます（検証レベルの使い分けは図10-1参照）。

例えば、大学の履修システムを考えてみましょう。オブジェクト指向では、「学生オブジェクト」「科目オブジェクト」を作り、学生オブジェクトが「履修リスト」を属性として持つかもしれません。しかしAlloyでは、「学生」「科目」という集合と、「履修関係」という関係で表現します。

【ツール準拠（そのまま動く）】
```alloy
sig Student {
    enrollment: set Course
}

sig Course {}
```

この表現により、`enrollment` は `Student -> Course` 型の関係（フィールド）として扱われ、`s.enrollment` で学生 `s` が履修する科目集合を参照できます。関係性が明確になり、様々な制約や性質を自然に表現できます。

### 関係としての世界の構造

関係中心の世界観では、すべてが「関係」として理解されます。これは、データベースの関係モデルや、グラフ理論の考え方に近いものです。

- **所有関係**: ユーザーがファイルを所有する
- **包含関係**: フォルダがファイルを含む
- **依存関係**: モジュールが他のモジュールに依存する
- **継承関係**: クラスが他のクラスを継承する
- **通信関係**: プロセスが他のプロセスと通信する

これらの関係を明示的にモデル化することで、システムの構造的な性質を分析できます。

### アトムとシグネチャ

Alloyの基本的な構成要素は「アトム（atom）」です。アトムは、分割できない基本的な要素で、システムの登場人物や物体を表します。アトムは「シグネチャ（signature）」によってグループ化されます。

【ツール準拠（そのまま動く）】
```text
sig Person {
    age: Int,
    friends: set Person
}

sig Student extends Person {
    courses: set Course
}

sig Teacher extends Person {
    teaches: set Course
}
```

この例では、`Person`、`Student`、`Teacher`がシグネチャで、それぞれのシグネチャに属する個々の要素（例：具体的な学生、具体的な教師）がアトムです。

### フィールドとしての関係表現

シグネチャのフィールドは、実際には関係の表現です。`age: Int`は「Personから整数への関係」、`friends: set Person`は「Personから複数のPersonへの関係」です。

この関係表現により、複雑な構造を簡潔に記述できます：

【ツール準拠（そのまま動く）】
```text
sig File {
    parent: lone Directory,  // 最大1つのディレクトリが親
    contents: set Byte       // 複数のバイトを含む
}

sig Directory {
    children: set File       // 複数のファイルが子
}
```

### 制約としてのファクト

Alloyでは、システムが満たすべき制約を「ファクト（fact）」として記述します。ファクトは、すべての有効なモデルで成り立つべき性質です。

【ツール準拠（そのまま動く）】
```text
fact NoSelfLoop {
    // 人は自分自身の友達にはなれない
    no p: Person | p in p.friends
}

fact SymmetricFriendship {
    // 友達関係は対称的
    all p1, p2: Person | p1 in p2.friends iff p2 in p1.friends
}

fact FileSystemTree {
    // ファイルシステムは木構造
    no f: File | f in f.^parent  // 循環なし
}
```

### 多重度の表現力

Alloyの関係には「多重度（multiplicity）」を指定できます。これにより、関係の性質を正確に表現できます：

- `one`: ちょうど1つ
- `lone`: 最大1つ（0または1）
- `some`: 最低1つ
- `set`: 任意個数（0以上）

【ツール準拠（そのまま動く）】
```text
sig Car {
    owner: one Person,       // 車には必ず1人の所有者
    driver: lone Person,     // 運転者は0人または1人
    passengers: set Person   // 乗客は0人以上
}
```

### 関係演算の豊富さ

Alloyでは、関係に対する豊富な演算が提供されています：

**結合（join）**: `r.s` - 関係rとsを結合
**転置（transpose）**: `~r` - 関係rの方向を逆転
**反射推移閉包**: `^r` - 関係rの推移閉包
**推移閉包**: `*r` - 関係rの反射推移閉包

例：
【ツール準拠（そのまま動く）】
```text
// すべての祖先
person.^parent

// 相互フォロー関係
person.follows & person.~follows

// 到達可能なすべてのファイル
directory.*children
```

### 関係による制約表現

関係中心の表現により、複雑な制約も自然に表現できます：

【ツール準拠（そのまま動く）】
```text
// セキュリティポリシー
fact AccessControl {
    // ファイルにアクセスできるのは所有者または権限を持つユーザー
    all f: File, u: User | 
        u in f.readers implies (u = f.owner or u in f.authorized)
}

// 整合性制約
fact DatabaseConsistency {
    // 外部キー制約
    all o: Order | o.customer in Customer
    
    // 在庫制約
    all p: Product | p.stock >= 0
}
```

## 4.3 基本的な構造の記述

### 最初のAlloyモデル：住所録システム

Alloyでのモデリングを学ぶために、身近な例である住所録システムを作ってみましょう。この例を通じて、Alloyの基本的な構文と考え方を理解できます。

【ツール準拠（そのまま動く）】
```alloy
module AddressBook

// 基本的なシグネチャの定義
sig Name {}
sig Address {}

// 住所録のエントリ
sig Contact {
    name: one Name,
    address: lone Address,
    friends: set Contact
}
```

この簡単なモデルでも、多くのことを表現しています：
- すべての連絡先は必ず1つの名前を持つ
- 連絡先は住所を持たない場合もある（lone = 0または1）
- 連絡先は複数の友人を持てる

### シグネチャ階層の活用

より複雑な構造を表現するために、シグネチャの継承を使えます：

【ツール準拠（そのまま動く）】
```alloy
abstract sig Contact {
    name: one Name,
    address: lone Address
}

sig PersonalContact extends Contact {
    birthday: lone Date,
    relatives: set PersonalContact
}

sig BusinessContact extends Contact {
    company: one Company,
    position: lone String
}

sig Company {
    employees: set BusinessContact
}
```

`abstract`キーワードにより、`Contact`自体のアトムは存在せず、具体的な継承先のアトムのみが存在します。

### 制約による構造の精密化

基本的な構造だけでは不十分です。現実的な制約を追加することで、より正確なモデルになります：

【ツール準拠（そのまま動く）】
```alloy
fact ConsistentEmployment {
    // 会社の従業員リストと個人の勤務先は一致する
    all b: BusinessContact, c: Company |
        b in c.employees iff c = b.company
}

fact NoSelfRelation {
    // 自分自身との関係は禁止
    no c: Contact | c in c.friends
    no p: PersonalContact | p in p.relatives
}

fact ReasonableRelatives {
    // 親族関係は対称的
    all p1, p2: PersonalContact |
        p1 in p2.relatives iff p2 in p1.relatives
}
```

### 動的な振る舞いの表現

Alloyは静的構造だけでなく、動的な振る舞いも表現できます。「時間」の概念を導入することで、状態の変化をモデル化できます：

【ツール準拠（そのまま動く）】
```alloy
sig Time {}

sig Contact {
    name: one Name,
    address: Address lone -> Time,  // 時間により住所が変わる
    friends: Contact set -> Time    // 友人関係も時間により変化
}

// 住所変更の操作
pred moveAddress[c: Contact, newAddr: Address, t, t': Time] {
    // 事前条件：時間t'はtの直後
    t' = t.next
    
    // 住所の変更
    c.address.t' = newAddr
    
    // 他の部分は変化しない
    all other: Contact - c | other.address.t' = other.address.t
    all contact: Contact | contact.friends.t' = contact.friends.t
}
```

### 実践例1：電子メールシステムのアクセス制御

より実践的な例として、電子メールシステムのアクセス制御をモデル化してみましょう：

【ツール準拠（そのまま動く）】
```alloy
module EmailSecurity

// 基本エンティティ
sig User {
    roles: set Role
}

sig Role {
    permissions: set Permission
}

sig Permission {}

sig Email {
    sender: one User,
    recipients: set User,
    confidential: lone User  // 機密メールの場合、閲覧可能ユーザー
}

// 具体的な権限
one sig ReadEmail, SendEmail, AdminAccess extends Permission {}

// 具体的な役割  
one sig RegularUser, Manager, Administrator extends Role {}

// アクセス制御の制約
fact RolePermissions {
    RegularUser.permissions = ReadEmail + SendEmail
    Manager.permissions = ReadEmail + SendEmail  
    Administrator.permissions = ReadEmail + SendEmail + AdminAccess
}

// セキュリティポリシー
pred canReadEmail[u: User, e: Email] {
    // 送信者または受信者は読める
    u = e.sender or u in e.recipients
    or
    // 機密メールでない場合、読み取り権限があれば読める
    (no e.confidential and ReadEmail in u.roles.permissions)
    or  
    // 機密メールの場合、指定ユーザーまたは管理者のみ
    (some e.confidential and (u = e.confidential or AdminAccess in u.roles.permissions))
}

// セキュリティ検証のアサーション
assert NoUnauthorizedAccess {
    all u: User, e: Email |
        canReadEmail[u, e] or not (u can read e)
}

check NoUnauthorizedAccess for 5 User, 5 Email, 3 Role
```

### 実践例2：オンライン書店の在庫管理システム

複雑なビジネスロジックを含む例として、オンライン書店システムをモデル化します：

【ツール準拠（そのまま動く）】
```alloy
module OnlineBookstore

// 基本エンティティ
sig Book {
    isbn: one ISBN,
    price: one Int,
    stock: Int one -> Time
}

sig ISBN {}

sig Customer {
    orders: set Order
}

sig Order {
    items: set OrderItem,
    status: Status one -> Time,
    timestamp: one Time
}

sig OrderItem {
    book: one Book,
    quantity: one Int
}

abstract sig Status {}
one sig Pending, Confirmed, Shipped, Delivered, Cancelled extends Status {}

sig Time {
    next: lone Time
}

// ビジネス制約
fact ValidQuantities {
    all item: OrderItem | item.quantity > 0
    all b: Book, t: Time | b.stock.t >= 0
}

fact OrderIntegrity {
    all o: Order | some o.items  // 空の注文は存在しない
    all item: OrderItem | one orders.items.item  // 各項目は1つの注文にのみ属する
}

// 在庫予約操作
pred reserveStock[b: Book, qty: Int, t, t': Time] {
    t' = t.next
    b.stock.t >= qty  // 十分な在庫がある
    b.stock.t' = b.stock.t - qty  // 在庫を減らす
    
    // 他の本の在庫は変化しない
    all other: Book - b | other.stock.t' = other.stock.t
}

// 注文処理操作
pred processOrder[o: Order, t, t': Time] {
    t' = t.next
    o.status.t = Pending
    
    // 在庫チェック
    all item: o.items | item.book.stock.t >= item.quantity
    
    // 在庫予約
    all item: o.items | 
        item.book.stock.t' = item.book.stock.t - item.quantity
    
    // ステータス更新
    o.status.t' = Confirmed
}

// ビジネスルール検証
assert NoOverselling {
    all b: Book, t: Time | 
        b.stock.t >= 0 implies 
            (all t': Time | t'.^(~next) = t implies b.stock.t' >= 0)
}

assert OrderConsistency {
    all o: Order, t: Time |
        o.status.t = Confirmed implies
            (all item: o.items | item.quantity <= item.book.stock.t)
}

check NoOverselling for 5 Book, 5 Order, 10 Time
check OrderConsistency for 5 Book, 5 Order, 10 Time
```

### 実践例3：分散システムのリーダー選出アルゴリズム

より高度な例として、分散システムにおけるリーダー選出アルゴリズムをモデル化します：

【ツール準拠（そのまま動く）】
```alloy
module LeaderElection

// ノードとメッセージ
sig Node {
    id: one Int,
    leader: Node lone -> Time,
    alive: Boolean one -> Time
}

sig Message {
    from: one Node,
    to: one Node,
    content: one MessageType,
    timestamp: one Time
}

abstract sig MessageType {}
one sig Election, OK, Coordinator extends MessageType {}

sig Time {
    next: lone Time
}

// アルゴリズムの制約
fact UniqueIDs {
    all disj n1, n2: Node | n1.id != n2.id
}

fact InitialState {
    some first: Time | no first.~next and
        all n: Node | 
            no n.leader.first and
            n.alive.first = True
}

// リーダー選出プロセス
pred startElection[n: Node, t: Time] {
    n.alive.t = True
    no n.leader.t  // リーダーが決まっていない
    
    // より高いIDを持つノードに選出メッセージを送信
    all higher: Node | higher.id > n.id and higher.alive.t = True implies
        some m: Message | 
            m.from = n and m.to = higher and 
            m.content = Election and m.timestamp = t
}

pred respondToElection[receiver: Node, sender: Node, t: Time] {
    receiver.alive.t = True
    receiver.id > sender.id  // 受信者のIDが高い
    
    // OK応答を送信
    some m: Message |
        m.from = receiver and m.to = sender and
        m.content = OK and m.timestamp = t
    
    // 自分も選出プロセスを開始
    startElection[receiver, t]
}

pred becomeLeader[n: Node, t, t': Time] {
    t' = t.next
    n.alive.t = True
    
    // タイムアウト内にOK応答がなかった
    no m: Message | 
        m.to = n and m.content = OK and m.timestamp = t
    
    // 自分をリーダーに設定
    n.leader.t' = n
    
    // より低いIDのノードにCoordinatorメッセージを送信
    all lower: Node | lower.id < n.id and lower.alive.t = True implies
        some m: Message |
            m.from = n and m.to = lower and
            m.content = Coordinator and m.timestamp = t'
}

// 安全性の検証
assert LeaderUniqueness {
    all t: Time | lone n: Node | n.leader.t = n
}

assert LeaderIsAlive {
    all n: Node, t: Time | 
        n.leader.t = n implies n.alive.t = True
}

assert HighestIdWins {
    all t: Time, n: Node |
        n.leader.t = n implies
            (no higher: Node | higher.id > n.id and higher.alive.t = True)
}

check LeaderUniqueness for 5 Node, 10 Message, 8 Time
check LeaderIsAlive for 5 Node, 10 Message, 8 Time  
check HighestIdWins for 5 Node, 10 Message, 8 Time
```

これらの実例は、第8章の模型検査や第11章の開発プロセス統合で再び参照され、Alloyモデルの実用的価値を具体的に示しています。

### 複数のシグネチャ間の関係

実世界のシステムでは、複数の種類の要素が複雑に関連します：

【ツール準拠（そのまま動く）】
```alloy
sig User {
    owns: set File,
    groups: set Group
}

sig Group {
    members: set User,
    permissions: set Permission
}

sig File {
    owner: one User,
    readers: set User,
    groups: set Group
}

sig Permission {}

// 整合性制約
fact Consistency {
    // 所有関係の一致
    all u: User, f: File | f in u.owns iff u = f.owner
    
    // グループメンバーシップの一致
    all u: User, g: Group | u in g.members iff g in u.groups
}

// アクセス制御ポリシー
fact AccessControl {
    all f: File, u: User |
        u in f.readers implies (
            u = f.owner or  // 所有者はアクセス可能
            some g: u.groups & f.groups | some g.permissions  // グループ権限
        )
}
```

### ユーティリティ述語の定義

複雑なモデルでは、再利用可能な述語を定義することで可読性が向上します：

【ツール準拠（そのまま動く）】
```alloy
// ユーザーがファイルにアクセス可能かを判定
pred canAccess[u: User, f: File] {
    u in f.readers or
    u = f.owner or
    some g: u.groups & f.groups | some g.permissions
}

// ファイルが孤児（所有者のいない）状態かを判定
pred orphaned[f: File] {
    no f.owner
}

// セキュリティポリシー違反の検出
pred securityViolation {
    some f: File, u: User |
        not canAccess[u, f] and u in f.readers
}
```

### モデルの段階的構築

大きなモデルは、段階的に構築することが重要です：

**第1段階**：基本的な要素とその関係
【ツール準拠（そのまま動く）】
```alloy
sig File {}

sig User {
    owns: set File
}
```

**第2段階**：制約の追加
【ツール準拠（そのまま動く）】
```alloy
sig File {}

sig User {
    owns: set File
}

// 各ファイルはちょうど1人のユーザーに所有される
fact UniqueOwner {
    all f: File | one u: User | f in u.owns
}
```

**第3段階**：複雑な関係の導入
【ツール準拠（そのまま動く）】
```alloy
sig File {}

sig Group {
    groupFiles: set File
}

sig User {
    owns: set File,
    groups: set Group
}
```

**第4段階**：ポリシーと制約の詳細化
【擬似記法】（省略を含むため、そのままツールへ投入できません）
```alloy
fact AccessPolicy { ... }
fact ConsistencyRules { ... }
```

この段階的アプローチにより、複雑さを管理しながら正確なモデルを構築できます。

## 4.4 制約と性質の表現

### 論理式による制約表現

Alloyの真価は、複雑な制約を論理式で表現できることにあります。自然言語では曖昧になりがちな要求を、数学的に厳密な形で記述できます。

基本的な論理演算子：
- `and` または `&&`: 論理積
- `or` または `||`: 論理和  
- `not` または `!`: 否定
- `implies` または `=>`: 含意
- `iff` または `<=>`: 同値

例：大学の履修システムの制約
【ツール準拠（そのまま動く）】
```alloy
fact EnrollmentRules {
    // 学生は最大5科目まで履修可能
    all s: Student | #s.courses <= 5
    
    // 必修科目は全学生が履修する
    all s: Student | RequiredCourse in s.courses
    
    // 上級科目は下級科目の履修が前提
    all s: Student, c: AdvancedCourse |
        c in s.courses implies c.prerequisite in s.courses
}
```

### 量詞による一般的制約

量詞は、「すべて」や「存在する」といった概念を表現するために使います：

- `all x: Set | formula`: すべてのxについて式が成り立つ
- `some x: Set | formula`: 少なくとも1つのxについて式が成り立つ
- `no x: Set | formula`: どのxについても式が成り立たない
- `one x: Set | formula`: ちょうど1つのxについて式が成り立つ
- `lone x: Set | formula`: 最大1つのxについて式が成り立つ

実例：ファイルシステムの制約
【ツール準拠（そのまま動く）】
```alloy
fact FileSystemInvariants {
    // すべてのファイルは最大1つの親ディレクトリを持つ
    all f: File | lone f.parent
    
    // ルートディレクトリは必ず1つ存在する
    one d: Directory | no d.parent
    
    // すべてのディレクトリは有限の深さに存在する
    all d: Directory | d not in d.^parent
    
    // 空でないディレクトリが存在する
    some d: Directory | some d.children
}
```

### 集合演算による関係表現

Alloyでは、集合演算を使って複雑な関係を表現できます：

- `s1 + s2`: 和集合
- `s1 & s2`: 積集合  
- `s1 - s2`: 差集合
- `s in t`: 包含関係
- `#s`: 集合のサイズ

銀行システムの例：
【ツール準拠（そのまま動く）】
```alloy
sig Account {
    owner: one Customer,
    balance: one Int,
    authorized: set Customer
}

sig Customer {
    accounts: set Account
}

fact BankingRules {
    // 口座の所有者は必ず承認ユーザーに含まれる
    all a: Account | a.owner in a.authorized
    
    // 残高は非負
    all a: Account | a.balance >= 0
    
    // 顧客の口座リストと口座の所有者は一致
    all c: Customer, a: Account |
        a in c.accounts iff c = a.owner
        
    // 共同口座（複数の承認ユーザー）の検出
    all a: Account | #a.authorized > 1 implies a in JointAccount
}
```

### 時間的性質の表現

システムの動的な振る舞いや時間的制約も表現できます：

【ツール準拠（そのまま動く）】
```alloy
sig State {
    next: lone State,
    users: set User,
    sessions: set Session
}

sig Session {
    user: one User,
    startTime: one State,
    endTime: lone State
}

fact SessionLifecycle {
    // セッションは開始時刻より後に終了する
    all s: Session | 
        some s.endTime implies s.endTime in s.startTime.^next
    
    // セッション中はユーザーがアクティブ
    all s: Session, st: State |
        st in s.startTime.*next and 
        (no s.endTime or st in s.endTime.^~next) implies
        s.user in st.users
        
    // 同一ユーザーの並行セッションは禁止
    all u: User, st: State |
        lone s: Session | s.user = u and 
        st in s.startTime.*next and
        (no s.endTime or st in s.endTime.^~next)
}
```

### セキュリティポリシーの形式化

Alloyは、セキュリティポリシーの記述に特に適しています：

【ツール準拠（そのまま動く）】
```alloy
sig Subject {
    roles: set Role,
    clearance: one SecurityLevel
}

sig Object {
    classification: one SecurityLevel,
    owner: one Subject
}

sig Role {
    permissions: set Permission
}

sig Permission {}
sig SecurityLevel {
    dominates: set SecurityLevel
}

fact BellLaPadulaModel {
    // No Read Up: 被験者は自分のクリアランスレベル以下のオブジェクトのみ読める
    all s: Subject, o: Object |
        canRead[s, o] implies o.classification in s.clearance.*dominates
        
    // No Write Down: 被験者は自分のクリアランスレベル以上のオブジェクトにのみ書ける
    all s: Subject, o: Object |
        canWrite[s, o] implies s.clearance in o.classification.*dominates
}

pred canRead[s: Subject, o: Object] {
    ReadPermission in s.roles.permissions or s = o.owner
}

pred canWrite[s: Subject, o: Object] {
    WritePermission in s.roles.permissions or s = o.owner
}
```

### 不変条件の階層化

複雑なシステムでは、制約を階層化して管理することが重要です：

【ツール準拠（そのまま動く）】
```alloy
// レベル1: 基本的なデータ整合性
fact BasicConsistency {
    // 参照整合性
    all ref: Reference | ref.target in ValidTargets
    
    // 一意性制約  
    all disj x, y: Entity | x.id != y.id
}

// レベル2: ビジネスルール
fact BusinessRules {
    // 在庫制約
    all p: Product | p.stock >= p.reserved
    
    // 注文制約
    all o: Order | o.total = sum[o.items.price]
}

// レベル3: セキュリティポリシー
fact SecurityPolicies {
    // アクセス制御
    all s: Subject, r: Resource |
        accesses[s, r] implies authorized[s, r]
        
    // 監査ログ
    all action: Action | some log: AuditLog | log.action = action
}

// レベル4: 性能制約
fact PerformanceConstraints {
    // キャッシュサイズ制限
    #CacheEntries <= MaxCacheSize
    
    // 接続数制限
    #ActiveConnections <= MaxConnections
}
```

このような階層化により、制約の目的と重要度を明確にし、段階的な検証が可能になります。

## 4.5 Alloy Analyzerによる検証の実践

### 模型検査の基本概念

Alloy Analyzerは、作成したモデルを実際に検査するためのツールです。「模型検査（Model Checking）」という技術を使って、指定された範囲内ですべての可能な状況を探索し、制約違反や予期しない振る舞いを発見します。

模型検査の基本的な流れ：
1. **モデル生成**: 制約を満たすインスタンスを生成
2. **性質検証**: 特定の性質が成り立つかを確認
3. **反例発見**: 問題があれば具体的な反例を提示
4. **結果分析**: 反例を分析してモデルを改善

### 最初の検証：インスタンス生成

まず、作成したモデルが意味のあるインスタンスを生成できるかを確認しましょう。住所録システムの例：

【ツール準拠（そのまま動く）】
```alloy
// 基本的なインスタンス生成
run {} for 3

// 特定の条件を満たすインスタンス
run {
    some c: Contact | #c.friends > 0
} for 3 Contact, 2 Name

// 複雑な状況のインスタンス
run {
    some disj c1, c2: Contact | 
        c1 in c2.friends and c2 in c1.friends
} for 4
```

`run`コマンドは、制約を満たすインスタンスが存在するかを確認します。`for 3`は「最大3個のアトムを使って探索する」という意味です。

### アサーション：性質の検証

`assert`文を使って、モデルが期待する性質を満たすかを検証できます：

【ツール準拠（そのまま動く）】
```alloy
// 友人関係の対称性をテスト
assert FriendshipSymmetry {
    all c1, c2: Contact | 
        c1 in c2.friends implies c2 in c1.friends
}

// 検証実行
check FriendshipSymmetry for 5

// より複雑な性質
assert NoOrphanedFiles {
    all f: File | some u: User | f in u.owns
}

check NoOrphanedFiles for 4 User, 6 File
```

`check`コマンドは、アサーションが**常に**成り立つかを確認します。反例が見つかれば、その具体例が表示されます。

### 反例の解釈と活用

反例が見つかった場合の分析例：

【ツール準拠（そのまま動く）】
```alloy
sig User {
    files: set File,
    groups: set Group
}

sig Group {
    members: set User,
    sharedFiles: set File
}

sig File {}

fact {
    // ユーザーはグループの共有ファイルにアクセス可能
    all u: User, g: u.groups | g.sharedFiles in u.files
}

assert NoFileSharing {
    // すべてのファイルは1人のユーザーのみが所有
    all f: File | lone u: User | f in u.files
}

check NoFileSharing for 3
```

この例では、`NoFileSharing`アサーションが失敗します。Analyzerは以下のような反例を生成するかもしれません：

【ツール準拠（そのまま動く）】
```text
User0: files = {File0}, groups = {Group0}
User1: files = {File0}, groups = {Group0}  
Group0: members = {User0, User1}, sharedFiles = {File0}
File0: (ファイル)
```

この反例は、「グループ共有により複数ユーザーが同じファイルを持つ」という設計上の矛盾を明確に示しています。

### スコープの調整と効果的な検証

検証の範囲（スコープ）の設定は、検証の効果と性能に大きく影響します：

【ツール準拠（そのまま動く）】
```alloy
// 小さなスコープでの高速検証
check BasicProperty for 2

// 特定の要素を多めに設定
check ScalabilityProperty for 2 User, 6 File, 3 Group

// 大きなスコープでの徹底検証（時間がかかる）
check ComplexProperty for 8

// 特定の条件での検証
check ConditionalProperty for 4 but exactly 2 Admin
```

一般的な指針：
- まず小さなスコープ（2-3要素）で基本的な問題を発見
- 問題が見つからなければ段階的にスコープを拡大
- 特定の要素が重要な場合は個別に制御

### 述語を使った段階的検証

複雑なシナリオは、述語を使って段階的に検証できます：

【ツール準拠（そのまま動く）】
```alloy
// 基本的な状態
pred initialState {
    no User.files
    no Group.sharedFiles
}

// ファイル作成操作
pred createFile[u: one User, f: one File] {
    f not in u.files  // 事前条件（作成者uの所有集合に未登録）
    no other: User - u | f in other.files  // 他ユーザーにも未登録（重複作成の排除）
    // 事後条件は実装依存
}

// セキュリティ違反の検出
pred securityBreach {
    some u: User, f: File |
        f in u.files and
        not authorized[u, f]
}

// 段階的な検証
run initialState for 3
run { initialState and some u: User, f: File | createFile[u, f] } for 3
check { not securityBreach } for 4
```

### モデルの反復改善プロセス

実際の検証では、以下のような反復プロセスを行います。

**1. 初期モデル作成**
【ツール準拠（そのまま動く）】
```alloy
sig Document {
    owner: one User,
    readers: set User,
    authorized: set User
}

sig User {}

fact BasicSecurity {
    all d: Document | d.owner in d.readers
}
```

**2. 基本的な検証**
【ツール準拠（そのまま動く）】
```alloy
run {} for 3  // インスタンス生成確認
assert OwnerCanRead { all d: Document | d.owner in d.readers }
check OwnerCanRead for 3
```

**3. 問題発見と修正**
【ツール準拠（そのまま動く）】
```alloy
// 反例により新しい要求を発見
pred collaborativeDocument {
    some d: Document | #d.readers > 1
}

run collaborativeDocument for 3
```

**4. 制約の追加**
【ツール準拠（そのまま動く）】
```alloy
fact SharePolicy {
    // 共同作業者は明示的に承認される
    all d: Document, u: User |
        u in d.readers and u != d.owner implies
        u in d.authorized
}
```

**5. 再検証**
【ツール準拠（そのまま動く）】
```alloy
assert NoUnauthorizedAccess {
    all d: Document, u: User |
        u in d.readers implies 
        (u = d.owner or u in d.authorized)
}

check NoUnauthorizedAccess for 4
```

この反復プロセスにより、段階的にモデルの品質を向上できます。

## 4.6 Alloy 6の拡張：可変状態（mutable state）と時間（temporal logic）

Alloyは伝統的に「静的構造（関係）」の整合性確認に強い一方、**Alloy 6**では`var`とtemporal operatorにより、状態遷移（トレース）を直接扱えます。これにより、Alloy 4で一般的だった「Stateシグネチャ+ordering」による時間エンコードを省略し、モデルと反例トレースをより近い形で扱えます。

本書の実行環境（付録B）は`tools/bootstrap.sh`でAlloy 6.2.0を固定しており、読者は同一のコマンドで再現できます（環境変数`ALLOY_VERSION`で上書き可能）。

### 基本構文（Alloy 6）

- `var`：シグネチャ/フィールドを「状態によって変化するもの」として宣言する
- `'`（prime）：次状態の値を参照する（例：`Trash' = Trash + f`）
- temporal operator：`always`（常に）、`eventually`（いつか）、`once`（過去に一度でも）、`after`（次状態）など
- `n steps`：探索するトレース長（上限）。スコープとstepsを増やすほど探索コストは増える

### 例：ゴミ箱（Trash）モデル（状態遷移の最小例）

`examples/alloy/trash-temporal.als`は、ファイル集合`File`と、可変なゴミ箱集合`Trash`を持つ最小モデルです。削除（delete）/復元（restore）を遷移として定義し、簡単な安全性性質を検査します。

【ツール準拠（そのまま動く）】
```alloy
var sig Trash in File {}

pred delete[f: File] {
  f not in Trash
  Trash' = Trash + f
}

pred restore[f: File] {
  f in Trash
  Trash' = Trash - f
}

pred stutter {
  Trash' = Trash
}

fact init {
  no Trash
}

fact transitions {
  always (stutter or some f: File | delete[f] or restore[f])
}

example: run { eventually (some Trash and after no Trash) } for 3 but 6 steps

assert restoreAfterDelete {
  always (all f: File | restore[f] implies once delete[f])
}
check restoreAfterDelete for 3 but 6 steps
```

実行（CLI）：

【ツール準拠（そのまま動く）】
```bash
bash tools/bootstrap.sh
bash tools/alloy-check.sh --verbose examples/alloy/trash-temporal.als
```

結果の読み方：
- `run`はトレースの存在確認であり、`SAT`は「条件を満たすトレースが存在」を意味します。
- `check`は反例探索であり、`UNSAT`は「与えたスコープ/steps内では反例が見つからない（性質が保持される）」を意味します（`SAT`なら反例が見つかっています）。

生成物（再現性のための保存先）：
- `.artifacts/alloy/trash-temporal/example-solution-0.md` にトレース（state 0,1,...）が出力されます。
- GUIで可視化したい場合は `java -jar tools/.cache/alloy-6.2.0.jar gui` で起動し、モデルを開いてstateを遷移しながら確認できます。

## 4.7 反例から学ぶ：設計の改善サイクル

### 反例の教育的価値

Alloy Analyzerが提供する反例は、単なるエラー報告ではありません。それは、設計者の思考プロセスを深化させる貴重な学習材料です。反例は、「なぜその状況が問題なのか」「どのような設計判断がその問題を引き起こしたのか」を具体的に示してくれます。

優れた設計者は、反例から学ぶことで設計能力を向上させます。反例を見て、「バグだから修正しよう」と考えるのではなく、「なぜこの状況が可能になったのか」「この状況は本当に問題なのか」「根本的な設計思想に問題があるのか」を考えることが重要です。

### アクセス制御システムの改善例

具体的な例として、ファイルアクセス制御システムの設計改善プロセスを追ってみましょう。

**初期設計**：
【ツール準拠（そのまま動く）】
```alloy
sig User {
    owns: set File,
    canRead: set File
}

sig File {
    owner: one User
}

fact OwnershipConsistent {
    all f: File | f in f.owner.owns
    all u: User, f: u.owns | f.owner = u
}

fact OwnerCanRead {
    all u: User | u.owns in u.canRead
}

assert SecureAccess {
    // ファイルを読めるユーザーは所有者のみ（共有を許可しない）
    all u: User | u.canRead = u.owns
}

check SecureAccess for 3
```

**反例の発見**：
【ツール準拠（そのまま動く）】
```text
User0: owns = {File0}, canRead = {File0, File1}
User1: owns = {File1}, canRead = {File1}
File0: owner = User0
File1: owner = User1
```

この反例は、「User0がFile1を読める」という状況を示しています。これは設計者の意図に反するかもしれませんが、現在のモデルでは合法です。

**設計の見直し**：
この反例から、以下の設計上の判断が必要であることがわかります：
1. ファイル共有は許可するべきか？
2. 許可するなら、どのような制御が必要か？
3. 所有者以外の読み取り権限はどう管理するか？

**改善された設計**：
【ツール準拠（そのまま動く）】
```alloy
sig User {
    owns: set File
}

sig File {
    owner: one User,
    sharedWith: set User
}

// 読み取り権限の定義
fun canRead: User -> File {
    owns + ~sharedWith
}

fact SharePolicy {
    // 共有先は所有者以外（共有操作は別途モデル化）
    all f: File | f.sharedWith in User - f.owner
}

assert AuthorizedAccessOnly {
    // 読めるファイルは所有または共有されたもののみ
    all u: User, f: File |
        f in canRead[u] iff (f in u.owns or u in f.sharedWith)
}

check AuthorizedAccessOnly for 4
```

### グループベースアクセス制御への発展

単純な共有モデルでも新たな反例が見つかるかもしれません。例えば：

【ツール準拠（そのまま動く）】
```alloy
pred LargeSharedFile {
    some f: File | #f.sharedWith > 2
}

run LargeSharedFile for 5
```

この探索により、「多数のユーザーとファイルを共有する」シナリオが可能であることがわかります。これが問題かどうかは要求次第ですが、管理上の課題があるかもしれません。

**グループベースモデルへの改善**：
【ツール準拠（そのまま動く）】
```alloy
sig User {
    memberOf: set Group
}

sig Group {
    members: set User,
    files: set File
}

sig File {
    owner: one User,
    groups: set Group
}

fact GroupConsistency {
    // グループメンバーシップの一致
    all u: User, g: Group |
        u in g.members iff g in u.memberOf
        
    // ファイルとグループの一致
    all f: File, g: Group |
        f in g.files iff g in f.groups
}

fun canAccess: User -> File {
    owns + (memberOf.files)
}

assert GroupAccessControl {
    all u: User, f: File |
        f in u.canAccess iff 
        (f in u.owns or some g: u.memberOf | f in g.files)
}

check GroupAccessControl for 4
```

### 時間的制約の発見と対処

より複雑な反例として、時間的な問題があります：

【ツール準拠（そのまま動く）】
```alloy
sig Time {}

sig User {
    active: set Time
}

sig Session {
    user: one User,
    start: one Time,
    end: lone Time
}

fact SessionLifetime {
    all s: Session |
        some s.end implies s.end in s.start.^next
}

pred ConcurrentSessions {
    some disj s1, s2: Session |
        s1.user = s2.user and
        some t: Time | 
            t in s1.start.*next and t in s2.start.*next and
            (no s1.end or t in s1.end.^~next) and
            (no s2.end or t in s2.end.^~next)
}

run ConcurrentSessions for 3 User, 4 Session, 5 Time
```

この探索により、「同一ユーザーの並行セッション」が可能であることが判明します。これが許可されるべきかどうかは、システムの要求によります。

### パフォーマンス問題の予測

Alloyは、パフォーマンス上の問題も予測できます：

【ツール準拠（そのまま動く）】
```alloy
sig Database {
    tables: set Table,
    connections: set Connection
}

sig Table {
    rows: set Row,
    indexes: set Index
}

sig Connection {
    queries: set Query
}

sig Query {
    targetTable: one Table,
    filterConditions: set Condition
}

fact PerformanceConstraints {
    // 大きなテーブルにはインデックスが必要
    all t: Table | #t.rows > 100 implies some t.indexes
    
    // 同時接続数の制限
    all d: Database | #d.connections <= 50
}

pred PerformanceBottleneck {
    some q: Query |
        #q.targetTable.rows > 1000 and
        no q.targetTable.indexes and
        #q.filterConditions > 0
}

run PerformanceBottleneck for 3
```

### 反例駆動の設計改善メソドロジー

効果的な反例活用のためのメソドロジー：

1. **反例の分類**
   - 真の設計欠陥
   - 要求の不明確さ
   - モデルの不完全性
   - 想定外だが許容可能な状況

2. **根本原因分析**
   - なぜその状況が発生するのか？
   - どの制約が不足しているのか？
   - 暗黙の仮定は何か？

3. **対処戦略の選択**
   - 制約の追加
   - モデルの再構築
   - 要求の明確化
   - 受容（問題でない場合）

4. **改善の検証**
   - 新しい制約の効果確認
   - 他の性質への影響評価
   - より大きなスコープでの再検証

この体系的なアプローチにより、反例を設計改善の強力な武器として活用できます。

---

## 章末課題

### 基礎演習1：Alloyモデルの読解

以下のAlloyモデルを読んで、表現されているシステムの構造と制約を説明してください：

【ツール準拠（そのまま動く）】
```alloy
sig Person {
    spouse: lone Person,
    parents: set Person,
    children: set Person
}

fact FamilyRules {
    // 配偶者関係は対称
    all p1, p2: Person | p1.spouse = p2 iff p2.spouse = p1
    
    // 親子関係は逆方向
    all p1, p2: Person | p1 in p2.parents iff p2 in p1.children
    
    // 自分自身は親になれない
    all p: Person | p not in p.parents
    
    // 配偶者同士は親子関係にない
    all p: Person | no p.spouse & p.parents
}
```

説明すべき点：
1. シグネチャが表現する実世界の概念
2. 各制約の意味とその妥当性
3. このモデルで表現できない家族関係があるか
4. 考えられる反例とその意味

### 基礎演習2：制約の記述

オンライン図書館システムについて、以下の要求をAlloyの制約として記述してください：

**要求**：
- 利用者は複数の本を借りることができる
- 本は同時に複数の人に貸し出せない
- 利用者は最大5冊まで借りられる
- 延滞している利用者は新たに本を借りられない
- 本には返却期限がある

必要なシグネチャと制約を定義してください。

### 実践演習1：セキュリティポリシーのモデル化

以下の要求を満たすファイルアクセス制御システムをAlloyでモデル化してください：

**機能要求**：
- ユーザーはファイルを所有できる
- ファイルは読み取り専用または読み書き可能
- グループを作成し、ユーザーを追加できる
- ファイルをグループと共有できる

**セキュリティ要求**：
- 所有者は常にファイルにアクセス可能
- グループメンバーは共有されたファイルのみアクセス可能
- 読み取り専用ファイルへの書き込みは禁止
- 管理者は全ファイルにアクセス可能

1. 適切なシグネチャを定義
2. 制約をfactとして記述
3. セキュリティ性質をassertとして記述
4. check コマンドで検証

### 実践演習2：模型検査と改善

前の演習で作成したモデルについて：

1. 様々なrunコマンドでインスタンス生成を試す
2. 異なるスコープで検証を実行
3. 発見された反例（もしあれば）を分析
4. 制約や設計を改善
5. 改善版での再検証

### 発展演習：動的振る舞いのモデル化

Alloy 6の`var`とtemporal operatorを用い、以下のシステムの動的な振る舞いをモデル化してください（4.6参照）：

**ATMシステム**：
- 口座には残高がある
- 引き出し操作で残高が減る
- 預け入れ操作で残高が増える
- 残高不足では引き出しできない
- 取引履歴が記録される

1. 状態（口座残高、取引履歴など）を`var`で宣言
2. 各操作を「現状態→次状態」の述語として定義（`x' = ...`）
3. 不変条件/禁止事項を`always`で記述し、`check`で反例探索
4. `for ... but ... steps`で探索スコープとトレース長を調整し、反例→修正→再検証を回す

補足：Alloy 4系のスタイルとして、`State`シグネチャと`util/ordering`で時間を明示的にエンコードする方法もありますが、本書ではAlloy 6の記法を基本とします。

**検証すべき性質**：
- 残高は非負を保つ
- 取引の前後で全体の金額が保存される
- すべての取引が履歴に記録される

これらの演習を通じて、Alloyを使った実践的なモデリング能力を身につけ、次章でのより高度な形式的手法への準備を整えてください。
