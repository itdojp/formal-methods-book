---
layout: book
title: "付録D：演習問題解答"
appendix: appendix04
order: 14
---

# 付録D　演習問題解答

## D.1 第1章：なぜ形式的手法が必要なのか

### 思考演習1：複雑性分析

**問題**: オンラインバンキングシステムの複雑性分析

**解答例**:

#### 1. システム構成要素の特定

- **フロントエンド**: Webアプリケーション、モバイルアプリ
- **認証システム**: 多要素認証、セッション管理
- **アプリケーション層**: 残高照会、振込、履歴管理
- **データベース**: 顧客情報、取引履歴、残高データ
- **外部連携**: 他行システム、決済ネットワーク
- **セキュリティ**: 暗号化、監査ログ、不正検知
- **インフラ**: ロードバランサー、キャッシュ、バックアップ

#### 2. 相互作用の分析

構成要素数：7個の主要コンポーネント
可能な相互作用数：C(7,2) = 21通り

**主要な相互作用**:
- 認証システム ↔ 全てのサービス（6相互作用）
- データベース ↔ アプリケーション層（複数の読み書き）
- セキュリティ ↔ 全ての通信経路（暗号化、監査）

#### 3. 失敗モードの分析

| 構成要素 | 失敗モード | 全体への影響 | 創発的リスク |
|----------|------------|--------------|--------------|
| 認証システム | ダウン | 全サービス停止 | 高 |
| データベース | 障害 | データ不整合 | 極高 |
| 外部連携 | 通信エラー | 部分的機能停止 | 中 |

#### 4. SILレベル評価

**評価**: SIL 2-3レベル
- 金融損失の可能性（高リスク）
- 個人情報保護の要求
- 形式的手法の適用推奨

### 実践演習：事故分析と予防策検討

**選択事例**: アリアン5号事故

#### 1. 技術的根本原因分析

**直接的原因**:
- 64ビット浮動小数点数 → 16ビット符号付き整数の変換でオーバーフロー
- 水平速度変数の値域がアリアン4号と異なった

**仕様の曖昧性**:
```
曖昧な仕様: "水平速度を整数として格納"
明確な仕様: "水平速度 v は -32768 ≤ v ≤ 32767 の範囲で格納"
```

#### 2. 形式的手法による予防可能性

**Alloyによるモデリング**:
```alloy
sig Velocity {
  value: Int
} {
  value >= -32768 and value <= 32767
}

pred ConversionSafe[v64: Int] {
  v64 >= -32768 and v64 <= 32767
}
```

**模型検査での発見**:
- 入力値域の検証
- 変換関数の前提条件チェック
- 異なる飛行プロファイルでのテスト

#### 3. 現代への教訓

- API設計時の事前条件の明示化
- 型安全性の活用（Rust、Haskellなど）
- 契約プログラミングの導入

## D.2 第2章：数学とプログラムの橋渡し

### 実践演習：状態変化の数学的モデル化

**問題**: 銀行口座システムの状態遷移

**解答**:

#### 1. 状態空間の定義

```math
Account = {
  balance: ℕ,
  status: {Active, Frozen, Closed}
}
```

#### 2. 操作の定義

**預金操作**:
```math
deposit(acc: Account, amount: ℕ) → Account
事前条件: acc.status = Active ∧ amount > 0
事後条件: acc'.balance = acc.balance + amount ∧ acc'.status = acc.status
```

**出金操作**:
```math
withdraw(acc: Account, amount: ℕ) → Account
事前条件: acc.status = Active ∧ amount > 0 ∧ acc.balance ≥ amount
事後条件: acc'.balance = acc.balance - amount ∧ acc'.status = acc.status
```

#### 3. 不変条件

```math
invariant BalanceNonNegative:
  ∀ acc: Account • acc.balance ≥ 0

invariant StatusConsistency:
  ∀ acc: Account • acc.status = Closed ⇒ acc.balance = 0
```

## D.3 第3章：仕様記述の基本

### 実践演習：仕様曖昧性の定量的分析

**問題**: パスワードログイン仕様の曖昧性分析

**元の仕様**:
「ユーザーは有効なパスワードを入力することで、システムにログインできる。パスワードが間違っている場合は、適切なエラーメッセージを表示する。セキュリティのため、連続する失敗については制限を設ける。」

#### 1. 曖昧性の特定（10個以上）

| # | 曖昧な要素 | 可能な解釈数 | リスク |
|---|------------|--------------|--------|
| 1 | 「有効なパスワード」 | 3種類 | 中 |
| 2 | 「適切なエラーメッセージ」 | 5種類 | 低 |
| 3 | 「連続する失敗」の定義 | 4種類 | 高 |
| 4 | 「制限」の内容 | 6種類 | 高 |
| 5 | 失敗カウントのリセット条件 | 3種類 | 高 |
| 6 | システムの応答時間 | 無限 | 中 |
| 7 | 同時ログイン試行の扱い | 4種類 | 高 |
| 8 | パスワード変更後の処理 | 3種類 | 中 |
| 9 | アカウントロック時間 | 無限 | 高 |
| 10 | ログイン成功時のセッション管理 | 5種類 | 中 |

#### 2. 実装バリエーションの計算

基本的な組み合わせ：3 × 5 × 4 × 6 × 3 × 4 × 3 × 5 = 32,400通り

#### 3. 形式化された仕様

```
LoginSystem = {
  maxFailures: ℕ = 3,
  lockoutDuration: Time = 15分,
  sessionTimeout: Time = 30分
}

login(user: User, password: String) → Result
事前条件: 
  user.isActive ∧ 
  user.failureCount < maxFailures ∧
  currentTime - user.lastFailure > lockoutDuration

事後条件:
  password = user.hashedPassword ⇒ 
    (result = Success ∧ user'.failureCount = 0)
  password ≠ user.hashedPassword ⇒ 
    (result = Failure ∧ user'.failureCount = user.failureCount + 1)
```

## D.4 第4章：軽量形式的手法入門 - Alloy

### 演習4.1：図書館システムのAlloyモデル

**問題**: 図書館の貸出システムをAlloyでモデリング

**解答**:

```alloy
sig Book {
  isbn: one ISBN,
  title: one Title
}

sig Member {
  id: one MemberID,
  borrowedBooks: set Book
}

sig ISBN, Title, MemberID {}

fact LibraryConstraints {
  // 各書籍は最大一人が借りられる
  all b: Book | lone m: Member | b in m.borrowedBooks
  
  // 各メンバーは最大5冊まで
  all m: Member | #m.borrowedBooks <= 5
  
  // ISBNは一意
  all b1, b2: Book | b1 != b2 implies b1.isbn != b2.isbn
}

pred borrow[m: Member, b: Book, m': Member, rest: set Member] {
  // 事前条件
  b not in m.borrowedBooks
  #m.borrowedBooks < 5
  no other: Member | b in other.borrowedBooks
  
  // 事後条件
  m'.borrowedBooks = m.borrowedBooks + b
  all other: rest | other.borrowedBooks = other.borrowedBooks
}

// 検証：貸出上限を超えることはない
assert NoOverBorrowing {
  all m: Member | #m.borrowedBooks <= 5
}

check NoOverBorrowing for 10
```

### 演習4.2：ファイルシステムの整合性

**問題**: 階層ファイルシステムの整合性を検証

**解答**:

```alloy
abstract sig FSNode {
  parent: lone Dir
}

sig File extends FSNode {}

sig Dir extends FSNode {
  children: set FSNode
}

one sig Root extends Dir {}

fact FileSystemStructure {
  // ルートディレクトリに親はない
  no Root.parent
  
  // 循環参照なし
  no n: FSNode | n in n.^parent
  
  // 親子関係の一貫性
  all d: Dir, n: FSNode | 
    n in d.children iff d = n.parent
}

// 検証：循環構造がないこと
assert Acyclic {
  no n: FSNode | n in n.^parent
}

check Acyclic for 8
```

## D.5 第8章：模型検査入門

### 演習8.1：相互排除プロトコルの検証

**問題**: Peterson's algorithmの相互排除性を検証

**解答（SPIN/Promela）**:

```promela
bool flag[2] = {false, false};
int turn = 0;
int critical = 0;

proctype Process(int pid) {
    do
    :: true ->
        // Entry protocol
        flag[pid] = true;
        turn = 1 - pid;
        (flag[1-pid] == false || turn == pid);
        
        // Critical section
        critical++;
        assert(critical == 1); // 相互排除の検証
        critical--;
        
        // Exit protocol
        flag[pid] = false;
    od
}

init {
    run Process(0);
    run Process(1);
}

// 検証性質
ltl mutual_exclusion { [] (critical <= 1) }
ltl progress { []<> (Process[0]@critical_section) }
```

### 演習8.2：分散合意プロトコルの活性検証

**問題**: 3ノードの分散合意における活性性質

**解答（TLA+）**:

```tla
---- MODULE ThreeNodeConsensus ----
EXTENDS Integers, Sequences

VARIABLES 
    state,      \* Each node's state: "propose", "accept", "decide"
    proposal,   \* Each node's proposal value
    votes,      \* Votes received by each node
    decided     \* Global decision value

Nodes == {1, 2, 3}
Values == {0, 1}

TypeOK == 
    /\ state \in [Nodes -> {"propose", "accept", "decide"}]
    /\ proposal \in [Nodes -> Values]
    /\ votes \in [Nodes -> SUBSET Nodes]
    /\ decided \in {0, 1, "none"}

Init ==
    /\ state = [n \in Nodes |-> "propose"]
    /\ proposal \in [Nodes -> Values]
    /\ votes = [n \in Nodes |-> {}]
    /\ decided = "none"

Propose(n) ==
    /\ state[n] = "propose"
    /\ state' = [state EXCEPT ![n] = "accept"]
    /\ UNCHANGED <<proposal, votes, decided>>

Vote(n, m) ==
    /\ state[n] = "accept"
    /\ state[m] = "accept"
    /\ proposal[n] = proposal[m]
    /\ votes' = [votes EXCEPT ![n] = @ \cup {m}]
    /\ UNCHANGED <<state, proposal, decided>>

Decide(n) ==
    /\ state[n] = "accept"
    /\ Cardinality(votes[n]) >= 2
    /\ state' = [state EXCEPT ![n] = "decide"]
    /\ decided' = proposal[n]
    /\ UNCHANGED <<proposal, votes>>

Next ==
    \/ \E n \in Nodes : Propose(n)
    \/ \E n, m \in Nodes : Vote(n, m)
    \/ \E n \in Nodes : Decide(n)

Spec == Init /\ [][Next]_<<state, proposal, votes, decided>>

\* 安全性：一意の決定
Safety == decided # "none" => 
    \A n \in Nodes : state[n] = "decide" => proposal[n] = decided

\* 活性：最終的に決定する
Liveness == <>[](\E n \in Nodes : state[n] = "decide")
====
```

## D.6 第10章：プログラム検証

### 演習10.1：ループ不変条件の証明

**問題**: 配列の最大値を求めるアルゴリズムの正しさ証明

**解答**:

```
プログラム:
max := a[0];
i := 1;
while i < n do
  if a[i] > max then max := a[i];
  i := i + 1;

ループ不変条件:
I(i, max) ≡ 1 ≤ i ≤ n ∧ max = max{a[0], a[1], ..., a[i-1]}

証明:

1. 初期化: I(1, a[0])が成立
   - 1 ≤ 1 ≤ n ✓ (n ≥ 1の前提)
   - a[0] = max{a[0]} ✓

2. 保存性: I(i, max) ∧ i < n ∧ 実行 ⟹ I(i+1, max')
   
   場合分け:
   a) a[i] > max の場合:
      max' = a[i]
      I(i+1, max') ≡ 1 ≤ i+1 ≤ n ∧ a[i] = max{a[0],...,a[i]}
      
   b) a[i] ≤ max の場合:
      max' = max
      I(i+1, max') ≡ 1 ≤ i+1 ≤ n ∧ max = max{a[0],...,a[i]}

3. 終了性: I(n, max) ∧ ¬(i < n) ⟹ max = max{a[0],...,a[n-1]}
```

### 演習10.2：再帰関数の全正当性

**問題**: クイックソートの正しさの証明

**解答**:

```
関数定義:
quicksort(arr, low, high)
  if low < high then
    pivot := partition(arr, low, high)
    quicksort(arr, low, pivot-1)
    quicksort(arr, pivot+1, high)

仕様:
事前条件: P ≡ 0 ≤ low ≤ high < |arr|
事後条件: Q ≡ sorted(arr[low..high]) ∧ multiset(arr) = multiset(arr₀)

証明（構造帰納法）:

基底ケース: low ≥ high
  - 配列は空またはサイズ1 → すでにソート済み ✓

帰納ケース: low < high
  仮定: |high - low| < n の場合、quicksortは正しく動作
  
  証明すべき: |high - low| = n の場合の正しさ
  
  1. partition(arr, low, high)により:
     - arr[low..pivot-1] ≤ arr[pivot] ≤ arr[pivot+1..high]
     - multiset保存性
  
  2. 再帰呼び出し:
     - quicksort(arr, low, pivot-1): |pivot-1-low| < n
     - quicksort(arr, pivot+1, high): |high-(pivot+1)| < n
     
  3. 帰納仮定により両方の呼び出しは正しく動作
  
  4. 結果: sorted(arr[low..pivot-1]) ∧ sorted(arr[pivot+1..high])
          ∧ arr[low..pivot-1] ≤ arr[pivot] ≤ arr[pivot+1..high]
          ⟹ sorted(arr[low..high])

終了性:
  測度関数: μ(low, high) = high - low
  各再帰でμが減少する ⟹ 有限回で終了
```

---

これらの解答は、形式的手法の各技法における典型的な問題に対する体系的なアプローチを示しています。実際の問題解決では、問題の特性に応じてこれらの手法を適切に組み合わせて使用してください。