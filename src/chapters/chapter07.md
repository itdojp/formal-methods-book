# 第7章　時間を扱う仕様記述 - TLA+入門

## 7.1 分散システムの挑戦：時間と状態の複雑さ

### 分散という根本的な困難

分散システムは、現代のデジタル社会を支える重要な技術基盤ですが、その設計と実装は、単一マシンシステムとは質的に異なる困難を抱えています。これらの困難は、物理的な制約と論理的な制約が複雑に絡み合うことから生じます。

最も根本的な問題は、「時間」の概念の曖昧さです。単一マシンでは、命令の実行順序は基本的に決定論的で、「A が B より前に実行された」という関係は明確です。しかし、分散システムでは、異なるマシン上で実行される操作間の時間的順序関係は自明ではありません。

### 物理時間の限界

各マシンには独自の時計があり、これらの時計を完全に同期させることは不可能です。相対性理論が示すように、絶対的な同時性という概念は存在しません。実用的なレベルでも、ネットワーク遅延、クロックスキュー、タイムゾーンの違いなどにより、「正確な時刻」の共有は困難です。

例えば、東京とニューヨークに配置された二つのサーバーが、それぞれ「12:00:00.000」に操作を実行したとします。しかし、これらの操作は本当に「同時」なのでしょうか？タイムゾーンの差、ネットワーク遅延、クロック精度の違いを考慮すると、この「同時性」は疑わしくなります。

### 因果関係の複雑化

分散システムでは、事象間の因果関係が複雑になります。Aという事象がBという事象の「原因」となるためには、Aに関する情報がBに到達している必要があります。しかし、ネットワーク遅延により、この情報伝播には時間がかかります。

【擬似記法】
```
ノード1: 事象A発生 → メッセージ送信
         |
         ↓ (ネットワーク遅延)
ノード2: メッセージ受信 → 事象B発生
```

この因果関係は、物理時間だけでは表現できません。「論理的時間」という概念が必要になります。

### 部分故障の現実

分散システムでは、「部分故障」が避けられない現実です。システムの一部が故障しても、残りの部分は動作し続けます。これは、従来の単一マシンシステムでは経験しない状況です。

部分故障の典型例：
- **ネットワーク分断**: 一部のノード間の通信が切断
- **ノード故障**: 特定のマシンが応答不能
- **性能劣化**: 一部のノードの処理速度が低下
- **ビザンチン故障**: ノードが任意の誤動作

これらの状況で、システム全体の一貫性をどのように保つかは、分散システム設計の核心的な課題です。

### 一貫性と可用性のトレードオフ

分散システム理論における重要な発見の一つが、「CAP定理」です。これは、以下の三つの性質を同時に満たすことはできないという定理です：

- **一貫性（Consistency）**: すべてのノードが同じデータを見る
- **可用性（Availability）**: システムが常に応答を返す  
- **分断耐性（Partition tolerance）**: ネットワーク分断に耐える

実世界のシステムでは、ネットワーク分断は避けられないため、一貫性と可用性のどちらかを犠牲にする必要があります。この選択は、システムの要求に応じて決定されます。

### 非決定性の管理

分散システムでは、非決定性が本質的な特徴です。同じ初期状態から開始しても、ネットワーク遅延やスケジューリングの違いにより、異なる結果が生じる可能性があります。

この非決定性は、システムの柔軟性をもたらす一方で、正しさの保証を困難にします。「どのような実行順序であっても、システムは安全である」ことを保証する必要があります。

### 合意の困難性

分散システムでは、複数のノードが何らかの値について「合意」する必要がある場面が頻繁にあります。しかし、この合意形成は、思っているより困難です。

**FLP不可能性定理**は、非同期分散システムにおいて、一つでもノード故障がある場合、決定論的な合意アルゴリズムは存在しないことを証明しています。これは、理論的な限界を示す重要な結果です。

実際のシステムでは、この限界を回避するため、様々な仮定（時間制限、故障モデル、確率的アルゴリズムなど）を導入します。

### 状態の爆発

分散システムの状態空間は、ノード数に対して指数的に増大します。N個のノードがそれぞれK個の状態を持つ場合、システム全体の状態数はK^Nになります。

この状態爆発により、システムの振る舞いを完全に把握することは困難になります。形式的手法は、この複雑性を管理し、重要な性質を保証するための重要なツールです。

### TLA+による解決アプローチ

これらの困難に対して、TLA+（Temporal Logic of Actions）は、以下のアプローチを提供します：

- **時相論理による動的性質の記述**: 「いつか」「常に」といった時間的性質を厳密に表現
- **状態遷移システムとしてのモデリング**: システムを状態とその変化として抽象化
- **行動による変化の記述**: 状態変化を「行動」として構造化
- **公平性仮定による現実的なモデリング**: 理想的ではない環境での振る舞いを表現

TLA+は、分散システムの本質的な困難を回避するのではなく、それらを明示的に扱うことで、より確実なシステム設計を可能にします。

## 7.2 TLA+の哲学：行動と時相論理

### Leslie Lamportの革新的洞察

TLA+の開発者であるLeslie Lamportは、分散システム理論の発展に大きく貢献した研究者です。彼の最も重要な洞察の一つは、「システムの振る舞いは状態の列として理解できる」ということでした。

この洞察は単純に見えますが、実は深い含意があります。従来のプログラミングでは、「命令の実行」に焦点が当てられていました。しかしLamportは、重要なのは「何が実行されたか」ではなく、「システムの状態がどのように変化したか」であることを示しました。

この視点の転換により、分散システムの複雑な相互作用も、状態変化の観点から統一的に理解できるようになりました。

### 状態遷移システムとしての世界観

TLA+では、あらゆるシステムを「状態遷移システム」として捉えます。システムは、初期状態から開始し、一連の状態変化（遷移）を経て、様々な状態に到達します。

【擬似記法】
```
初期状態 → 状態1 → 状態2 → 状態3 → ...
```

この単純なモデルにより、極めて複雑な分散システムも理解可能になります。状態には、システムのすべての関連情報（変数の値、ネットワークの状態、各ノードの状況など）が含まれます。

### 行動（Action）による変化の抽象化

TLA+の「行動（Action）」は、状態変化を抽象化する概念です。行動は、「現在の状態」から「次の状態」への変換を記述します。これは、数学的には述語として表現されます。

例えば、変数xの値を1増加させる行動は、以下のように記述できます：
【擬似記法】
```tla
Increment ≜ x' = x + 1
```

ここで、`x'`は次の状態でのxの値、`x`は現在の状態でのxの値を表します。

### 時相論理の表現力

TLA+の時相論理は、システムの動的な性質を表現するための強力な言語を提供します。主要な時相演算子は以下の通りです：

**□ (Box, "常に")**: 性質が常に成り立つ
【擬似記法】
```tla
□(x ≥ 0)  ← xは常に非負
```

**◇ (Diamond, "いつか")**: 性質がいつか成り立つ
【擬似記法】
```tla
◇(x = 10)  ← xはいつか10になる
```

**○ (Next, "次に")**: 次の状態で性質が成り立つ
【擬似記法】
```tla
○(x > y)  ← 次の状態でx > y
```

これらの演算子を組み合わせることで、複雑な動的性質を表現できます：
【擬似記法】
```tla
□◇(process = "ready")  ← プロセスは無限に何度も準備状態になる
◇□(system = "stable")  ← システムはいつか安定し、その後ずっと安定
```

### プリミング記法の威力

TLA+の「プライム記法」（変数名に'を付ける）は、現在の状態と次の状態を区別する簡潔で強力な方法です。この記法により、状態変化を自然に表現できます。

【擬似記法】
```tla
Transfer ≜ 
  ∧ amount > 0
  ∧ balance_from ≥ amount
  ∧ balance_from' = balance_from - amount
  ∧ balance_to' = balance_to + amount
```

この記述は、「amountが正で、送金元に十分な残高があるとき、送金を実行する」という操作を表現しています。

### 公平性（Fairness）の概念

並行/分散システムでは、仕様上は「いつでも実行できる」行動が、スケジューラや環境の偏りで永遠に選ばれない実行（飢餓）が理論上は存在します。公平性（fairness）は、その種の**非現実的な実行を仮定として除外**するための条件です（公平性を入れたから実装が自動的に公平になる、という意味ではありません）。

ここで「可能（`ENABLED`）」は、現在状態からその行動を満たす次状態が存在することを指します。

- **弱公平性（WF）**: ある時点以降ずっと行動が可能なら、その行動は無限回実行される  
  → 「ずっと可能なのに永遠に無視される」実行を除外
- **強公平性（SF）**: 行動が無限回可能になるなら、その行動は無限回実行される  
  → 「可能になるたびに回避され続ける」実行を除外

【ツール準拠（そのまま動く）】
```tla
WF_vars(Action)
SF_vars(Action)
```

### 構成可能性（Compositionality）

TLA+では、小さなシステムから大きなシステムを構成できます。これは、複雑性の管理において重要な特徴です。

【擬似記法】
```tla
System ≜ Process1 ∧ Process2 ∧ Process3
```

各プロセスを独立に仕様化し、それらを論理積で結合することで、システム全体の仕様を得られます。

### 段階的詳細化（Refinement）

TLA+では、抽象的な仕様から具体的な実装への段階的な詳細化を支援します。これにより、高レベルの性質を保ちながら、実装に向けた詳細化を進められます。

【ツール準拠（そのまま動く）】
```tla
抽象仕様 ⊨ 具体仕様
```

この関係により、実装が仕様を満たすことを数学的に保証できます。

### 非決定性の受容

TLA+は、システムの非決定性を問題として扱うのではなく、モデリングの重要な要素として積極的に活用します。非決定性により、実装の自由度を保ちながら、安全性を保証できます。

【擬似記法】
```tla
Next ≜ Action1 ∨ Action2 ∨ Action3
```

どの行動が選択されるかは非決定的ですが、いずれの選択でも安全性が保たれるように設計します。

### 数学的基盤の実用化

TLA+は、集合論、論理学、計算理論といった確立された数学的基盤の上に構築されています。しかし、これらを実用的なシステム記述に適した形で統合しています。

特に、無限集合や高階関数なども自然に扱えることで、抽象的な概念から具体的な実装まで、統一的な枠組みで記述できます。

### ツールとの統合

TLA+は、記述言語だけでなく、検証ツール（TLC）と密接に統合されています。これにより、記述した仕様を実際に検証し、問題を発見できます。理論と実践の橋渡しを提供することも、TLA+の重要な特徴です。

## 7.3 状態と行動：システムの動的モデル

### 状態空間の構造化

TLA+において、「状態」はシステムの完全な情報を表現します。これは、プログラムのすべての変数、ネットワークの状況、外部環境の状態など、システムの振る舞いに影響するあらゆる要素を含みます。

状態を数学的に表現すると、変数から値への関数として理解できます。例えば、銀行システムの状態は以下のようになります：

【擬似記法】
```tla
State ≜ [
  accounts: [AccountID → Nat],
  transactions: Seq(Transaction),
  current_time: Time,
  network_status: NetworkState
]
```

この表現により、システムの任意の時点での完全な状況を記述できます。

### 変数と型の定義

TLA+では、システムの状態を構成する変数を明示的に宣言します。各変数は、取りうる値の集合（型）を持ちます。

【擬似記法】
```tla
VARIABLES 
  balance,      \* 口座残高のマッピング
  pending,      \* 保留中の取引
  log,          \* 取引ログ
  clock         \* システム時刻

TypeInvariant ≜
  ∧ balance ∈ [AccountID → Nat]
  ∧ pending ∈ SUBSET Transaction
  ∧ log ∈ Seq(LogEntry)
  ∧ clock ∈ Nat
```

型不変条件により、状態が常に有効な形式を保つことを保証します。

### 初期状態の指定

システムの動作は、初期状態の指定から始まります。初期状態は、システムが満たすべき最初の条件を記述します。

【擬似記法】
```tla
Init ≜
  ∧ balance = [a ∈ AccountID ↦ InitialBalance[a]]
  ∧ pending = {}
  ∧ log = ⟨⟩
  ∧ clock = 0
```

この指定により、システムの開始時点での状況が明確になります。

### 行動による状態変化

TLA+の行動は、状態変化のパターンを記述します。行動は、現在の状態（プライムなし変数）と次の状態（プライム付き変数）の関係を述語として表現します。

**預金操作の例**：
【擬似記法】
```tla
Deposit(account, amount) ≜
  ∧ amount > 0
  ∧ account ∈ DOMAIN balance
  ∧ balance' = [balance EXCEPT ![account] = @ + amount]
  ∧ log' = Append(log, [type ↦ "deposit", account ↦ account, amount ↦ amount])
  ∧ clock' = clock + 1
  ∧ UNCHANGED pending
```

この行動は、「金額が正で、口座が存在するとき、残高を増加し、ログを記録する」という操作を表現しています。

### 送金操作の複雑性

より複雑な操作として、口座間送金を考えてみましょう。この操作では、複数の変数が協調して変化する必要があります。

【擬似記法】
```tla
Transfer(from, to, amount) ≜
  ∧ amount > 0
  ∧ from ≠ to
  ∧ from ∈ DOMAIN balance ∧ to ∈ DOMAIN balance
  ∧ balance[from] ≥ amount
  ∧ balance' = [balance EXCEPT 
      ![from] = @ - amount,
      ![to] = @ + amount]
  ∧ log' = Append(log, [type ↦ "transfer", from ↦ from, to ↦ to, amount ↦ amount])
  ∧ clock' = clock + 1
  ∧ UNCHANGED pending
```

### 条件付き行動

実際のシステムでは、特定の条件下でのみ実行される行動があります。TLA+では、これを自然に表現できます。

【擬似記法】
```tla
ProcessPendingTransaction ≜
  ∧ pending ≠ {}
  ∧ ∃ t ∈ pending :
      ∧ CanProcess(t)
      ∧ ExecuteTransaction(t)
      ∧ pending' = pending \ {t}
  ∧ UNCHANGED ⟨balance, log, clock⟩
```

### 非決定的選択

TLA+では、複数の行動の中から非決定的に選択することを表現できます。これは、実装の自由度を保ちながら、安全性を保証するために重要です。

【擬似記法】
```tla
Next ≜
  ∨ ∃ account ∈ AccountID, amount ∈ Nat : Deposit(account, amount)
  ∨ ∃ from, to ∈ AccountID, amount ∈ Nat : Transfer(from, to, amount)
  ∨ ProcessPendingTransaction
  ∨ TimeoutCleanup
```

どの行動が実行されるかは非決定的ですが、いずれも安全性を保つように設計されています。

### フレーム条件の重要性

行動を記述する際、「変更されない変数」を明示することが重要です。これは「フレーム条件」と呼ばれ、意図しない副作用を防ぎます。

【擬似記法】
```tla
ReadBalance(account) ≜
  ∧ account ∈ DOMAIN balance
  ∧ UNCHANGED ⟨balance, pending, log, clock⟩
```

読み取り操作では、すべての変数が変更されないことを明示します。

### 原子性の表現

複数の変更を原子的（不可分）に実行する必要がある場合、TLA+では一つの行動内で記述します。

【擬似記法】
```tla
AtomicSwap(account1, account2) ≜
  ∧ account1 ≠ account2
  ∧ account1 ∈ DOMAIN balance ∧ account2 ∈ DOMAIN balance
  ∧ balance' = [balance EXCEPT 
      ![account1] = balance[account2],
      ![account2] = balance[account1]]
  ∧ log' = Append(log, [type ↦ "swap", acc1 ↦ account1, acc2 ↦ account2])
  ∧ clock' = clock + 1
  ∧ UNCHANGED pending
```

### 時間の進行

多くのシステムでは、明示的な時間の進行をモデル化する必要があります。

【擬似記法】
```tla
TickClock ≜
  ∧ clock' = clock + 1
  ∧ ProcessTimeouts
  ∧ UNCHANGED ⟨balance, pending⟩

ProcessTimeouts ≜
  log' = [i ∈ DOMAIN log ↦
    IF log[i].timestamp + TIMEOUT ≤ clock'
    THEN [log[i] EXCEPT !.status = "expired"]
    ELSE log[i]]
```

### 環境との相互作用

システムは、外部環境との相互作用も行います。これも行動として表現できます。

【擬似記法】
```tla
ReceiveExternalRequest(request) ≜
  ∧ ValidRequest(request)
  ∧ pending' = pending ∪ {request}
  ∧ log' = Append(log, [type ↦ "request_received", request ↦ request])
  ∧ clock' = clock + 1
  ∧ UNCHANGED balance
```

### 故障モデリング

実際のシステムでは、様々な故障が発生します。TLA+では、これらも行動として明示的にモデル化できます。

【擬似記法】
```tla
NetworkFailure ≜
  ∧ network_status = "operational"
  ∧ network_status' = "failed"
  ∧ pending' = {}  \* 通信中の取引はすべて失敗
  ∧ UNCHANGED ⟨balance, log, clock⟩

Recovery ≜
  ∧ network_status = "failed"
  ∧ network_status' = "operational"
  ∧ UNCHANGED ⟨balance, pending, log, clock⟩
```

### 状態述語による制約

システムが満たすべき性質を、状態述語として表現できます。

【擬似記法】
```tla
SafetyInvariant ≜
  ∧ TypeInvariant
  ∧ ∀ a ∈ DOMAIN balance : balance[a] ≥ 0
  ∧ TotalMoney' = TotalMoney  \* 金銭保存の法則

TotalMoney ≜ Sum({balance[a] : a ∈ DOMAIN balance})
```

この安全性不変条件は、すべての実行において保たれるべき性質を表現しています。

## 7.4 時相論理：「いつ」と「どのように」を語る言語

### 時間の抽象化

時相論理（Temporal Logic）は、時間に関する推論を行うための論理体系です。TLA+では、物理的な時間を抽象化し、「状態の列」として時間を理解します。これにより、具体的な時間値に依存しない、本質的な時間的性質を表現できます。

時相論理の美しさは、「いつ起こるか」よりも「起こる順序」に焦点を当てることです。これにより、タイミングの詳細に惑わされることなく、システムの本質的な振る舞いを分析できます。

### 基本的な時相演算子

TLA+の時相論理は、いくつかの基本的な演算子から構成されています。

**□ (Always, "常に")**：
【擬似記法】
```tla
□P  ← 性質Pが常に成り立つ
```

例：
【擬似記法】
```tla
□(balance ≥ 0)  ← 残高は常に非負
□(mutex ⟹ ¬(process1_critical ∧ process2_critical))  ← 相互排除
```

**◇ (Eventually, "いつか")**：
【擬似記法】
```tla
◇P  ← 性質Pがいつか成り立つ
```

例：
【擬似記法】
```tla
◇(task_completed)  ← タスクはいつか完了する
◇(system_stable)  ← システムはいつか安定する
```

### 演算子の組み合わせ

時相演算子を組み合わせることで、より複雑な時間的性質を表現できます。

**□◇ (Infinitely Often, "無限に何度も")**：
【擬似記法】
```tla
□◇P  ← 性質Pが無限に何度も成り立つ
```

例：
【擬似記法】
```tla
□◇(process_scheduled)  ← プロセスは無限に何度もスケジュールされる
□◇(garbage_collected)  ← ガベージコレクションが無限に何度も実行される
```

**◇□ (Eventually Always, "いつかずっと")**：
【擬似記法】
```tla
◇□P  ← 性質Pがいつかずっと成り立つ
```

例：
【擬似記法】
```tla
◇□(leader_elected)  ← いつかリーダーが選出され、その後ずっと存在する
◇□(consensus_reached)  ← いつか合意に達し、その後変更されない
```

### リードス・トゥ関係

「AならばいつかB」という関係は、分散システムで重要な性質です。

【擬似記法】
```tla
A ~> B ≜ □(A ⟹ ◇B)
```

例：
【擬似記法】
```tla
request_sent ~> response_received  ← 要求を送ればいつか応答を受ける
failure_detected ~> recovery_initiated  ← 故障を検出すればいつか回復を開始
```

### 安全性と活性の区別

システムの性質は、大きく「安全性」と「活性」に分類できます。

**安全性（Safety）**：「悪いことは決して起こらない」
【擬似記法】
```tla
Safety ≜ □¬BadThing
```

例：
【擬似記法】
```tla
□¬(balance < 0)  ← 残高が負になることはない
□¬(deadlock)  ← デッドロックは発生しない
```

**活性（Liveness）**：「良いことがいつか起こる」
【擬似記法】
```tla
Liveness ≜ ◇GoodThing
```

例：
【擬似記法】
```tla
◇(all_processes_terminate)  ← すべてのプロセスがいつか終了する
□(request ⟹ ◇response)  ← 要求があればいつか応答する
```

### 公平性の時相的表現

現実的なシステムでは、公平性の仮定が重要です。TLA+では、これを時相論理で厳密に表現できます。

**弱公平性（Weak Fairness）**：
【擬似記法】
```tla
WF_vars(A) ≜ ◇□ENABLED ⟨A⟩_vars ⟹ □◇⟨A⟩_vars
```

「行動Aが最終的にずっと可能であれば、Aは無限に何度も実行される」

**強公平性（Strong Fairness）**：
【擬似記法】
```tla
SF_vars(A) ≜ □◇ENABLED ⟨A⟩_vars ⟹ □◇⟨A⟩_vars
```

「行動Aが無限に何度も可能になれば、Aは無限に何度も実行される」

注記：`⟨A⟩_vars` は「アクションAが起き、`vars` が変化する（スタッタリングを除外）」ことを表します。厳密な定義はTLA+言語仕様と TLC のドキュメントを参照してください。

### 相互排除の時相的性質

相互排除プロトコルを例に、時相的性質を詳しく見てみましょう。

【擬似記法】
```tla
MutualExclusion ≜
  ∀ i, j ∈ Processes : i ≠ j ⟹ □¬(pc[i] = "critical" ∧ pc[j] = "critical")

Starvation_Free ≜
  ∀ i ∈ Processes : (pc[i] = "trying") ~> (pc[i] = "critical")

Progress ≜
  (∃ i ∈ Processes : pc[i] = "trying") ⟹ ◇(∃ j ∈ Processes : pc[j] = "critical")
```

### 分散合意の時相的性質

分散合意アルゴリズムでは、以下の時相的性質が重要です：

**合意（Agreement）**：
【擬似記法】
```tla
Agreement ≜ □(decided ⟹ ∀ i, j ∈ Nodes : decision[i] = decision[j])
```

**妥当性（Validity）**：
【擬似記法】
```tla
Validity ≜ □(decided ⟹ ∃ i ∈ Nodes : decision[i] ∈ proposed_values)
```

**終了性（Termination）**：
【擬似記法】
```tla
Termination ≜ ◇decided
```

### 因果関係の時相的表現

分散システムでは、事象間の因果関係が重要です。

【擬似記法】
```tla
CausalOrder ≜ 
  ∀ e1, e2 ∈ Events : 
    (e1.timestamp < e2.timestamp ∧ e1.node = e2.node) ⟹ 
    (e1 happens_before e2)

EventualConsistency ≜
  ◇□(∀ n1, n2 ∈ Nodes : replica[n1] = replica[n2])
```

### 時間制限の表現

実用的なシステムでは、時間制限も重要な要求です。

【擬似記法】
```tla
ResponseTime ≜
  ∀ req ∈ Requests : 
    (request_sent(req)) ~> (response_received(req) ∧ time ≤ req.timestamp + TIMEOUT)

PeriodicMaintenance ≜
  □◇(maintenance_performed ∧ time_since_last_maintenance ≤ MAINTENANCE_INTERVAL)
```

### 故障と回復の時相的モデル

システムの故障と回復も時相論理で表現できます。

【擬似記法】
```tla
FailureRecovery ≜
  □(failure_detected ~> recovery_initiated)

Availability ≜
  □◇(system_operational)

BoundedDowntime ≜
  □(failure_occurred ⟹ ◇≤MAX_DOWNTIME system_operational)
```

### 複雑な時相的性質

実際のシステムでは、複数の時相的性質が組み合わさります。

【擬似記法】
```tla
SystemSpec ≜
  ∧ Safety_Properties
  ∧ Liveness_Properties  
  ∧ Fairness_Assumptions

Safety_Properties ≜
  ∧ MutualExclusion
  ∧ DataConsistency
  ∧ SecurityPolicy

Liveness_Properties ≜
  ∧ Progress
  ∧ EventualTermination
  ∧ ServiceAvailability

Fairness_Assumptions ≜
  ∧ ∀ i ∈ Processes : WF_vars(Step(i))
  ∧ ∀ msg ∈ Messages : SF_vars(Deliver(msg))
```

### 時相論理の表現力と限界

時相論理は強力ですが、万能ではありません。

**表現可能な性質**：
- 安全性と活性
- 公平性と進歩
- 因果関係と順序
- 周期的な振る舞い

**限界**：
- 定量的な時間制約（実時間）
- 確率的な性質
- リソース消費量
- 複雑な数値計算

これらの限界を理解し、適切な抽象化レベルで時相的性質を記述することが重要です。

## 7.5 TLCによる模型検査の実践

### TLCとは何か

TLC（TLA+ Checker）は、TLA+仕様に対する模型検査器です。Leslie Lamportとその同僚により開発されたこのツールは、TLA+仕様を実際に実行し、指定された性質が満たされるかを自動的に検証します。

TLCの最大の価値は、理論的な仕様を「実行可能」にすることです。数学的な記述だけでは見つけにくい問題を、具体的な反例として提示してくれます。これにより、設計段階での問題発見と修正が可能になります。

### 模型検査の基本原理

模型検査は、システムの状態空間を体系的に探索し、指定された性質に違反する状態がないかを確認する技術です。TLCは、以下の手順で検査を行います：

1. **初期状態の生成**：Init述語を満たすすべての状態を生成
2. **状態遷移の探索**：各状態からNext述語により到達可能な状態を計算
3. **性質の検証**：各状態で不変条件や時相的性質をチェック
4. **反例の生成**：違反が見つかれば、その実行トレースを報告

### 仕様の実行可能性

TLA+仕様をTLCで検査するには、仕様が「実行可能」である必要があります。これは、抽象的な数学的記述を、有限の計算で扱える形に制限することを意味します。

**有限化の例**：
【擬似記法】
```tla
CONSTANTS
  Processes,     \* 有限集合として定義
  MaxBalance,    \* 残高の上限
  MaxTime        \* 時間の上限

ASSUME
  ∧ Processes ⊆ {"p1", "p2", "p3"}
  ∧ MaxBalance ∈ Nat ∧ MaxBalance ≤ 1000
  ∧ MaxTime ∈ Nat ∧ MaxTime ≤ 100
```

### 設定ファイルの作成

TLCの動作は、設定ファイル（.cfg）で制御されます。このファイルで、定数値、初期述語、次状態述語、検証する性質などを指定します。

【擬似記法】
```
\* BankingSystem.cfg
CONSTANTS
  Accounts = {"A1", "A2", "A3"}
  InitialBalance = 100
  
SPECIFICATION Spec

INVARIANTS
  TypeInvariant
  SafetyInvariant
  
PROPERTIES
  ProgressProperty
  LivenessProperty
```

### 段階的な検証アプローチ

複雑なシステムの検証では、段階的なアプローチが効果的です。

**第1段階：基本的な型安全性**
【擬似記法】
```tla
TypeInvariant ≜
  ∧ balance ∈ [Accounts → Nat]
  ∧ pending ∈ SUBSET Transactions
  ∧ clock ∈ Nat
```

**第2段階：安全性不変条件**
【擬似記法】
```tla
SafetyInvariant ≜
  ∧ ∀ a ∈ Accounts : balance[a] ≤ MaxBalance
  ∧ ∀ t ∈ pending : t.amount > 0
  ∧ TotalMoney = CHOOSE n ∈ Nat : TRUE  \* 金銭保存
```

**第3段階：活性性質**
【擬似記法】
```tla
Progress ≜ □(pending ≠ {} ⟹ ◇(pending = {}))
```

### 状態空間の制御

TLCの性能と実用性は、状態空間のサイズに大きく依存します。効果的な制御方法を学ぶことが重要です。

**対称性の活用**：
【ツール準拠（そのまま動く）】
```tla
SYMMETRY Permutations(Accounts)
```

プロセスや口座など、同等な要素の順序を無視することで、状態空間を大幅に削減できます。

**状態制約の導入**：
【擬似記法】
```tla
StateConstraint ≜
  ∧ clock ≤ MaxTime
  ∧ ∀ a ∈ Accounts : balance[a] ≤ MaxBalance
  ∧ Cardinality(pending) ≤ MaxPendingTransactions
```

### エラートレースの分析

TLCが不変条件違反を発見すると、問題が発生するまでの実行トレースを出力します。このトレースの分析は、問題の根本原因を理解するために重要です。

**典型的な出力例**：
【擬似記法】
```
Error: Invariant SafetyInvariant is violated.

State 1: (Initial state)
balance = (A1 :> 100 @@ A2 :> 100 @@ A3 :> 100)
pending = {}
clock = 0

State 2:
balance = (A1 :> 50 @@ A2 :> 100 @@ A3 :> 100)  
pending = {[from |-> "A1", to |-> "A2", amount |-> 50]}
clock = 1

State 3:
balance = (A1 :> 50 @@ A2 :> 150 @@ A3 :> 100)
pending = {}
clock = 2
```

### デッドロック検出

TLCは、デッドロック（すべてのプロセスが停止する状態）を自動的に検出します。

【擬似記法】
```tla
\* デッドロックが発生する可能性のある仕様
BadMutex ≜
  ∧ pc[1] = "wait" ∧ pc[2] = "wait"
  ∧ ∀ i ∈ {1,2} : UNCHANGED pc[i]

\* TLCは以下のようなエラーを報告：
\* Error: Deadlock reached.
\* The following 2 states form a deadlock:
```

### 活性性質の検証

活性性質の検証は、安全性よりも計算コストが高くなります。TLCは、強連結成分の分析により、活性性質を効率的に検証します。

【擬似記法】
```tla
EventualProgress ≜ 
  ∀ i ∈ Processes : □(pc[i] = "trying" ⟹ ◇(pc[i] = "critical"))

\* 活性性質違反の例：
\* Error: Temporal properties were violated.
\* Property EventualProgress is violated by the following behavior:
```

### 確率的検証

大きな状態空間を持つシステムでは、完全な検証が困難な場合があります。TLCは、ランダムサンプリングによる確率的検証もサポートします。

【擬似記法】
```
\* 設定ファイルでの指定
CONSTRAINT StateConstraint
SYMMETRY Symmetries  
CHECK_DEADLOCK TRUE
COVERAGE 80
```

### 性能最適化のテクニック

TLCの性能を向上させるための技術：

**並列実行**：
【ツール準拠（そのまま動く）】
```bash
tlc -workers 8 BankingSystem.tla
```

**メモリ最適化**：
【ツール準拠（そのまま動く）】
```bash
tlc -Xmx8g -XX:+UseG1GC BankingSystem.tla
```

**チェックポイント**：
【ツール準拠（そのまま動く）】
```bash
tlc -checkpoint 60 BankingSystem.tla
```

### 反復的な仕様改善

TLCによる検証は、通常、反復的なプロセスです：

1. **初期仕様の作成**
2. **TLCによる検証実行**
3. **エラーの分析と仕様修正**
4. **再検証**

この サイクルを繰り返すことで、徐々に仕様の品質を向上させます。

### 実用的な検証戦略

効果的なTLC活用のための戦略：

**小さく始める**：まず最小限のモデルで基本的な性質を確認
**段階的拡張**：徐々にモデルを複雑化し、新しい性質を追加
**継続的検証**：仕様変更のたびに検証を実行
**性能監視**：検証時間と状態数を記録し、性能劣化を早期発見

### 限界の理解

TLCには限界があることを理解し、適切に活用することが重要です：

**状態爆発**：指数的に増大する状態空間
**有限化の必要性**：無限集合は直接扱えない
**時間的制約**：大規模モデルでは検証時間が膨大
**メモリ制約**：利用可能メモリによる状態数の制限

これらの制約内で、最大限の価値を得るための工夫が、実用的なTLC活用の鍵となります。

## 7.6 実世界への適用：分散コンセンサスアルゴリズム

### 分散合意問題の本質

分散コンセンサス（分散合意）は、分散システムにおける最も基本的で重要な問題の一つです。複数のノードが、ある値について「合意」を形成する必要がある状況は、実世界のあらゆる分散システムで発生します。

この問題の困難さは、ノードの故障、ネットワークの遅延、メッセージの損失などの現実的な制約の中で、すべてのノードが同じ値に合意する必要があることです。さらに、一度合意に達したら、その決定は変更されてはいけません。

### 合意問題の形式的定義

分散合意問題は、以下の性質を満たすアルゴリズムを設計することです：

**合意（Agreement）**：決定したノードは、すべて同じ値を選択する
**妥当性（Validity）**：決定された値は、誰かが提案した値である
**終了性（Termination）**：すべての正常なノードは、最終的に決定を行う

これらの性質をTLA+で表現すると：

【擬似記法】
```tla
VARIABLES
  proposed,    \* 各ノードが提案した値
  decided,     \* 各ノードの決定状態
  decision,    \* 各ノードの決定値
  phase        \* プロトコルのフェーズ

Agreement ≜ 
  ∀ p, q ∈ Nodes : 
    (decided[p] ∧ decided[q]) ⟹ (decision[p] = decision[q])

Validity ≜ 
  ∀ p ∈ Nodes : 
    decided[p] ⟹ decision[p] ∈ {proposed[q] : q ∈ Nodes}

Termination ≜ 
  ◇(∀ p ∈ Nodes : decided[p])
```

### Raftアルゴリズムの概要

Raftは、理解しやすさを重視して設計された分散合意アルゴリズムです。システムをリーダー選出と ログレプリケーションの2つの部分に分け、複雑性を管理しています。

**主要な概念**：
- **ノードの役割**：Leader（リーダー）、Follower（フォロワー）、Candidate（候補者）
- **Term（任期）**：リーダーの統治期間を表す単調増加する番号
- **ログエントリ**：合意すべき操作の記録

### Raftの状態モデル

Raftアルゴリズムの状態を TLA+ で記述してみましょう：

【ツール準拠（そのまま動く）】
```tla
VARIABLES
  \* 永続状態（すべてのサーバー）
  currentTerm,     \* サーバーが見た最新の任期
  votedFor,        \* 現在の任期で投票したCandidateId
  log,             \* ログエントリ

  \* 揮発状態（すべてのサーバー）
  state,           \* Leader, Follower, Candidate
  commitIndex,     \* コミット済みの最高ログインデックス
  
  \* 揮発状態（リーダーのみ）
  nextIndex,       \* 各サーバーに送る次のログエントリ
  matchIndex,      \* 各サーバーで複製済みの最高ログインデックス
  
  \* 補助変数
  messages,        \* ネットワーク上のメッセージ
  election_timer,  \* 選出タイマー
  heartbeat_timer  \* ハートビートタイマー
```

### 初期状態の定義

システムの初期状態では、すべてのノードがフォロワーとして開始します：

【擬似記法】
```tla
Init ≜
  ∧ currentTerm = [s ∈ Servers ↦ 0]
  ∧ votedFor = [s ∈ Servers ↦ Nil]
  ∧ log = [s ∈ Servers ↦ ⟨⟩]
  ∧ state = [s ∈ Servers ↦ Follower]
  ∧ commitIndex = [s ∈ Servers ↦ 0]
  ∧ nextIndex = [s ∈ Servers ↦ [t ∈ Servers ↦ 1]]
  ∧ matchIndex = [s ∈ Servers ↦ [t ∈ Servers ↦ 0]]
  ∧ messages = {}
  ∧ election_timer = [s ∈ Servers ↦ ElectionTimeout]
  ∧ heartbeat_timer = [s ∈ Servers ↦ HeartbeatInterval]
```

### リーダー選出プロセス

Raftのリーダー選出は、以下の段階で行われます：

**1. 選出タイムアウト**：
【擬似記法】
```tla
ElectionTimeout(s) ≜
  ∧ state[s] = Follower
  ∧ election_timer[s] = 0
  ∧ state' = [state EXCEPT ![s] = Candidate]
  ∧ currentTerm' = [currentTerm EXCEPT ![s] = @ + 1]
  ∧ votedFor' = [votedFor EXCEPT ![s] = s]
  ∧ SendRequestVoteRequests(s)
  ∧ election_timer' = [election_timer EXCEPT ![s] = ElectionTimeout]
  ∧ UNCHANGED ⟨log, commitIndex, nextIndex, matchIndex, heartbeat_timer⟩
```

**2. 投票要求の送信**：
【擬似記法】
```tla
SendRequestVoteRequests(s) ≜
  messages' = messages ∪ 
    {[type ↦ "RequestVote",
      term ↦ currentTerm'[s],
      candidateId ↦ s,
      lastLogIndex ↦ Len(log[s]),
      lastLogTerm ↦ IF Len(log[s]) > 0 THEN log[s][Len(log[s])].term ELSE 0,
      dest ↦ t] : t ∈ Servers \ {s}}
```

**3. 投票応答の処理**：
【擬似記法】
```tla
ReceiveRequestVoteResponse(s) ≜
  ∃ m ∈ messages :
    ∧ m.type = "RequestVoteResponse"
    ∧ m.dest = s
    ∧ m.term = currentTerm[s]
    ∧ m.voteGranted = TRUE
    ∧ state[s] = Candidate
    ∧ LET votes ≜ {t ∈ Servers : ∃ msg ∈ messages : 
                     msg.type = "RequestVoteResponse" ∧ 
                     msg.dest = s ∧ msg.voteGranted = TRUE} ∪ {s}
       IN  ∧ Cardinality(votes) > Cardinality(Servers) ÷ 2
           ∧ state' = [state EXCEPT ![s] = Leader]
           ∧ SendHeartbeats(s)
           ∧ UNCHANGED ⟨currentTerm, votedFor, log, commitIndex⟩
```

### ログレプリケーション

リーダーは、クライアントからの要求を受け取り、それをログエントリとして他のサーバーに複製します：

**1. エントリの追加**：
【擬似記法】
```tla
AppendEntry(s, entry) ≜
  ∧ state[s] = Leader
  ∧ log' = [log EXCEPT ![s] = Append(@, entry)]
  ∧ SendAppendEntries(s)
  ∧ UNCHANGED ⟨currentTerm, votedFor, state, commitIndex⟩
```

**2. AppendEntriesの送信**：
【擬似記法】
```tla
SendAppendEntries(s) ≜
  messages' = messages ∪ 
    {[type ↦ "AppendEntries",
      term ↦ currentTerm[s],
      leaderId ↦ s,
      prevLogIndex ↦ nextIndex[s][t] - 1,
      prevLogTerm ↦ IF nextIndex[s][t] > 1 
                     THEN log[s][nextIndex[s][t] - 1].term 
                     ELSE 0,
      entries ↦ SubSeq(log[s], nextIndex[s][t], Len(log[s])),
      leaderCommit ↦ commitIndex[s],
      dest ↦ t] : t ∈ Servers \ {s}}
```

**3. 応答の処理と コミット**：
【擬似記法】
```tla
ProcessAppendEntriesResponse(s) ≜
  ∃ m ∈ messages :
    ∧ m.type = "AppendEntriesResponse"
    ∧ m.dest = s
    ∧ state[s] = Leader
    ∧ m.term = currentTerm[s]
    ∧ IF m.success
       THEN ∧ nextIndex' = [nextIndex EXCEPT ![s][m.source] = m.matchIndex + 1]
            ∧ matchIndex' = [matchIndex EXCEPT ![s][m.source] = m.matchIndex]
            ∧ UpdateCommitIndex(s)
       ELSE ∧ nextIndex' = [nextIndex EXCEPT ![s][m.source] = Max(1, @ - 1)]
            ∧ UNCHANGED matchIndex
    ∧ UNCHANGED ⟨currentTerm, votedFor, log, state, commitIndex⟩
```

### 安全性の保証

Raftアルゴリズムが満たすべき安全性不変条件：

【擬似記法】
```tla
\* ログの一致性
LogMatching ≜
  ∀ s, t ∈ Servers, i ∈ DOMAIN log[s] ∩ DOMAIN log[t] :
    log[s][i].term = log[t][i].term ⟹ 
    ∀ j ∈ 1..i : log[s][j] = log[t][j]

\* リーダーの一意性
LeaderUniqueness ≜
  ∀ s, t ∈ Servers : 
    (state[s] = Leader ∧ state[t] = Leader) ⟹ 
    (s = t ∨ currentTerm[s] ≠ currentTerm[t])

\* コミット済みエントリの不変性
CommittedEntriesNeverChange ≜
  ∀ s ∈ Servers, i ∈ 1..commitIndex[s] :
    □(log[s][i] = log'[s][i])
```

### 故障モデルの組み込み

現実的なシステムでは、様々な故障が発生します：

**1. ノード故障**：
【擬似記法】
```tla
NodeFailure(s) ≜
  ∧ state[s] ≠ Failed
  ∧ state' = [state EXCEPT ![s] = Failed]
  ∧ UNCHANGED ⟨currentTerm, votedFor, log, commitIndex, 
               nextIndex, matchIndex, messages⟩
```

**2. ネットワーク分断**：
【擬似記法】
```tla
NetworkPartition ≜
  ∃ partition ⊆ Servers :
    ∧ Cardinality(partition) > 0
    ∧ Cardinality(partition) < Cardinality(Servers)
    ∧ ∀ m ∈ messages : 
        (m.source ∈ partition ∧ m.dest ∉ partition) ∨
        (m.source ∉ partition ∧ m.dest ∈ partition) ⟹
        m ∉ messages'
```

**3. メッセージ損失**：
【擬似記法】
```tla
MessageLoss ≜
  ∃ m ∈ messages :
    ∧ messages' = messages \ {m}
    ∧ UNCHANGED ⟨currentTerm, votedFor, log, state, commitIndex, 
                 nextIndex, matchIndex⟩
```

### 活性の保証

Raftアルゴリズムの活性性質：

【擬似記法】
```tla
\* 最終的にリーダーが選出される
EventualLeaderElection ≜
  ◇(∃ s ∈ Servers : state[s] = Leader)

\* 進歩が保証される（ネットワークが安定している場合）
Progress ≜
  □(client_request ⟹ ◇committed)

\* 公平性仮定
Fairness ≜
  ∧ ∀ s ∈ Servers : WF_vars(ElectionTimeout(s))
  ∧ ∀ s ∈ Servers : WF_vars(ReceiveMessage(s))
  ∧ ∀ m ∈ MessageType : SF_vars(DeliverMessage(m))
```

### TLCによる検証

実際にTLCでRaftアルゴリズムを検証する際の設定：

【擬似記法】
```
\* Raft.cfg
CONSTANTS
  Servers = {"s1", "s2", "s3"}
  ElectionTimeout = 3
  HeartbeatInterval = 1
  MaxLogLength = 5

SPECIFICATION
  Init ∧ □[Next]_vars ∧ Fairness

INVARIANTS
  TypeInvariant
  LogMatching
  LeaderUniqueness
  CommittedEntriesNeverChange

PROPERTIES
  EventualLeaderElection
  Progress
```

この検証により、小規模なクラスターでのRaftアルゴリズムの正しさを確認できます。実際の検証では、様々な故障シナリオを組み込み、アルゴリズムの堅牢性を徹底的に確認します。

分散合意アルゴリズムのような複雑なプロトコルも、TLA+とTLCにより形式的に記述し、検証できることが、この例によって示されます。理論的な正しさと実用的な堅牢性を同時に保証することが、現代の分散システム開発には不可欠です。

---

## 章末課題

**AI利用時の提出ルール（共通）**
- AIの出力は提案として扱い、合否は検証器で判定する
- 提出物: 使用プロンプト / 生成仕様・不変条件 / 検証コマンドとログ（seed/深さ/スコープ） / 反例が出た場合の修正履歴
- 詳細なテンプレは付録D・付録Fを参照する


### 基礎理解演習1：時相論理の記法理解

以下の時相論理式を日本語で説明し、具体的なシステムでの例を挙げてください：

1. `□(resource_requested ⟹ ◇resource_granted)`
2. `◇□(system_stable)`  
3. `□◇(garbage_collection)`
4. `(critical_section_entered) ~> (critical_section_exited)`

それぞれについて：
- 論理式の意味の説明
- 実際のシステムでの具体例
- この性質が破られる状況の例

### 基礎理解演習2：状態と行動の記述

以下のシステムをTLA+の状態と行動で記述してください：

**単純な在庫管理システム**：
- 在庫数を管理する変数 `stock`
- 入荷操作：在庫を増加
- 出荷操作：在庫を減少（在庫不足時は実行不可）
- 棚卸操作：在庫数を正確な値に修正

記述すべき要素：
1. 変数宣言と型不変条件
2. 初期状態
3. 各操作の行動定義
4. Next状態述語
5. 基本的な安全性不変条件

### 実践演習1：相互排除プロトコルの設計

Peterson のアルゴリズムをTLA+で記述し、TLCで検証してください：

**要求**：
- 2つのプロセスによる相互排除
- 各プロセスは「非クリティカル」「要求中」「クリティカル」の状態を持つ
- フラグ配列とターン変数による制御

**検証すべき性質**：
1. 相互排除：2つのプロセスが同時にクリティカルセクションにいない
2. 進歩：要求があれば最終的に誰かがクリティカルセクションに入る
3. 公平性：両プロセスが交互にクリティカルセクションに入れる

### 実践演習2：生産者・消費者問題

有限バッファーを持つ生産者・消費者システムをTLA+で設計してください：

**システム構成**：
- 複数の生産者プロセス
- 複数の消費者プロセス  
- 固定サイズの共有バッファー

**制約**：
- バッファーが満杯の時は生産者は待機
- バッファーが空の時は消費者は待機
- データの順序は保持される（FIFO）

**検証事項**：
1. デッドロック不発生
2. データの損失なし
3. 生産者・消費者の公平性
4. バッファーオーバーフロー/アンダーフローの回避

### 発展演習：分散システムの設計

分散ファイルシステムの簡単版をTLA+で設計してください：

**システム要求**：
- 複数のストレージノード
- ファイルの冗長化（レプリケーション）
- クライアントからの読み書き要求
- ノード故障への耐性

**主要な操作**：
1. ファイル作成・削除
2. ファイル読み込み・書き込み
3. レプリケーション管理
4. 故障検出と回復

**検証すべき性質**：
1. **一貫性**：すべてのレプリカが最終的に同じ内容
2. **可用性**：一部のノードが故障してもサービス継続
3. **耐久性**：データの永続的な保存
4. **分断耐性**：ネットワーク分断に対する適切な処理

**設計課題**：
- 故障モデルの定義（どのような故障を想定するか）
- 一貫性モデルの選択（強一貫性 vs 結果整合性）
- 分散合意の必要性とアルゴリズムの選択
- 性能とのトレードオフの考慮

これらの演習を通じて、TLA+による分散システムの形式的設計能力を身につけ、実際のシステム開発に応用できる知識を獲得してください。特に発展演習では、CAP定理の制約の中での設計判断や、理論と実践のバランスを考慮することが重要です。
