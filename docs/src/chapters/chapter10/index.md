# 第10章：セキュリティアーキテクチャ

セキュリティは後付けでは実現できない。システムの設計段階から組み込まれ、アーキテクチャ全体に浸透していなければならない機能である。しかし、セキュリティ要件と性能・可用性・コストとの間には、常にトレードオフが存在する。

なぜネットワークセグメンテーションが必要なのか。ファイアウォールのルール順序がなぜ性能に影響するのか。暗号化処理でなぜハードウェアアクセラレーションが重要なのか。これらの疑問に答えることで、セキュリティ機能を性能劣化の要因ではなく、システムの価値を高める要素として統合することが可能となる。

## 10.1 ネットワークセグメンテーション戦略

### マイクロセグメンテーションの実装

ネットワークセグメンテーションは、ネットワークを論理的に分割し、セキュリティ境界を作り出す技術である。従来の境界型セキュリティから、内部ネットワークでも信頼できない前提に基づく防御戦略への転換を実現する。

**従来のセグメンテーションの限界**

```text
従来の3層セグメンテーション：
DMZ（非武装地帯）：Webサーバー
└─ ファイアウォール
内部ネットワーク：アプリケーションサーバー、データベース
└─ ファイアウォール  
管理ネットワーク：管理コンソール、バックアップサーバー
```

この構造の問題点：
- 内部ネットワーク内での横方向の移動（Lateral Movement）を阻止できない
- 一つの層に侵入されると、その層内のすべてのリソースが危険にさらされる
- VLANによる論理分離のみでは不十分

**マイクロセグメンテーションの実装アプローチ**

マイクロセグメンテーションは、各ワークロード間に個別のセキュリティ境界を設ける：

```text
ワークロード単位でのセグメンテーション：
┌─────────────────┐   ┌─────────────────┐
│ Web Server 1    │   │ Web Server 2    │
│ VLAN 100        │   │ VLAN 101        │ 
│ 192.168.100.10  │   │ 192.168.101.10  │
└─────────────────┘   └─────────────────┘
         │                       │
    ┌────▼────┐             ┌────▼────┐
    │FW Rules │             │FW Rules │
    └────┬────┘             └────┬────┘
         │                       │
┌────────▼──────────────────────▼─────────┐
│        Application Server               │
│        VLAN 200                         │
│        192.168.200.10                   │
└────────┬────────────────────────────────┘
         │
    ┌────▼────┐
    │FW Rules │
    └────┬────┘
         │
┌────────▼─────────┐
│   Database       │
│   VLAN 300       │
│   192.168.300.10 │
└──────────────────┘
```

**VMware NSX による実装例**

```bash
# NSX-T によるマイクロセグメンテーション設定

# セキュリティグループの作成
nsxcli -c "create security-group web-servers"
nsxcli -c "create security-group app-servers"  
nsxcli -c "create security-group db-servers"

# セキュリティポリシーの定義
nsxcli -c "create security-policy web-to-app
  source: web-servers
  destination: app-servers
  action: allow
  services: tcp/8080"

nsxcli -c "create security-policy app-to-db
  source: app-servers
  destination: db-servers  
  action: allow
  services: tcp/3306"

# すべての他の通信を拒否
nsxcli -c "create security-policy default-deny
  source: any
  destination: any
  action: drop
  priority: 1000"  # 最低優先度
```

**Linux iptables によるホストベース実装**

```bash
#!/bin/bash
# マイクロセグメンテーション設定スクリプト

# デフォルトポリシー：すべて拒否
iptables -P INPUT DROP
iptables -P FORWARD DROP
iptables -P OUTPUT DROP

# ループバックインターフェース許可
iptables -A INPUT -i lo -j ACCEPT
iptables -A OUTPUT -o lo -j ACCEPT

# SSH管理アクセス（管理ネットワークのみ）
iptables -A INPUT -s 192.168.200.0/24 -p tcp --dport 22 -j ACCEPT

# Webサーバーからアプリケーションサーバーへの通信
if [ "$SERVER_ROLE" = "web" ]; then
    iptables -A OUTPUT -d 192.168.100.10 -p tcp --dport 8080 -j ACCEPT
    iptables -A INPUT -p tcp --dport 80 -j ACCEPT
    iptables -A INPUT -p tcp --dport 443 -j ACCEPT
fi

# アプリケーションサーバーからデータベースへの通信
if [ "$SERVER_ROLE" = "app" ]; then
    iptables -A INPUT -s 192.168.10.0/24 -p tcp --dport 8080 -j ACCEPT
    iptables -A OUTPUT -d 192.168.300.10 -p tcp --dport 3306 -j ACCEPT
fi

# データベースサーバー
if [ "$SERVER_ROLE" = "db" ]; then
    iptables -A INPUT -s 192.168.100.10 -p tcp --dport 3306 -j ACCEPT
fi

# 確立済み接続の許可
iptables -A INPUT -m state --state ESTABLISHED,RELATED -j ACCEPT
iptables -A OUTPUT -m state --state ESTABLISHED,RELATED -j ACCEPT

# ルール永続化
iptables-save > /etc/iptables/rules.v4
```

**実装における性能考慮点**

```bash
# iptables の性能最適化
# 1. よく使用されるルールを上位に配置
iptables -I INPUT 1 -m state --state ESTABLISHED,RELATED -j ACCEPT

# 2. ipset を使用した効率的なIP範囲管理
ipset create web-servers hash:ip
ipset add web-servers 192.168.10.10
ipset add web-servers 192.168.10.11
iptables -A INPUT -m set --match-set web-servers src -p tcp --dport 8080 -j ACCEPT

# 3. ルール統計の監視
iptables -L -n -v
# Chain INPUT (policy DROP 0 packets, 0 bytes)
#  pkts bytes target     prot opt in     out     source     destination
# 12345  890K ACCEPT     all  --  *      *       0.0.0.0/0  0.0.0.0/0   state RELATED,ESTABLISHED
#   234   45K ACCEPT     tcp  --  *      *       192.168.200.0/24  0.0.0.0/0  tcp dpt:22

# 使用されていないルールの特定と削除
awk '$1 == "0" {print NR, $0}' < <(iptables -L -n -v --line-numbers)
```

### ゼロトラストへの移行判断

ゼロトラスト（Zero Trust）は、「何も信頼しない、すべてを検証する」という原則に基づくセキュリティモデルである。従来の境界型セキュリティからの根本的な転換を意味する。

**ゼロトラストの基本原則**

```text
従来モデル：
信頼境界内＝安全、境界外＝危険

ゼロトラストモデル：
すべてのトラフィック＝信頼できない
すべてのアクセス＝検証が必要
```

**実装アーキテクチャの段階的移行**

1. **フェーズ1：可視化とインベントリ**
   ```bash
   # ネットワークトラフィックの分析
   # ntopng による詳細な通信パターン把握
   ntopng -i eth0 -d /var/lib/ntopng -P /var/run/ntopng.pid
   
   # 通信フローの記録
   nfcapd -w -D -t 300 -l /var/cache/nfcapd
   
   # アプリケーション間通信の可視化
   nfdump -r /var/cache/nfcapd -s record/bytes -n 20
   # Date first seen    Duration Proto      Src IP Addr:Port      Dst IP Addr:Port   Bytes
   # 2024-06-18 10:00:01   0.345   TCP    192.168.10.100:45678  192.168.20.100:8080   12345
   ```

2. **フェーズ2：マイクロセグメンテーション実装**
   ```yaml
   # Kubernetes NetworkPolicy でのゼロトラスト実装
   apiVersion: networking.k8s.io/v1
   kind: NetworkPolicy
   metadata:
     name: web-app-zero-trust
   spec:
     podSelector:
       matchLabels:
         app: web-frontend
     policyTypes:
     - Ingress
     - Egress
     ingress:
     - from:
       - podSelector:
           matchLabels:
             app: load-balancer
       ports:
       - protocol: TCP
         port: 8080
     egress:
     - to:
       - podSelector:
           matchLabels:
             app: api-backend
       ports:
       - protocol: TCP
         port: 9090
     # DNS解決のみ許可
     - to: []
       ports:
       - protocol: UDP
         port: 53
   ```

3. **フェーズ3：アイデンティティベース認証**
   ```python
   # mTLS による相互認証実装
   import ssl
   import socket
   from cryptography import x509
   from cryptography.hazmat.primitives import hashes, serialization
   
   class ZeroTrustConnector:
       def __init__(self, client_cert, client_key, ca_cert):
           self.client_cert = client_cert
           self.client_key = client_key
           self.ca_cert = ca_cert
       
       def create_secure_connection(self, hostname, port):
           # SSL/TLS コンテキスト作成
           context = ssl.create_default_context()
           context.check_hostname = True
           context.verify_mode = ssl.CERT_REQUIRED
           
           # クライアント証明書設定
           context.load_cert_chain(self.client_cert, self.client_key)
           context.load_verify_locations(self.ca_cert)
           
           # 接続確立
           sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
           secure_sock = context.wrap_socket(sock, server_hostname=hostname)
           secure_sock.connect((hostname, port))
           
           # 証明書検証
           peer_cert = secure_sock.getpeercert(binary_form=True)
           cert = x509.load_der_x509_certificate(peer_cert)
           
           # アプリケーション固有の検証
           if not self.verify_application_identity(cert):
               raise ssl.SSLError("Application identity verification failed")
           
           return secure_sock
       
       def verify_application_identity(self, cert):
           # SAN (Subject Alternative Name) から役割を確認
           for extension in cert.extensions:
               if extension.oid._name == 'subjectAltName':
                   for name in extension.value:
                       if name.value.startswith('URI:spiffe://'):
                           return self.validate_spiffe_id(name.value)
           return False
   ```

**性能影響の定量化**

```bash
# ゼロトラスト実装前後の性能測定

# 暗号化なし（ベースライン）
wrk -t12 -c400 -d30s http://api.internal.com/health
# Running 30s test @ http://api.internal.com/health
# 12 threads and 400 connections
# Requests/sec: 45000.12
# Transfer/sec: 5.23MB

# mTLS実装後
wrk -t12 -c400 -d30s --cert client.crt --key client.key https://api.internal.com/health
# Running 30s test @ https://api.internal.com/health  
# 12 threads and 400 connections
# Requests/sec: 38000.24  # 約15%低下
# Transfer/sec: 4.42MB

# CPU使用率の比較
# 暗号化なし：15% CPU使用率
# mTLS実装：28% CPU使用率
```

**移行判断のフレームワーク**

```text
ゼロトラスト移行の判断基準：

技術的準備度：
✓ 現在のネットワーク通信パターンの完全な把握
✓ アプリケーション間依存関係の文書化
✓ 証明書管理インフラの整備
✓ 監視・ログ基盤の構築

組織的準備度：
✓ セキュリティチームと開発チームの連携体制
✓ インシデント対応プロセスの整備
✓ 段階的移行のためのリソース確保

リスク・ベネフィット分析：
- セキュリティリスクの定量化
- 実装コストの算出
- 運用コストの継続評価
- 業務影響の最小化計画
```

## 10.2 ファイアウォール実装の最適化

### ステートフル検査のオーバーヘッド

ステートフル検査は、現代ファイアウォールの核心機能である。しかし、その実装はシステムリソースを消費し、通信遅延を増加させる。最適な設定と運用により、セキュリティ機能と性能のバランスを取ることが重要である。

**ステートフル検査の動作原理**

```text
ステートフル検査の処理フロー：

1. パケット受信
   ↓
2. 既存コネクション状態テーブル検索
   ↓
3a. 既存コネクション → 状態確認後転送
   ↓
3b. 新規コネクション → ルール評価
   ↓  
4. 許可の場合 → 状態テーブルに登録 → 転送
   拒否の場合 → ドロップ/ログ記録
```

**状態テーブルの実装とメモリ消費**

```bash
# Linux netfilter の接続追跡テーブル確認
cat /proc/net/nf_conntrack | head -5
# ipv4 2 tcp 6 431999 ESTABLISHED src=192.168.1.100 dst=203.0.113.10 sport=45678 dport=80
# ipv4 2 tcp 6 86397 TIME_WAIT src=192.168.1.101 dst=203.0.113.20 sport=52341 dport=443

# 接続追跡統計
cat /proc/net/nf_conntrack_count
# 1247  # 現在の追跡中接続数

cat /proc/sys/net/netfilter/nf_conntrack_max
# 65536  # 最大追跡可能接続数

# メモリ使用量の計算
# 1接続 ≈ 300バイト（構造体 + メタデータ）
# 65536接続 ≈ 19.7MB
```

**ステートフル検査の性能測定**

```bash
# iptables でのパフォーマンステスト
#!/bin/bash

# テスト用ルール設定
iptables -F
iptables -A INPUT -m state --state ESTABLISHED,RELATED -j ACCEPT
iptables -A INPUT -p tcp --dport 80 -j ACCEPT
iptables -A INPUT -j DROP

# 同時接続数テスト
for i in {1..1000}; do
    curl -s http://localhost/ &
done
wait

# CPU使用率とメモリ使用量測定
top -b -n1 | grep kthreadd  # カーネルスレッドCPU使用率
echo "Memory usage: $(cat /proc/meminfo | grep -E '(MemTotal|MemAvailable)')"

# 接続追跡のオーバーヘッド測定
echo "Conntrack entries: $(cat /proc/net/nf_conntrack_count)"
echo "Conntrack memory: $(cat /proc/slabinfo | grep nf_conntrack)"
# nf_conntrack        1247   1280    304   13    1 : tunables  0  0  0
```

**最適化戦略**

1. **接続追跡の選択的無効化**
   ```bash
   # 高トラフィックサービスで接続追跡を無効化
   iptables -t raw -A PREROUTING -p tcp --dport 80 -j NOTRACK
   iptables -t raw -A OUTPUT -p tcp --sport 80 -j NOTRACK
   
   # 対応するfilterルール
   iptables -A INPUT -p tcp --dport 80 -j ACCEPT
   iptables -A OUTPUT -p tcp --sport 80 -j ACCEPT
   ```

2. **ハッシュテーブルサイズの調整**
   ```bash
   # conntrack ハッシュテーブルサイズ増加
   echo 'net.netfilter.nf_conntrack_buckets = 32768' >> /etc/sysctl.conf
   echo 'net.netfilter.nf_conntrack_max = 131072' >> /etc/sysctl.conf
   
   # タイムアウト値の調整
   echo 'net.netfilter.nf_conntrack_tcp_timeout_established = 1800' >> /etc/sysctl.conf
   echo 'net.netfilter.nf_conntrack_tcp_timeout_time_wait = 30' >> /etc/sysctl.conf
   
   sysctl -p
   ```

3. **専用ハードウェアの活用**
   ```bash
   # Intel DPDK による高速パケット処理
   # ユーザー空間での直接パケット処理
   
   # 設定例（概念的）
   # CPU コア専有
   isolcpus=2,3,4,5
   
   # 大きなページサイズ設定
   echo 1024 > /sys/kernel/mm/hugepages/hugepages-2048kB/nr_hugepages
   
   # DPDK アプリケーション起動
   ./dpdk-firewall -c 0x3c -n 4 -- -p 0x3 --config="(0,0,2),(1,0,3)" --rule-file=rules.cfg
   ```

### ルール順序による性能影響

ファイアウォールルールの評価は、通常、上から順番に行われる。ルールの順序は、パフォーマンスに直接的な影響を与える。

**ルール評価のコスト分析**

```bash
# iptables ルール評価時間の測定
#!/bin/bash

# 測定用のルールセット作成
iptables -F INPUT

# 頻繁にマッチするルールを下位に配置（悪い例）
for i in {1..100}; do
    iptables -A INPUT -s 10.0.0.$i -j DROP
done
iptables -A INPUT -p tcp --dport 22 -j ACCEPT  # SSH（頻繁なアクセス）

# パフォーマンス測定
time for i in {1..1000}; do
    ssh -o ConnectTimeout=1 localhost echo test 2>/dev/null
done

# 結果例（悪い順序）：
# real    0m45.123s
# user    0m12.456s  
# sys     0m8.789s

# ルール順序を最適化
iptables -F INPUT
iptables -A INPUT -p tcp --dport 22 -j ACCEPT  # 頻繁なルールを上位に
for i in {1..100}; do
    iptables -A INPUT -s 10.0.0.$i -j DROP
done

# 再測定
time for i in {1..1000}; do
    ssh -o ConnectTimeout=1 localhost echo test 2>/dev/null
done

# 結果例（最適化後）：
# real    0m15.234s
# user    0m8.123s
# sys     0m3.456s

# 約3倍の性能向上
```

**最適化のベストプラクティス**

1. **頻度ベース順序付け**
   ```bash
   # トラフィック分析によるルール使用頻度調査
   iptables -L INPUT -n -v --line-numbers
   # Chain INPUT (policy ACCEPT 0 packets, 0 bytes)
   # num   pkts bytes target     prot opt source     destination
   # 1    45678  12M ACCEPT     tcp  --  0.0.0.0/0  0.0.0.0/0   tcp dpt:80
   # 2     1234  345K ACCEPT    tcp  --  0.0.0.0/0  0.0.0.0/0   tcp dpt:443
   # 3        0     0 DROP      all  --  10.0.0.1   0.0.0.0/0
   
   # 使用されていないルール（pkts=0）を削除または下位に移動
   ```

2. **効率的な条件指定**
   ```bash
   # 非効率な例：複数のルールで同一ポートを指定
   iptables -A INPUT -s 192.168.1.0/24 -p tcp --dport 80 -j ACCEPT
   iptables -A INPUT -s 192.168.2.0/24 -p tcp --dport 80 -j ACCEPT
   iptables -A INPUT -s 192.168.3.0/24 -p tcp --dport 80 -j ACCEPT
   
   # 効率的：ipset を使用した一括処理
   ipset create allowed-networks hash:net
   ipset add allowed-networks 192.168.1.0/24
   ipset add allowed-networks 192.168.2.0/24
   ipset add allowed-networks 192.168.3.0/24
   iptables -A INPUT -m set --match-set allowed-networks src -p tcp --dport 80 -j ACCEPT
   ```

3. **ルール統合による最適化**
   ```bash
   # 統合前（6ルール）
   iptables -A INPUT -p tcp --dport 80 -j ACCEPT
   iptables -A INPUT -p tcp --dport 443 -j ACCEPT
   iptables -A INPUT -p tcp --dport 8080 -j ACCEPT
   iptables -A INPUT -p tcp --dport 8443 -j ACCEPT
   iptables -A INPUT -p tcp --dport 9000 -j ACCEPT
   iptables -A INPUT -p tcp --dport 9443 -j ACCEPT
   
   # 統合後（1ルール）
   iptables -A INPUT -p tcp -m multiport --dports 80,443,8080,8443,9000,9443 -j ACCEPT
   ```

**自動最適化スクリプト**

```bash
#!/bin/bash
# iptables ルール最適化スクリプト

optimize_iptables() {
    local chain=$1
    
    # 現在のルール統計取得
    iptables -L $chain -n -v --line-numbers > /tmp/rules_stats.txt
    
    # 使用頻度によるソート（pktカラムでソート）
    tail -n +3 /tmp/rules_stats.txt | sort -k2 -nr > /tmp/sorted_rules.txt
    
    echo "=== ルール使用統計 ==="
    cat /tmp/sorted_rules.txt
    
    # 使用されていないルールの特定
    echo "=== 未使用ルール ==="
    awk '$2 == "0" {print "Line " $1 ": " $0}' /tmp/sorted_rules.txt
    
    # 統合可能なルールの検出
    echo "=== 統合可能なルール ==="
    awk '{
        if ($8 == "tcp" && $10 ~ /dpt:/) {
            split($10, port, ":")
            ports[port[2]]++
            lines[port[2]] = lines[port[2]] " " $1
        }
    } END {
        for (p in ports) {
            if (ports[p] > 1) {
                print "Port " p " appears in lines:" lines[p]
            }
        }
    }' /tmp/sorted_rules.txt
}

# チェーン別最適化実行
optimize_iptables INPUT
optimize_iptables FORWARD
optimize_iptables OUTPUT
```

## 10.3 認証・認可システムの実装

### PAMアーキテクチャの拡張性

Pluggable Authentication Modules（PAM）は、Unix系システムにおいて認証機能をモジュール化し、柔軟な認証方式を実現するフレームワークである。企業環境での複雑な認証要件に対応するため、PAMの設計原理と拡張方法を理解することが重要である。

**PAMの基本アーキテクチャ**

```text
PAMの4つの管理グループ：

1. auth（認証）：ユーザーの身元確認
2. account（アカウント）：アカウントの有効性確認
3. password（パスワード）：パスワード変更処理
4. session（セッション）：セッション開始・終了処理
```

**PAM設定の実例**

```bash
# /etc/pam.d/sshd の例
# 複数要素認証（MFA）の実装

# Google Authenticator による2段階認証
auth       required     pam_google_authenticator.so

# LDAP認証
auth       sufficient   pam_ldap.so
auth       sufficient   pam_unix.so try_first_pass

# Kerberos認証
auth       sufficient   pam_krb5.so

# 認証失敗時のfallback
auth       required     pam_deny.so

# アカウント管理
account    required     pam_nologin.so
account    sufficient   pam_ldap.so
account    required     pam_unix.so

# セッション管理
session    required     pam_selinux.so close
session    required     pam_loginuid.so
session    optional     pam_console.so
session    required     pam_selinux.so open
```

**カスタムPAMモジュールの実装**

```c
// custom_auth.c - 独自認証モジュール
#include <security/pam_modules.h>
#include <security/pam_ext.h>
#include <syslog.h>
#include <string.h>

// 認証処理の実装
PAM_EXTERN int pam_sm_authenticate(pam_handle_t *pamh, int flags,
                                   int argc, const char **argv) {
    const char *username;
    const char *password;
    
    // ユーザー名の取得
    int retval = pam_get_user(pamh, &username, "Username: ");
    if (retval != PAM_SUCCESS) {
        return retval;
    }
    
    // パスワードの取得
    retval = pam_get_authtok(pamh, PAM_AUTHTOK, &password, "Password: ");
    if (retval != PAM_SUCCESS) {
        return retval;
    }
    
    // カスタム認証ロジック
    if (custom_validate_user(username, password)) {
        pam_syslog(pamh, LOG_INFO, "Custom authentication successful for %s", username);
        return PAM_SUCCESS;
    } else {
        pam_syslog(pamh, LOG_WARNING, "Custom authentication failed for %s", username);
        return PAM_AUTH_ERR;
    }
}

// アカウント確認の実装
PAM_EXTERN int pam_sm_acct_mgmt(pam_handle_t *pamh, int flags,
                                int argc, const char **argv) {
    const char *username;
    pam_get_user(pamh, &username, NULL);
    
    // アカウント状態確認
    if (is_account_locked(username)) {
        return PAM_ACCT_EXPIRED;
    }
    
    if (password_expired(username)) {
        return PAM_NEW_AUTHTOK_REQD;
    }
    
    return PAM_SUCCESS;
}

// 独自認証ロジック
int custom_validate_user(const char *username, const char *password) {
    // データベース接続
    MYSQL *conn = mysql_init(NULL);
    mysql_real_connect(conn, "localhost", "auth_user", "auth_pass", 
                       "authentication", 0, NULL, 0);
    
    // SQL準備
    char query[512];
    snprintf(query, sizeof(query), 
             "SELECT password_hash FROM users WHERE username='%s' AND active=1",
             username);
    
    // クエリ実行
    if (mysql_query(conn, query)) {
        mysql_close(conn);
        return 0;
    }
    
    MYSQL_RES *result = mysql_store_result(conn);
    MYSQL_ROW row = mysql_fetch_row(result);
    
    if (row) {
        // パスワードハッシュ検証
        int valid = verify_password(password, row[0]);
        mysql_free_result(result);
        mysql_close(conn);
        return valid;
    }
    
    mysql_free_result(result);
    mysql_close(conn);
    return 0;
}
```

**コンパイルと配置**

```bash
# PAMモジュールのコンパイル
gcc -fPIC -shared -o pam_custom_auth.so custom_auth.c -lpam -lmysqlclient

# 適切な場所に配置
sudo cp pam_custom_auth.so /lib/security/
sudo chmod 755 /lib/security/pam_custom_auth.so

# PAM設定での使用
echo "auth    sufficient    pam_custom_auth.so" >> /etc/pam.d/custom-service
```

**高度なPAM設定例**

```bash
# /etc/pam.d/enterprise-login
# 企業向け多段階認証設定

# 証明書ベース認証（第1段階）
auth    [success=2 default=ignore]    pam_pkcs11.so

# LDAP認証（第2段階）
auth    [success=1 default=ignore]    pam_ldap.so use_first_pass

# ローカル認証（fallback）
auth    requisite                     pam_unix.so nullok_secure

# ワンタイムパスワード（第3段階）
auth    required                      pam_oath.so usersfile=/etc/users.oath

# 失敗ログ記録
auth    required                      pam_warn.so

# アカウント制限
account required    pam_access.so
account required    pam_time.so
account required    pam_unix.so

# セッション管理
session required    pam_limits.so
session required    pam_unix.so
session optional    pam_systemd.so
```

### RBACの実装とスケーラビリティ

Role-Based Access Control（RBAC）は、ユーザーに役割（Role）を割り当て、役割に権限を関連付けることで、アクセス制御を実現する手法である。大規模組織での権限管理の複雑性を軽減する。

**RBAC実装のデータモデル**

```sql
-- RBAC データベーススキーマ設計

-- ユーザーテーブル
CREATE TABLE users (
    id INT PRIMARY KEY AUTO_INCREMENT,
    username VARCHAR(50) UNIQUE NOT NULL,
    email VARCHAR(100) UNIQUE NOT NULL,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    active BOOLEAN DEFAULT TRUE
);

-- 役割テーブル
CREATE TABLE roles (
    id INT PRIMARY KEY AUTO_INCREMENT,
    name VARCHAR(50) UNIQUE NOT NULL,
    description TEXT,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

-- 権限テーブル
CREATE TABLE permissions (
    id INT PRIMARY KEY AUTO_INCREMENT,
    name VARCHAR(100) UNIQUE NOT NULL,
    resource VARCHAR(50) NOT NULL,
    action VARCHAR(50) NOT NULL,
    description TEXT
);

-- ユーザー・役割関連テーブル
CREATE TABLE user_roles (
    user_id INT,
    role_id INT,
    assigned_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    assigned_by INT,
    PRIMARY KEY (user_id, role_id),
    FOREIGN KEY (user_id) REFERENCES users(id),
    FOREIGN KEY (role_id) REFERENCES roles(id),
    FOREIGN KEY (assigned_by) REFERENCES users(id)
);

-- 役割・権限関連テーブル
CREATE TABLE role_permissions (
    role_id INT,
    permission_id INT,
    granted_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    granted_by INT,
    PRIMARY KEY (role_id, permission_id),
    FOREIGN KEY (role_id) REFERENCES roles(id),
    FOREIGN KEY (permission_id) REFERENCES permissions(id),
    FOREIGN KEY (granted_by) REFERENCES users(id)
);

-- 階層的役割管理（役割継承）
CREATE TABLE role_hierarchy (
    parent_role_id INT,
    child_role_id INT,
    PRIMARY KEY (parent_role_id, child_role_id),
    FOREIGN KEY (parent_role_id) REFERENCES roles(id),
    FOREIGN KEY (child_role_id) REFERENCES roles(id)
);
```

**RBAC権限チェック機能の実装**

```python
# rbac.py - RBAC実装
import hashlib
import time
from typing import List, Set, Optional
from dataclasses import dataclass
from functools import lru_cache

@dataclass
class Permission:
    resource: str
    action: str
    
    def __str__(self):
        return f"{self.resource}:{self.action}"

@dataclass  
class Role:
    name: str
    permissions: Set[Permission]
    inherited_roles: Set[str] = None

class RBACManager:
    def __init__(self, db_connection):
        self.db = db_connection
        self._cache = {}
        self._cache_ttl = 300  # 5分キャッシュ
    
    @lru_cache(maxsize=1000)
    def get_user_permissions(self, username: str) -> Set[Permission]:
        """ユーザーの全権限を取得（継承込み）"""
        cache_key = f"user_perms:{username}"
        cached = self._get_from_cache(cache_key)
        if cached:
            return cached
        
        # ユーザーの直接割り当て役割取得
        user_roles = self._get_user_roles(username)
        all_permissions = set()
        
        # 各役割の権限を収集（継承含む）
        for role_name in user_roles:
            role_permissions = self._get_role_permissions_recursive(role_name)
            all_permissions.update(role_permissions)
        
        # キャッシュに保存
        self._set_cache(cache_key, all_permissions)
        return all_permissions
    
    def _get_role_permissions_recursive(self, role_name: str) -> Set[Permission]:
        """役割の権限を再帰的に取得（継承込み）"""
        permissions = set()
        
        # 直接権限の取得
        query = """
        SELECT p.resource, p.action 
        FROM permissions p
        JOIN role_permissions rp ON p.id = rp.permission_id
        JOIN roles r ON rp.role_id = r.id
        WHERE r.name = %s
        """
        
        cursor = self.db.cursor()
        cursor.execute(query, (role_name,))
        
        for resource, action in cursor.fetchall():
            permissions.add(Permission(resource, action))
        
        # 継承役割の権限取得
        inherited_query = """
        SELECT r2.name
        FROM roles r1
        JOIN role_hierarchy rh ON r1.id = rh.child_role_id
        JOIN roles r2 ON rh.parent_role_id = r2.id
        WHERE r1.name = %s
        """
        
        cursor.execute(inherited_query, (role_name,))
        for (inherited_role,) in cursor.fetchall():
            inherited_permissions = self._get_role_permissions_recursive(inherited_role)
            permissions.update(inherited_permissions)
        
        cursor.close()
        return permissions
    
    def check_permission(self, username: str, resource: str, action: str) -> bool:
        """権限チェック"""
        required_permission = Permission(resource, action)
        user_permissions = self.get_user_permissions(username)
        
        # 完全一致チェック
        if required_permission in user_permissions:
            return True
        
        # ワイルドカードチェック
        wildcard_permission = Permission(resource, "*")
        if wildcard_permission in user_permissions:
            return True
        
        resource_wildcard = Permission("*", action)
        if resource_wildcard in user_permissions:
            return True
        
        return False
    
    def _get_from_cache(self, key: str) -> Optional[Set[Permission]]:
        if key in self._cache:
            value, timestamp = self._cache[key]
            if time.time() - timestamp < self._cache_ttl:
                return value
            else:
                del self._cache[key]
        return None
    
    def _set_cache(self, key: str, value: Set[Permission]):
        self._cache[key] = (value, time.time())

# デコレータによる権限チェック
def require_permission(resource: str, action: str):
    def decorator(func):
        def wrapper(*args, **kwargs):
            # 現在のユーザー情報取得（実装依存）
            current_user = get_current_user()
            
            rbac = RBACManager(get_db_connection())
            if not rbac.check_permission(current_user, resource, action):
                raise PermissionError(f"Access denied: {resource}:{action}")
            
            return func(*args, **kwargs)
        return wrapper
    return decorator

# 使用例
@require_permission("user_management", "create")
def create_user(username: str, email: str):
    # ユーザー作成処理
    pass

@require_permission("financial_data", "read")  
def get_financial_report():
    # 財務データ取得処理
    pass
```

**スケーラビリティ対策**

```python
# 大規模環境向けRBAC最適化

class ScalableRBACManager(RBACManager):
    def __init__(self, db_connection, redis_client=None):
        super().__init__(db_connection)
        self.redis = redis_client
        self.batch_size = 1000
        
    def bulk_permission_check(self, checks: List[tuple]) -> List[bool]:
        """バッチ権限チェック"""
        results = []
        
        # ユーザーごとにグループ化
        user_checks = {}
        for i, (username, resource, action) in enumerate(checks):
            if username not in user_checks:
                user_checks[username] = []
            user_checks[username].append((i, resource, action))
        
        # ユーザーごとに権限を一括取得
        for username, user_check_list in user_checks.items():
            user_permissions = self.get_user_permissions(username)
            
            for original_index, resource, action in user_check_list:
                result = self._check_permission_from_set(
                    user_permissions, resource, action
                )
                results.append((original_index, result))
        
        # 元の順序で結果を返す
        results.sort(key=lambda x: x[0])
        return [result for _, result in results]
    
    def preload_permissions(self, usernames: List[str]):
        """権限の事前ロード"""
        if not self.redis:
            return
        
        for username in usernames:
            permissions = self.get_user_permissions(username)
            cache_key = f"rbac:user:{username}"
            
            # Redis に JSON 形式で保存
            import json
            permissions_data = [
                {"resource": p.resource, "action": p.action} 
                for p in permissions
            ]
            self.redis.setex(
                cache_key, 
                300,  # 5分TTL
                json.dumps(permissions_data)
            )
```

## 10.4 暗号化実装の実践的課題

### ハードウェアアクセラレーションの活用

暗号化処理は計算集約的であり、CPUリソースを大量に消費する。現代のプロセッサが提供するハードウェア支援機能を活用することで、暗号化性能を大幅に向上させることができる。

**AES-NI（Advanced Encryption Standard New Instructions）の実装**

```c
// aes_hardware.c - AES-NI を使用した高速暗号化
#include <wmmintrin.h>
#include <emmintrin.h>
#include <smmintrin.h>

// AES-128 暗号化の実装
void aes128_encrypt_block(const uint8_t *plaintext, 
                         const uint8_t *key, 
                         uint8_t *ciphertext) {
    __m128i block, round_key;
    __m128i key_schedule[11];
    
    // 鍵展開
    aes128_key_expansion(key, key_schedule);
    
    // 平文をSSEレジスタにロード
    block = _mm_loadu_si128((__m128i*)plaintext);
    
    // 初期ラウンドキー加算
    block = _mm_xor_si128(block, key_schedule[0]);
    
    // 9ラウンドの暗号化
    for (int i = 1; i < 10; i++) {
        block = _mm_aesenc_si128(block, key_schedule[i]);
    }
    
    // 最終ラウンド
    block = _mm_aesenclast_si128(block, key_schedule[10]);
    
    // 暗号文を出力
    _mm_storeu_si128((__m128i*)ciphertext, block);
}

// 鍵展開の実装
void aes128_key_expansion(const uint8_t *key, __m128i *key_schedule) {
    __m128i temp1, temp2;
    __m128i *Key_Schedule = (__m128i*)key_schedule;
    
    temp1 = _mm_loadu_si128((__m128i*)key);
    Key_Schedule[0] = temp1;
    
    // ラウンド1
    temp2 = _mm_aeskeygenassist_si128(temp1, 0x1);
    temp1 = AES_128_ASSIST(temp1, temp2);
    Key_Schedule[1] = temp1;
    
    // ラウンド2-10（省略：実際の実装では全ラウンド必要）
    // ... 各ラウンドでAESKEYGENASSIST命令を使用
}

// 性能比較関数
void performance_benchmark() {
    uint8_t plaintext[16] = {0};
    uint8_t key[16] = {0};
    uint8_t ciphertext[16];
    
    clock_t start, end;
    const int iterations = 1000000;
    
    // ソフトウェア実装の測定
    start = clock();
    for (int i = 0; i < iterations; i++) {
        aes128_encrypt_software(plaintext, key, ciphertext);
    }
    end = clock();
    double software_time = ((double)(end - start)) / CLOCKS_PER_SEC;
    
    // ハードウェア実装の測定
    start = clock();
    for (int i = 0; i < iterations; i++) {
        aes128_encrypt_block(plaintext, key, ciphertext);
    }
    end = clock();
    double hardware_time = ((double)(end - start)) / CLOCKS_PER_SEC;
    
    printf("Software AES: %.2f seconds\n", software_time);
    printf("Hardware AES: %.2f seconds\n", hardware_time);
    printf("Speedup: %.2fx\n", software_time / hardware_time);
}
```

**OpenSSLでのハードウェアアクセラレーション有効化**

```bash
# OpenSSL でのAES-NI対応確認
openssl version -a | grep -i aes
# OPENSSLDIR: "/etc/ssl"
# ENGINESDIR: "/usr/lib/x86_64-linux-gnu/engines-1.1"
# compiler: gcc -fPIC -pthread -m64 -Wa,--noexecstack -maes -msse2

# AES-NI 対応ベンチマーク
openssl speed aes-128-cbc
# AES-128-CBC without hardware acceleration:
# The 'aes' engine (aes asm) was given.
# type        16 bytes    64 bytes   256 bytes  1024 bytes  8192 bytes 16384 bytes
# aes-128-cbc  345678k    890123k   1234567k   1456789k   1567890k   1598765k

# CPU機能確認
grep -m1 -o aes /proc/cpuinfo
# aes

# AES-NI 使用状況の確認
# Intel製CPUの場合
cpuid | grep AES
# AES instruction                         = true
```

**TLS/SSL通信での実装**

```python
# Python での高速暗号化実装
import ssl
import socket
from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes
from cryptography.hazmat.primitives.ciphers.aead import AESGCM
from cryptography.hazmat.backends import default_backend
import time

class HighPerformanceTLS:
    def __init__(self):
        # ハードウェアアクセラレーション対応の確認
        self.backend = default_backend()
        self.cipher_suites = [
            'ECDHE-RSA-AES256-GCM-SHA384',
            'ECDHE-RSA-AES128-GCM-SHA256', 
            'AES256-GCM-SHA384',
            'AES128-GCM-SHA256'
        ]
    
    def create_ssl_context(self):
        """最適化されたSSLコンテキスト作成"""
        context = ssl.create_default_context()
        
        # 高速な暗号スイートを優先
        context.set_ciphers(':'.join(self.cipher_suites))
        
        # セッション再利用の有効化
        context.set_session_cache_mode(ssl.SESS_CACHE_CLIENT)
        
        # OCSP Stapling の有効化
        context.check_hostname = True
        context.verify_mode = ssl.CERT_REQUIRED
        
        return context
    
    def benchmark_encryption(self):
        """暗号化性能測定"""
        data = b'A' * 1024 * 1024  # 1MB
        key = AESGCM.generate_key(bit_length=256)
        aesgcm = AESGCM(key)
        nonce = b'0' * 12
        
        # AES-GCM暗号化測定
        start_time = time.time()
        iterations = 100
        
        for _ in range(iterations):
            encrypted = aesgcm.encrypt(nonce, data, None)
        
        end_time = time.time()
        total_data = len(data) * iterations
        throughput = total_data / (end_time - start_time) / (1024 * 1024)
        
        print(f"AES-GCM Throughput: {throughput:.2f} MB/s")
        return throughput

# TLS接続での性能測定
def measure_tls_performance():
    context = HighPerformanceTLS().create_ssl_context()
    
    # 接続確立時間測定
    start_time = time.time()
    
    sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    ssl_sock = context.wrap_socket(sock, server_hostname='example.com')
    ssl_sock.connect(('example.com', 443))
    
    handshake_time = time.time() - start_time
    
    # データ転送速度測定
    request = b'GET / HTTP/1.1\r\nHost: example.com\r\n\r\n'
    
    start_time = time.time()
    ssl_sock.send(request)
    response = ssl_sock.recv(4096)
    transfer_time = time.time() - start_time
    
    ssl_sock.close()
    
    print(f"TLS Handshake Time: {handshake_time:.3f}s")
    print(f"Data Transfer Time: {transfer_time:.3f}s")
    print(f"Cipher Suite: {ssl_sock.cipher()}")
```

### 鍵管理の自動化戦略

暗号化システムにおいて、鍵管理は最も重要かつ複雑な要素である。適切な鍵管理の自動化により、セキュリティリスクを軽減し、運用負荷を削減できる。

**HashiCorp Vault による鍵管理**

```bash
# Vault サーバーの設定
# /etc/vault/vault.hcl
storage "consul" {
  address = "127.0.0.1:8500"
  path    = "vault/"
}

listener "tcp" {
  address = "0.0.0.0:8200"
  tls_cert_file = "/etc/vault/tls/vault.crt"
  tls_key_file  = "/etc/vault/tls/vault.key"
}

api_addr = "https://vault.example.com:8200"
cluster_addr = "https://vault.example.com:8201"
ui = true

# 高可用性設定
cluster_name = "vault-prod"
max_lease_ttl = "87600h"
default_lease_ttl = "8760h"

# Vault 初期化と設定
vault operator init -key-shares=5 -key-threshold=3

# データベース認証情報の動的生成
vault secrets enable database
vault write database/config/mysql \
    plugin_name=mysql-database-plugin \
    connection_url="{{username}}:{{password}}@tcp(localhost:3306)/" \
    allowed_roles="readonly,readwrite" \
    username="vault-admin" \
    password="vault-password"

# ロール定義
vault write database/roles/readonly \
    db_name=mysql \
    creation_statements="CREATE USER '{{name}}'@'%' IDENTIFIED BY '{{password}}';GRANT SELECT ON *.* TO '{{name}}'@'%';" \
    default_ttl="1h" \
    max_ttl="24h"

vault write database/roles/readwrite \
    db_name=mysql \
    creation_statements="CREATE USER '{{name}}'@'%' IDENTIFIED BY '{{password}}';GRANT ALL PRIVILEGES ON app.* TO '{{name}}'@'%';" \
    default_ttl="30m" \
    max_ttl="2h"
```

**自動鍵ローテーション実装**

```python
# key_rotation.py - 自動鍵ローテーションシステム
import hvac
import schedule
import time
import logging
from datetime import datetime, timedelta
import mysql.connector
import json

class AutoKeyRotation:
    def __init__(self, vault_url, vault_token):
        self.vault_client = hvac.Client(url=vault_url, token=vault_token)
        self.logger = self._setup_logging()
        
    def _setup_logging(self):
        logging.basicConfig(
            level=logging.INFO,
            format='%(asctime)s - %(levelname)s - %(message)s',
            handlers=[
                logging.FileHandler('/var/log/key-rotation.log'),
                logging.StreamHandler()
            ]
        )
        return logging.getLogger(__name__)
    
    def rotate_database_credentials(self):
        """データベース認証情報のローテーション"""
        try:
            # 現在の認証情報取得
            current_creds = self.vault_client.read('database/creds/readwrite')
            
            if not current_creds:
                self.logger.error("Failed to retrieve current credentials")
                return False
            
            old_username = current_creds['data']['username']
            old_password = current_creds['data']['password']
            
            # 新しい認証情報生成
            new_creds = self.vault_client.read('database/creds/readwrite')
            new_username = new_creds['data']['username']
            new_password = new_creds['data']['password']
            
            # アプリケーション設定更新
            self._update_application_config(new_username, new_password)
            
            # アプリケーション再起動
            self._restart_applications()
            
            # 動作確認
            if self._verify_database_connection(new_username, new_password):
                self.logger.info(f"Successfully rotated database credentials")
                return True
            else:
                self.logger.error("Database connection verification failed")
                return False
                
        except Exception as e:
            self.logger.error(f"Database credential rotation failed: {str(e)}")
            return False
    
    def rotate_encryption_keys(self):
        """暗号化キーのローテーション"""
        try:
            # Transit シークレットエンジン使用
            key_name = "application-key"
            
            # 新しいキーバージョン作成
            self.vault_client.write(f'transit/keys/{key_name}/rotate')
            
            # キー情報取得
            key_info = self.vault_client.read(f'transit/keys/{key_name}')
            latest_version = key_info['data']['latest_version']
            
            self.logger.info(f"Rotated encryption key to version {latest_version}")
            
            # 古いデータの再暗号化（バックグラウンド処理）
            self._schedule_reencryption(key_name, latest_version)
            
            return True
            
        except Exception as e:
            self.logger.error(f"Encryption key rotation failed: {str(e)}")
            return False
    
    def _update_application_config(self, username, password):
        """アプリケーション設定の更新"""
        config = {
            'database': {
                'username': username,
                'password': password,
                'host': 'localhost',
                'port': 3306,
                'database': 'app'
            }
        }
        
        with open('/etc/app/database.json', 'w') as f:
            json.dump(config, f, indent=2)
    
    def _restart_applications(self):
        """アプリケーションの再起動"""
        import subprocess
        try:
            subprocess.run(['systemctl', 'reload', 'webapp'], check=True)
            self.logger.info("Application reloaded successfully")
        except subprocess.CalledProcessError as e:
            self.logger.error(f"Application reload failed: {str(e)}")
    
    def _verify_database_connection(self, username, password):
        """データベース接続確認"""
        try:
            conn = mysql.connector.connect(
                host='localhost',
                user=username,
                password=password,
                database='app'
            )
            cursor = conn.cursor()
            cursor.execute("SELECT 1")
            cursor.fetchone()
            conn.close()
            return True
        except Exception:
            return False
    
    def _schedule_reencryption(self, key_name, new_version):
        """古いデータの再暗号化スケジューリング"""
        # 実際の実装では、キューシステム（RabbitMQ、Redis等）を使用
        self.logger.info(f"Scheduled reencryption with key version {new_version}")

# スケジューラー設定
def setup_rotation_schedule():
    rotator = AutoKeyRotation(
        vault_url='https://vault.example.com:8200',
        vault_token='hvs.CAESIG...'  # 実際の運用では適切な認証方法を使用
    )
    
    # データベース認証情報：毎日午前2時にローテーション
    schedule.every().day.at("02:00").do(rotator.rotate_database_credentials)
    
    # 暗号化キー：毎週日曜日午前3時にローテーション
    schedule.every().sunday.at("03:00").do(rotator.rotate_encryption_keys)
    
    # 監視ループ
    while True:
        schedule.run_pending()
        time.sleep(60)

if __name__ == "__main__":
    setup_rotation_schedule()
```

**PKI（Public Key Infrastructure）の自動化**

```bash
# Vault PKI エンジンの設定
vault secrets enable pki
vault secrets tune -max-lease-ttl=87600h pki

# ルートCA作成
vault write pki/root/generate/internal \
    common_name="Example Inc Root CA" \
    ttl=87600h

# 中間CA設定
vault secrets enable -path=pki_int pki
vault secrets tune -max-lease-ttl=43800h pki_int

# 中間CA CSR生成
vault write -format=json pki_int/intermediate/generate/internal \
    common_name="Example Inc Intermediate CA" \
    | jq -r '.data.csr' > pki_intermediate.csr

# ルートCAで中間CAに署名
vault write -format=json pki/root/sign-intermediate \
    csr=@pki_intermediate.csr \
    format=pem_bundle \
    ttl=43800h \
    | jq -r '.data.certificate' > intermediate.cert.pem

# 中間CA証明書設定
vault write pki_int/intermediate/set-signed \
    certificate=@intermediate.cert.pem

# 証明書発行ロール作成
vault write pki_int/roles/example-dot-com \
    allowed_domains="example.com" \
    allow_subdomains=true \
    max_ttl="720h"

# 自動証明書発行スクリプト
cat > /usr/local/bin/auto-cert.sh << 'EOF'
#!/bin/bash

DOMAIN=$1
VAULT_ADDR="https://vault.example.com:8200"
CERT_PATH="/etc/ssl/certs"

# 証明書発行
vault write -format=json pki_int/issue/example-dot-com \
    common_name="$DOMAIN" \
    ttl="720h" > /tmp/cert_response.json

# 証明書ファイル作成
jq -r '.data.certificate' /tmp/cert_response.json > "$CERT_PATH/$DOMAIN.crt"
jq -r '.data.private_key' /tmp/cert_response.json > "$CERT_PATH/$DOMAIN.key"
jq -r '.data.ca_chain[]' /tmp/cert_response.json > "$CERT_PATH/$DOMAIN-ca.crt"

# Nginx リロード
nginx -s reload

# 証明書情報ログ出力
echo "Certificate issued for $DOMAIN on $(date)" >> /var/log/cert-auto.log

rm /tmp/cert_response.json
EOF

chmod +x /usr/local/bin/auto-cert.sh
```

## 10.5 セキュリティ監視の実装

### IDSの誤検知率とチューニング

侵入検知システム（IDS）は、ネットワークやシステムへの攻撃を検出する重要なセキュリティツールである。しかし、誤検知（False Positive）が多すぎると運用負荷が増大し、本当の脅威を見逃すリスクが高まる。

**Suricata による高精度IDS構築**

```yaml
# suricata.yaml - Suricata設定ファイル
%YAML 1.1
---

# 統計情報設定
stats:
  enabled: yes
  interval: 8

# 出力設定
outputs:
  - fast:
      enabled: yes
      filename: fast.log
      append: yes
  
  - eve-log:
      enabled: yes
      filetype: regular
      filename: eve.json
      types:
        - alert:
            payload: yes
            packet: yes
            metadata: yes
        - http:
            extended: yes
        - dns:
            query: yes
            answer: yes
        - tls:
            extended: yes
        - files:
            force-filestore: no
        - smtp:
        - ssh:
        - stats:
            totals: yes
            threads: no
            deltas: no

# ネットワーク設定
af-packet:
  - interface: eth0
    cluster-id: 99
    cluster-type: cluster_flow
    defrag: yes
    use-mmap: yes
    tpacket-v3: yes

# ホームネットワーク定義
vars:
  address-groups:
    HOME_NET: "[192.168.0.0/16,10.0.0.0/8,172.16.0.0/12]"
    EXTERNAL_NET: "!$HOME_NET"
    
    HTTP_SERVERS: "$HOME_NET"
    SMTP_SERVERS: "$HOME_NET"
    SQL_SERVERS: "$HOME_NET"
    DNS_SERVERS: "$HOME_NET"
    
  port-groups:
    HTTP_PORTS: "80"
    SHELLCODE_PORTS: "!80"
    ORACLE_PORTS: 1521
    SSH_PORTS: 22
    DNP3_PORTS: 20000
    MODBUS_PORTS: 502
    FILE_DATA_PORTS: "[$HTTP_PORTS,110,143]"
    FTP_PORTS: 21

# ルール設定
rule-files:
  - suricata.rules
  - /etc/suricata/rules/emerging-threats.rules
  - /etc/suricata/rules/local.rules

# 分類設定
classification-file: /etc/suricata/classification.config
reference-config-file: /etc/suricata/reference.config
```

**カスタムルール作成と最適化**

```bash
# /etc/suricata/rules/local.rules
# 高精度検知ルールの例

# SQL インジェクション検知（偽陽性を減らす）
alert http $EXTERNAL_NET any -> $HTTP_SERVERS $HTTP_PORTS (msg:"SQL Injection Attack"; content:"union"; nocase; content:"select"; nocase; distance:0; within:20; pcre:"/union\s+.*select/i"; classtype:web-application-attack; sid:1000001; rev:1;)

# 異常なファイルアップロード検知
alert http $EXTERNAL_NET any -> $HTTP_SERVERS $HTTP_PORTS (msg:"Suspicious File Upload"; content:"Content-Type|3a| multipart/form-data"; http_header; content:".php"; http_client_body; pcre:"/\.(php|jsp|asp|py)\x22/i"; classtype:web-application-attack; sid:1000002; rev:1;)

# ブルートフォース攻撃検知（時間窓を使用）
alert tcp $EXTERNAL_NET any -> $SSH_SERVERS $SSH_PORTS (msg:"SSH Brute Force Attack"; flags:S; threshold:type threshold, track by_src, count 5, seconds 60; classtype:attempted-recon; sid:1000003; rev:1;)

# 異常なDNSクエリ検知
alert dns $HOME_NET any -> any any (msg:"DNS Tunneling Attempt"; dns_query; content:"|00|"; depth:50; pcre:"/^[A-Za-z0-9+\/]{50,}/"; classtype:trojan-activity; sid:1000004; rev:1;)

# 内部からの異常な外部通信
alert tcp $HOME_NET any -> $EXTERNAL_NET ![80,443,22,25,53] (msg:"Unusual Outbound Connection"; flags:S; threshold:type threshold, track by_src, count 10, seconds 300; classtype:policy-violation; sid:1000005; rev:1;)
```

**誤検知削減のためのチューニング**

```python
# ids_tuning.py - IDS誤検知分析・チューニングツール
import json
import re
from collections import defaultdict, Counter
from datetime import datetime, timedelta
import pandas as pd
import matplotlib.pyplot as plt

class IDSTuningAnalyzer:
    def __init__(self, eve_log_path):
        self.eve_log_path = eve_log_path
        self.alerts = []
        self.false_positives = []
        
    def load_alerts(self, hours=24):
        """過去24時間のアラートロード"""
        cutoff_time = datetime.now() - timedelta(hours=hours)
        
        with open(self.eve_log_path, 'r') as f:
            for line in f:
                try:
                    event = json.loads(line)
                    if event.get('event_type') == 'alert':
                        event_time = datetime.fromisoformat(
                            event['timestamp'].replace('Z', '+00:00')
                        )
                        if event_time > cutoff_time:
                            self.alerts.append(event)
                except json.JSONDecodeError:
                    continue
    
    def analyze_alert_patterns(self):
        """アラートパターン分析"""
        signature_counts = Counter()
        source_ip_counts = Counter()
        dest_port_counts = Counter()
        hourly_distribution = defaultdict(int)
        
        for alert in self.alerts:
            # シグネチャ別集計
            signature = alert['alert']['signature']
            signature_counts[signature] += 1
            
            # 送信元IP別集計
            src_ip = alert['src_ip']
            source_ip_counts[src_ip] += 1
            
            # 宛先ポート別集計
            dest_port = alert.get('dest_port', 0)
            dest_port_counts[dest_port] += 1
            
            # 時間別分布
            hour = datetime.fromisoformat(
                alert['timestamp'].replace('Z', '+00:00')
            ).hour
            hourly_distribution[hour] += 1
        
        return {
            'signatures': signature_counts,
            'source_ips': source_ip_counts,
            'dest_ports': dest_port_counts,
            'hourly': dict(hourly_distribution)
        }
    
    def identify_false_positives(self):
        """誤検知候補の特定"""
        patterns = self.analyze_alert_patterns()
        
        # 高頻度かつ単一IPからのアラート（誤検知候補）
        suspicious_patterns = []
        
        for signature, count in patterns['signatures'].most_common(20):
            # 同一シグネチャのアラートを分析
            signature_alerts = [
                a for a in self.alerts 
                if a['alert']['signature'] == signature
            ]
            
            source_ips = [a['src_ip'] for a in signature_alerts]
            ip_diversity = len(set(source_ips)) / len(source_ips)
            
            # 多数のアラートが少数のIPから発生している場合
            if count > 100 and ip_diversity < 0.1:
                suspicious_patterns.append({
                    'signature': signature,
                    'count': count,
                    'ip_diversity': ip_diversity,
                    'main_sources': Counter(source_ips).most_common(3)
                })
        
        return suspicious_patterns
    
    def generate_tuning_recommendations(self):
        """チューニング推奨事項生成"""
        false_positive_candidates = self.identify_false_positives()
        recommendations = []
        
        for fp in false_positive_candidates:
            # 送信元IPが内部ネットワークの場合
            main_ip = fp['main_sources'][0][0]
            if self._is_internal_ip(main_ip):
                recommendations.append({
                    'type': 'whitelist',
                    'signature': fp['signature'],
                    'description': f"Add {main_ip} to whitelist for signature",
                    'rule_modification': f"pass tcp {main_ip} any -> any any (msg:\"Whitelist for {main_ip}\"; sid:9000001;)"
                })
            
            # 閾値調整推奨
            if fp['count'] > 1000:
                recommendations.append({
                    'type': 'threshold',
                    'signature': fp['signature'],
                    'description': "Increase threshold to reduce noise",
                    'rule_modification': f"threshold: type threshold, track by_src, count 10, seconds 60;"
                })
        
        return recommendations
    
    def _is_internal_ip(self, ip):
        """内部IPアドレスかどうか判定"""
        import ipaddress
        private_ranges = [
            ipaddress.ip_network('192.168.0.0/16'),
            ipaddress.ip_network('10.0.0.0/8'),
            ipaddress.ip_network('172.16.0.0/12')
        ]
        
        try:
            ip_obj = ipaddress.ip_address(ip)
            return any(ip_obj in network for network in private_ranges)
        except ValueError:
            return False
    
    def generate_report(self):
        """チューニングレポート生成"""
        patterns = self.analyze_alert_patterns()
        recommendations = self.generate_tuning_recommendations()
        
        report = f"""
IDS Tuning Report - {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}
============================================================

Alert Summary:
- Total Alerts: {len(self.alerts)}
- Unique Signatures: {len(patterns['signatures'])}
- Unique Source IPs: {len(patterns['source_ips'])}

Top 10 Alert Signatures:
"""
        for sig, count in patterns['signatures'].most_common(10):
            report += f"- {sig}: {count} alerts\n"
        
        report += "\nTuning Recommendations:\n"
        for i, rec in enumerate(recommendations, 1):
            report += f"{i}. {rec['type'].upper()}: {rec['description']}\n"
            report += f"   Rule: {rec['rule_modification']}\n\n"
        
        return report

# 使用例
if __name__ == "__main__":
    analyzer = IDSTuningAnalyzer('/var/log/suricata/eve.json')
    analyzer.load_alerts(hours=24)
    
    report = analyzer.generate_report()
    print(report)
    
    # レポートをファイルに保存
    with open('/var/log/suricata/tuning_report.txt', 'w') as f:
        f.write(report)
```

### SIEMへのログ統合設計

Security Information and Event Management（SIEM）システムは、組織全体のセキュリティイベントを収集・分析・相関させる中核的な仕組みである。効果的なSIEM実装には、適切なログ正規化と相関ルールの設計が不可欠である。

**Elastic Stack を使用したSIEM構築**

```yaml
# docker-compose.yml - Elastic Stack SIEM環境
version: '3.8'

services:
  elasticsearch:
    image: docker.elastic.co/elasticsearch/elasticsearch:8.8.0
    container_name: siem-elasticsearch
    environment:
      - node.name=es01
      - cluster.name=siem-cluster
      - discovery.type=single-node
      - bootstrap.memory_lock=true
      - "ES_JAVA_OPTS=-Xms2g -Xmx2g"
      - xpack.security.enabled=true
      - xpack.security.enrollment.enabled=true
    ulimits:
      memlock:
        soft: -1
        hard: -1
    volumes:
      - esdata:/usr/share/elasticsearch/data
    ports:
      - "9200:9200"
    networks:
      - siem

  logstash:
    image: docker.elastic.co/logstash/logstash:8.8.0
    container_name: siem-logstash
    volumes:
      - ./logstash/config:/usr/share/logstash/pipeline
      - ./logstash/patterns:/usr/share/logstash/patterns
    ports:
      - "5044:5044"
      - "5000:5000/tcp"
      - "5000:5000/udp"
      - "9600:9600"
    environment:
      LS_JAVA_OPTS: "-Xmx1g -Xms1g"
    networks:
      - siem
    depends_on:
      - elasticsearch

  kibana:
    image: docker.elastic.co/kibana/kibana:8.8.0
    container_name: siem-kibana
    ports:
      - "5601:5601"
    environment:
      ELASTICSEARCH_HOSTS: http://elasticsearch:9200
    networks:
      - siem
    depends_on:
      - elasticsearch

volumes:
  esdata:

networks:
  siem:
    driver: bridge
```

**Logstash による多様なログの正規化**

```ruby
# logstash/config/security-logs.conf
input {
  beats {
    port => 5044
  }
  
  # Syslog 受信
  syslog {
    port => 5000
    codec => cef
  }
  
  # Suricata JSON ログ
  file {
    path => "/var/log/suricata/eve.json"
    codec => json
    tags => ["suricata", "ids"]
  }
  
  # Apache アクセスログ
  file {
    path => "/var/log/apache2/access.log"
    tags => ["apache", "web"]
  }
}

filter {
  # Suricata ログ処理
  if "suricata" in [tags] {
    if [event_type] == "alert" {
      mutate {
        add_field => { 
          "event_category" => "intrusion_detection"
          "severity_level" => "high"
        }
      }
      
      # GeoIP 情報追加
      geoip {
        source => "src_ip"
        target => "src_geoip"
      }
      
      geoip {
        source => "dest_ip"  
        target => "dest_geoip"
      }
      
      # 脅威インテリジェンス拡充
      translate {
        field => "src_ip"
        destination => "threat_intel"
        dictionary_path => "/etc/logstash/threat_intel.yml"
        fallback => "unknown"
      }
    }
  }
  
  # Apache ログ処理
  if "apache" in [tags] {
    grok {
      match => { 
        "message" => "%{COMBINEDAPACHELOG}"
      }
    }
    
    date {
      match => [ "timestamp", "dd/MMM/yyyy:HH:mm:ss Z" ]
    }
    
    # 異常な HTTP ステータスコード検出
    if [response] >= 400 {
      mutate {
        add_field => { 
          "event_category" => "web_attack"
          "severity_level" => "medium"
        }
      }
    }
    
    # SQL インジェクション パターン検出
    if [request] =~ /(?i)(union|select|insert|delete|update|drop|exec)/ {
      mutate {
        add_field => { 
          "event_category" => "sql_injection"
          "severity_level" => "high"
        }
      }
    }
  }
  
  # 共通フィールド追加
  mutate {
    add_field => { 
      "log_source" => "%{host}"
      "ingestion_timestamp" => "%{@timestamp}"
    }
  }
  
  # 不要フィールド削除
  mutate {
    remove_field => [ "message", "host" ]
  }
}

output {
  elasticsearch {
    hosts => ["elasticsearch:9200"]
    index => "security-logs-%{+YYYY.MM.dd}"
    
    # テンプレート適用
    template_name => "security-logs"
    template => "/usr/share/logstash/templates/security-template.json"
    template_overwrite => true
  }
  
  # 高重要度アラートはSlackに送信
  if [severity_level] == "high" {
    http {
      url => "https://hooks.slack.com/services/YOUR/SLACK/WEBHOOK"
      http_method => "post"
      format => "json"
      mapping => {
        "channel" => "#security-alerts"
        "username" => "SIEM-Bot"
        "text" => "High severity security event detected: %{event_category} from %{src_ip}"
        "attachments" => [
          {
            "color" => "danger"
            "fields" => [
              {
                "title" => "Event Type"
                "value" => "%{event_category}"
                "short" => true
              },
              {
                "title" => "Source IP"
                "value" => "%{src_ip}"
                "short" => true
              },
              {
                "title" => "Timestamp"
                "value" => "%{@timestamp}"
                "short" => true
              }
            ]
          }
        ]
      }
    }
  }
}
```

**相関ルールエンジンの実装**

```python
# correlation_engine.py - セキュリティイベント相関エンジン
import json
import redis
from datetime import datetime, timedelta
from collections import defaultdict
import logging

class SecurityCorrelationEngine:
    def __init__(self, redis_host='localhost', redis_port=6379):
        self.redis_client = redis.Redis(host=redis_host, port=redis_port, decode_responses=True)
        self.logger = self._setup_logging()
        
        # 相関ルール定義
        self.correlation_rules = [
            self.brute_force_detection,
            self.lateral_movement_detection,
            self.data_exfiltration_detection,
            self.privilege_escalation_detection
        ]
    
    def _setup_logging(self):
        logging.basicConfig(
            level=logging.INFO,
            format='%(asctime)s - %(levelname)s - %(message)s'
        )
        return logging.getLogger(__name__)
    
    def process_event(self, event):
        """セキュリティイベント処理"""
        # イベントを Redis に一時保存
        event_key = f"event:{event['src_ip']}:{int(datetime.now().timestamp())}"
        self.redis_client.setex(event_key, 3600, json.dumps(event))  # 1時間保持
        
        # 各相関ルールを実行
        for rule in self.correlation_rules:
            try:
                correlation_result = rule(event)
                if correlation_result:
                    self._generate_alert(correlation_result)
            except Exception as e:
                self.logger.error(f"Error in correlation rule {rule.__name__}: {str(e)}")
    
    def brute_force_detection(self, event):
        """ブルートフォース攻撃検出"""
        if event.get('event_category') not in ['failed_login', 'ssh_auth_failure']:
            return None
        
        src_ip = event['src_ip']
        window_key = f"brute_force:{src_ip}"
        
        # 過去10分間の失敗回数を記録
        current_time = int(datetime.now().timestamp())
        self.redis_client.zadd(window_key, {current_time: current_time})
        self.redis_client.expire(window_key, 600)  # 10分間保持
        
        # 10分間で5回以上の失敗
        ten_minutes_ago = current_time - 600
        failure_count = self.redis_client.zcount(window_key, ten_minutes_ago, current_time)
        
        if failure_count >= 5:
            return {
                'correlation_type': 'brute_force_attack',
                'severity': 'high',
                'src_ip': src_ip,
                'failure_count': failure_count,
                'time_window': '10_minutes',
                'description': f'Brute force attack detected from {src_ip} with {failure_count} failures'
            }
        
        return None
    
    def lateral_movement_detection(self, event):
        """横方向移動検出"""
        if event.get('event_category') != 'successful_login':
            return None
        
        src_ip = event['src_ip']
        dest_ip = event.get('dest_ip', '')
        user = event.get('username', '')
        
        # 同一ユーザーの異なるホストへのログイン追跡
        movement_key = f"lateral_movement:{user}"
        current_time = int(datetime.now().timestamp())
        
        # 過去1時間のログイン先を記録
        login_record = {
            'timestamp': current_time,
            'src_ip': src_ip,
            'dest_ip': dest_ip
        }
        
        self.redis_client.lpush(movement_key, json.dumps(login_record))
        self.redis_client.expire(movement_key, 3600)  # 1時間保持
        
        # 過去1時間のログイン履歴を分析
        login_history = []
        for record_json in self.redis_client.lrange(movement_key, 0, -1):
            record = json.loads(record_json)
            if current_time - record['timestamp'] <= 3600:  # 1時間以内
                login_history.append(record)
        
        # 異なるホストへの短時間でのログイン検出
        unique_hosts = set(record['dest_ip'] for record in login_history)
        if len(unique_hosts) >= 3:  # 1時間に3台以上の異なるホスト
            return {
                'correlation_type': 'lateral_movement',
                'severity': 'high',
                'username': user,
                'hosts_accessed': list(unique_hosts),
                'time_window': '1_hour',
                'description': f'Lateral movement detected for user {user} across {len(unique_hosts)} hosts'
            }
        
        return None
    
    def data_exfiltration_detection(self, event):
        """データ流出検出"""
        if event.get('event_category') not in ['file_transfer', 'large_data_transfer']:
            return None
        
        src_ip = event['src_ip']
        bytes_transferred = event.get('bytes_transferred', 0)
        
        # 大容量データ転送の追跡
        exfil_key = f"data_exfil:{src_ip}"
        current_time = int(datetime.now().timestamp())
        
        # 過去30分間の転送量を記録
        self.redis_client.zadd(exfil_key, {current_time: bytes_transferred})
        self.redis_client.expire(exfil_key, 1800)  # 30分保持
        
        # 30分間の総転送量計算
        thirty_minutes_ago = current_time - 1800
        transfer_records = self.redis_client.zrangebyscore(
            exfil_key, thirty_minutes_ago, current_time, withscores=True
        )
        
        total_bytes = sum(score for _, score in transfer_records)
        
        # 30分間で1GB以上の転送
        if total_bytes > 1024 * 1024 * 1024:  # 1GB
            return {
                'correlation_type': 'data_exfiltration',
                'severity': 'critical',
                'src_ip': src_ip,
                'total_bytes': total_bytes,
                'time_window': '30_minutes',
                'description': f'Potential data exfiltration: {total_bytes / (1024**3):.2f}GB transferred from {src_ip}'
            }
        
        return None
    
    def privilege_escalation_detection(self, event):
        """権限昇格検出"""
        if event.get('event_category') != 'privilege_change':
            return None
        
        user = event.get('username', '')
        old_privileges = event.get('old_privileges', [])
        new_privileges = event.get('new_privileges', [])
        
        # 管理者権限への昇格検出
        admin_privileges = ['admin', 'root', 'administrator', 'sudo']
        old_admin = any(priv in admin_privileges for priv in old_privileges)
        new_admin = any(priv in admin_privileges for priv in new_privileges)
        
        if not old_admin and new_admin:
            return {
                'correlation_type': 'privilege_escalation',
                'severity': 'high',
                'username': user,
                'old_privileges': old_privileges,
                'new_privileges': new_privileges,
                'description': f'Privilege escalation detected for user {user} to admin level'
            }
        
        return None
    
    def _generate_alert(self, correlation_result):
        """相関結果からアラート生成"""
        alert = {
            'timestamp': datetime.now().isoformat(),
            'alert_type': 'correlation_alert',
            'correlation_type': correlation_result['correlation_type'],
            'severity': correlation_result['severity'],
            'description': correlation_result['description'],
            'details': correlation_result
        }
        
        # アラートをログ出力
        self.logger.warning(f"CORRELATION ALERT: {alert['description']}")
        
        # Elasticsearch にアラート送信
        self._send_to_elasticsearch(alert)
        
        # 高重要度アラートの場合、即座に通知
        if correlation_result['severity'] in ['high', 'critical']:
            self._send_immediate_notification(alert)
    
    def _send_to_elasticsearch(self, alert):
        """Elasticsearch にアラート送信"""
        # 実装例（実際にはElasticsearchクライアントを使用）
        print(f"Sending to Elasticsearch: {json.dumps(alert, indent=2)}")
    
    def _send_immediate_notification(self, alert):
        """即座の通知送信"""
        # 実装例（実際にはSlack、メール、SMS等の通知システムを使用）
        print(f"IMMEDIATE NOTIFICATION: {alert['description']}")

# 使用例
if __name__ == "__main__":
    engine = SecurityCorrelationEngine()
    
    # サンプルイベント処理
    sample_events = [
        {
            'src_ip': '192.168.1.100',
            'dest_ip': '192.168.1.10',
            'event_category': 'failed_login',
            'username': 'admin',
            'timestamp': datetime.now().isoformat()
        },
        {
            'src_ip': '192.168.1.100',
            'dest_ip': '192.168.1.20',
            'event_category': 'successful_login',
            'username': 'user1',
            'timestamp': datetime.now().isoformat()
        }
    ]
    
    for event in sample_events:
        engine.process_event(event)
```

## まとめ

セキュリティアーキテクチャは、システム全体に浸透させる必要がある横断的な関心事である。ネットワークセグメンテーションから暗号化実装、監視システムまで、各層で適切なセキュリティ機能を実装し、それらを統合的に管理することが重要である。

特に注目すべきは、セキュリティと性能のトレードオフをいかに管理するかという点である。ゼロトラストアーキテクチャや暗号化の全面適用は理想的だが、実装コストと運用負荷を考慮した現実的なアプローチが求められる。

また、自動化の重要性も強調しておきたい。鍵管理の自動化、IDS の自動チューニング、SIEM での相関分析など、人的ミスを減らし、迅速な対応を可能にする自動化システムの構築が、現代のセキュリティ運用には不可欠である。

次章では、これらのセキュリティ基盤の上で動作する高可用性システムの設計を探る。冗長化、フェイルオーバー、分散システムでの一貫性保証という、可用性確保のための技術的課題に取り組む。