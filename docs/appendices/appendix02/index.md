---
layout: book
title: "付録B: トラブルシューティングガイド"
---

# 付録B: トラブルシューティングガイド

## B.1 ネットワーク関連のトラブルシューティング

### B.1.1 接続性の問題

**症状**: サーバーにアクセスできない

**診断手順**:
```bash
# 1. ローカルネットワーク設定確認
ip addr show
ip route show

# 2. DNS解決確認
nslookup example.com
dig example.com

# 3. 接続性確認
ping -c 4 example.com
traceroute example.com

# 4. ポート確認
telnet example.com 80
nmap -p 22,80,443 example.com
```

**対処法**:
- IPアドレス、サブネットマスク、ゲートウェイの確認
- DNSサーバー設定の確認
- ファイアウォール設定の確認
- ネットワーク機器の状態確認

### B.1.2 パフォーマンスの問題

**症状**: ネットワークが遅い

**診断手順**:
```bash
# 帯域幅測定
iperf3 -c server_ip

# パケット損失確認
ping -c 100 gateway_ip | grep loss

# ネットワーク利用状況確認
netstat -i
ss -tuln

# トラフィック監視
tcpdump -i eth0 -n
```

## B.2 サーバー関連のトラブルシューティング

### B.2.1 CPU使用率の問題

**症状**: CPUが100%になる

**診断手順**:
```bash
# CPU使用状況確認
top
htop
vmstat 1

# プロセス詳細確認
ps aux --sort=-%cpu | head -10

# CPU使用履歴確認
sar -u 1 10
```

**対処法**:
- 高CPU使用プロセスの特定と最適化
- プロセス数の制限
- スケーリング（スケールアップ/アウト）の検討

### B.2.2 メモリ不足の問題

**症状**: Out of Memory (OOM) エラー

**診断手順**:
```bash
# メモリ使用状況確認
free -h
cat /proc/meminfo

# プロセス別メモリ使用量
ps aux --sort=-%mem | head -10

# スワップ使用状況
swapon -s

# OOMキラーのログ確認
dmesg | grep -i "killed process"
journalctl -u kernel | grep -i oom
```

## B.3 ストレージ関連のトラブルシューティング

### B.3.1 ディスク容量不足

**症状**: No space left on device

**診断手順**:
```bash
# ディスク使用量確認
df -h

# ディレクトリ別使用量
du -sh /* | sort -hr

# inode使用状況確認
df -i

# 大きなファイルの検索
find /var -type f -size +100M -exec ls -lh {} \;
```

**対処法**:
- 不要ファイルの削除
- ログローテーションの設定
- ディスク容量の拡張
- ファイルシステムの最適化

### B.3.2 ディスクI/O性能問題

**症状**: ディスクアクセスが遅い

**診断手順**:
```bash
# I/O統計確認
iostat -x 1

# ディスク使用率確認
iotop

# ファイルシステム確認
lsblk
mount | grep ^/dev

# SMART情報確認
smartctl -a /dev/sda
```

## B.4 セキュリティ関連のトラブルシューティング

### B.4.1 不正アクセスの検出

**症状**: 異常なログイン試行

**診断手順**:
```bash
# 認証ログ確認
tail -f /var/log/auth.log
journalctl -u ssh -f

# 失敗したログイン試行確認
grep "Failed password" /var/log/auth.log | tail -20

# 接続中のセッション確認
who
w
ss -tuln | grep :22
```

**対処法**:
- 強力なパスワードポリシーの実装
- SSH鍵認証の設定
- fail2banの設定
- ファイアウォールルールの強化

### B.4.2 証明書の問題

**症状**: SSL/TLS証明書エラー

**診断手順**:
```bash
# 証明書確認
openssl x509 -in certificate.crt -text -noout

# 証明書の有効期限確認
openssl x509 -enddate -noout -in certificate.crt

# 証明書チェーンの確認
openssl s_client -connect example.com:443 -showcerts

# 証明書の検証
openssl verify -CAfile ca-bundle.crt certificate.crt
```

## B.5 サービス関連のトラブルシューティング

### B.5.1 サービス起動失敗

**症状**: systemdサービスが起動しない

**診断手順**:
```bash
# サービス状態確認
systemctl status service-name

# サービスログ確認
journalctl -u service-name -f

# 設定ファイル確認
systemctl show service-name
systemctl cat service-name

# 依存関係確認
systemctl list-dependencies service-name
```

### B.5.2 Webサーバーの問題

**症状**: Webサイトにアクセスできない

**診断手順**:
```bash
# Webサーバー状態確認
systemctl status nginx
systemctl status apache2

# ポート確認
ss -tuln | grep :80
ss -tuln | grep :443

# エラーログ確認
tail -f /var/log/nginx/error.log
tail -f /var/log/apache2/error.log

# 設定ファイル構文確認
nginx -t
apache2ctl configtest
```

## B.6 データベース関連のトラブルシューティング

### B.6.1 MySQL/MariaDBの問題

**症状**: データベース接続エラー

**診断手順**:
```bash
# データベース状態確認
systemctl status mysql
systemctl status mariadb

# プロセス確認
ps aux | grep mysql

# 接続テスト
mysql -u root -p -e "SHOW DATABASES;"

# エラーログ確認
tail -f /var/log/mysql/error.log

# 設定確認
mysql -u root -p -e "SHOW VARIABLES LIKE 'max_connections';"
```

### B.6.2 PostgreSQLの問題

**症状**: PostgreSQL接続エラー

**診断手順**:
```bash
# サービス状態確認
systemctl status postgresql

# ログ確認
tail -f /var/log/postgresql/postgresql-*.log

# 接続設定確認
cat /etc/postgresql/*/main/pg_hba.conf
cat /etc/postgresql/*/main/postgresql.conf

# 接続テスト
sudo -u postgres psql -c "\l"
```

## B.7 仮想化関連のトラブルシューティング

### B.7.1 Dockerの問題

**症状**: コンテナが起動しない

**診断手順**:
```bash
# Docker状態確認
systemctl status docker

# コンテナ状態確認
docker ps -a

# ログ確認
docker logs container-name

# イメージ確認
docker images

# リソース使用状況確認
docker stats
```

### B.7.2 仮想マシンの問題

**症状**: VM起動失敗

**診断手順**:
```bash
# KVM確認
lsmod | grep kvm
cat /proc/cpuinfo | grep vmx

# libvirt状態確認
systemctl status libvirtd

# VM状態確認
virsh list --all

# VM設定確認
virsh dumpxml vm-name

# ログ確認
journalctl -u libvirtd
```

## B.8 監視とパフォーマンス

### B.8.1 システム全体の健康状態チェック

**診断スクリプト例**:
```bash
#!/bin/bash
# system_health_check.sh

echo "=== システム健康状態チェック ==="
echo "実行時刻: $(date)"
echo

echo "=== CPU使用率 ==="
top -bn1 | grep "Cpu(s)" | awk '{print $2}' | cut -d'%' -f1

echo "=== メモリ使用率 ==="
free | grep Mem | awk '{printf "%.1f%%\n", $3/$2 * 100.0}'

echo "=== ディスク使用率 ==="
df -h | grep -vE '^Filesystem|tmpfs|cdrom' | awk '{print $5 " " $1}' | while read output;
do
  usage=$(echo $output | awk '{print $1}' | cut -d'%' -f1)
  partition=$(echo $output | awk '{print $2}')
  if [ $usage -ge 90 ]; then
    echo "警告: パーティション \"$partition\" の使用率が $usage% です"
  fi
done

echo "=== ネットワーク接続 ==="
ping -c 1 8.8.8.8 >/dev/null 2>&1 && echo "インターネット接続: OK" || echo "インターネット接続: NG"

echo "=== 重要サービス状態 ==="
for service in sshd nginx mysql; do
    if systemctl is-active --quiet $service; then
        echo "$service: 稼働中"
    else
        echo "$service: 停止中"
    fi
done
```

### B.8.2 ログ監視の自動化

**logwatchスクリプト例**:
```bash
#!/bin/bash
# log_monitor.sh

# エラーキーワード
ERROR_KEYWORDS="error|fail|exception|critical|alert"

# 監視対象ログファイル
LOG_FILES="/var/log/syslog /var/log/auth.log /var/log/nginx/error.log"

for log_file in $LOG_FILES; do
    if [ -f "$log_file" ]; then
        echo "=== $log_file の監視 ==="
        tail -n 100 "$log_file" | grep -iE "$ERROR_KEYWORDS" | tail -10
        echo
    fi
done
```

## B.9 予防保守

### B.9.1 定期的なヘルスチェック

**月次チェックリスト**:
- [ ] システムアップデート確認
- [ ] ディスク容量確認
- [ ] ログローテーション確認
- [ ] バックアップ動作確認
- [ ] セキュリティパッチ適用
- [ ] パフォーマンス監視データ確認

### B.9.2 自動化スクリプト

**自動メンテナンススクリプト**:
```bash
#!/bin/bash
# auto_maintenance.sh

# ログクリーンアップ
find /var/log -name "*.log.*" -mtime +30 -delete

# 一時ファイルクリーンアップ
find /tmp -type f -mtime +7 -delete

# パッケージキャッシュクリーンアップ
apt clean

# システム再起動が必要かチェック
if [ -f /var/run/reboot-required ]; then
    echo "システム再起動が必要です"
fi
```

## B.10 緊急時対応

### B.10.1 サーバーダウン時の対応手順

1. **初期確認**
   - サービス状態確認
   - リソース使用状況確認
   - ログ確認

2. **応急処置**
   - サービス再起動
   - リソース不足の解消
   - 一時的な回避策

3. **根本対策**
   - 原因調査
   - 設定変更
   - インフラ改善

### B.10.2 データ損失時の対応

1. **被害状況確認**
2. **バックアップからの復旧**
3. **整合性チェック**
4. **再発防止策の実装**

---

このトラブルシューティングガイドは、ITインフラの運用で遭遇する一般的な問題と解決方法をまとめたものです。定期的に更新し、組織固有の問題や解決方法を追加することをお勧めします。