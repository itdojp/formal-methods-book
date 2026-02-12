# 第8章：仮想化技術の実装原理

物理的なハードウェアを論理的に分割し、複数の独立した環境を作り出す仮想化技術。この概念は単純に見えるが、その実装には CPU、メモリ、I/O という異なる特性を持つリソースの巧妙な抽象化が必要である。

なぜ仮想化が必要となったのか。なぜハイパーバイザーとコンテナという2つの大きく異なるアプローチが並存しているのか。これらの疑問に答えることで、現代のインフラストラクチャ設計における仮想化技術の位置づけと、適切な選択基準が明確になる。

## 8.1 CPU仮想化の実装技術

### Intel VT-x/AMD-Vの活用

現代の CPU 仮想化は、ハードウェア支援仮想化技術により大幅に効率化されている。Intel VT-x と AMD-V は、仮想化のオーバーヘッドを最小限に抑える革新的な技術である。

**ハードウェア支援仮想化の必要性**

従来のソフトウェア仮想化では、特権命令の処理が大きな課題だった：

```text
x86アーキテクチャの特権命令問題：
1. ゲストOSがRing 0で実行される想定だが、実際はRing 1で実行
2. 特権命令（例：CLI、STI、LGDT）がトラップされずに実行される
3. 結果：システム状態の不整合、セキュリティホール

従来の解決策（バイナリ変換）：
- 特権命令を動的にトラップ可能な命令に書き換え
- 大きなオーバーヘッド（10〜30%の性能低下）
- 複雑な実装（VMware、VirtualBoxの初期実装）
```

**VT-x/AMD-V による解決**

```text
ハードウェア支援による新しいアプローチ：

VMX Operation Mode（Intel VT-x）:
- VMX root operation：ハイパーバイザー実行環境
- VMX non-root operation：ゲストOS実行環境

VM Exit/Entry：
- 特権命令実行時に自動的にハイパーバイザーに制御移管
- ハイパーバイザーで処理後、ゲストOSに制御復帰
- ハードウェアレベルでの高速切り替え

VMCS（Virtual Machine Control Structure）:
- ゲストOSの状態保存領域
- VM Exit/Entry条件の設定
- ハードウェアによる自動管理
```

**VT-x機能の確認と設定**

```bash
# CPU の仮想化機能確認
grep -E "(vmx|svm)" /proc/cpuinfo

# Intel VT-x
grep vmx /proc/cpuinfo
# flags: ... vmx ... (Virtual Machine eXtensions)

# AMD-V  
grep svm /proc/cpuinfo
# flags: ... svm ... (Secure Virtual Machine)

# KVM モジュールの確認
lsmod | grep kvm
# kvm_intel             245760  0    # Intel VT-x サポート
# kvm                   737280  1 kvm_intel

# 詳細な仮想化機能確認
/usr/bin/kvm-ok
# INFO: /dev/kvm exists
# KVM acceleration can be used

# QEMU/KVM での VT-x 活用例
qemu-system-x86_64 \
    -enable-kvm \          # KVM acceleration 有効
    -cpu host \            # ホストCPU機能をゲストに公開
    -m 4096 \              # 4GB RAM
    -smp cores=2 \         # 2 CPU コア
    disk.qcow2

# VM Exit 統計の確認
cat /sys/kernel/debug/kvm/vcpu-*/exit_reason
# 主要な Exit 理由：
# EPT_VIOLATION: メモリアクセス違反
# IO_INSTRUCTION: I/O 命令実行
# MSR_WRITE: モデル固有レジスタ書き込み
# INTERRUPT_WINDOW: 割り込み注入
```

**パフォーマンス最適化**

```bash
# CPU パフォーマンス カウンターによる測定
perf kvm stat record -p [qemu-pid]
perf kvm stat report

# 出力例：
# Analyze events for all VCPUs:
# 
#     VM-EXIT    Samples  Samples%     Time%         Avg time
# IO_INSTRUCTION    1204     8.42%     2.45%      40.99us
# EPT_VIOLATION      890     6.23%     1.12%      25.44us
# MSR_WRITE          456     3.19%     0.89%      39.25us

# 最適化のポイント：
# 1. IO_INSTRUCTION の削減：
#    - virtio の使用（準仮想化I/O）
#    - VFIO による デバイス直接割り当て

# 2. EPT_VIOLATION の削減：
#    - 適切なメモリサイズ設定
#    - Huge Pages の使用
#    - メモリバルーニングの調整

# CPU 親和性設定（NUMA考慮）
# ゲストのvCPUを特定の物理CPUに固定
virsh vcpupin vm-name 0 0-3    # vCPU 0を物理CPU 0-3に固定
virsh vcpupin vm-name 1 4-7    # vCPU 1を物理CPU 4-7に固定

# CPU isolation（ホストOS用とゲスト用を分離）
# カーネル起動パラメータ
# isolcpus=2-7 nohz_full=2-7 rcu_nocbs=2-7
# CPU 2-7をゲスト専用に隔離
```

### 準仮想化のメリットと適用範囲

準仮想化（Paravirtualization）は、ゲストOSが仮想化環境を認識し、ハイパーバイザーと協調して動作する技術である。完全仮想化より高い性能を実現できる場合がある。

**準仮想化の基本概念**

```text
完全仮想化 vs 準仮想化:

完全仮想化：
- ゲストOSは仮想化を意識しない
- 既存OSをそのまま使用可能
- ハードウェア支援が必要
- 一部操作でVM Exitが発生

準仮想化：
- ゲストOSが仮想化環境を認識
- 特権操作をhypercallで直接実行
- VM Exitの回数削減
- ゲストOSの改変が必要
```

**Xen における準仮想化実装**

```bash
# Xen hypercall の例
# ゲストOSから直接ハイパーバイザーを呼び出し

# メモリ管理 hypercall
# ページテーブル更新を直接ハイパーバイザーに依頼
echo "update_va_mapping(va, new_pte, flags)" 

# 時刻取得 hypercall  
# 仮想TSC（Time Stamp Counter）からの高精度時刻取得
echo "vcpu_op(VCPUOP_get_runstate_info, vcpu_id, &runstate)"

# I/O操作 hypercall
# デバイスアクセスを効率的に実行
echo "event_channel_op(EVTCHNOP_send, &send)"

# 準仮想化の利点（測定例）：
# システムコール実行：完全仮想化の80%の時間
# メモリ操作：90%の時間
# ネットワークI/O：70%の時間
```

**virtio による準仮想化 I/O**

```bash
# virtio デバイスの確認
lspci | grep -i virtio

# 出力例：
# 00:03.0 Ethernet controller: Red Hat, Inc. Virtio network device
# 00:04.0 SCSI storage controller: Red Hat, Inc. Virtio block device
# 00:05.0 Unclassified device [00ff]: Red Hat, Inc. Virtio memory balloon

# virtio-net（ネットワーク）設定
qemu-system-x86_64 \
    -netdev tap,id=net0,ifname=tap0,script=no,downscript=no \
    -device virtio-net-pci,netdev=net0,mac=52:54:00:12:34:56

# virtio-blk（ブロックデバイス）設定  
qemu-system-x86_64 \
    -drive file=disk.qcow2,if=virtio,format=qcow2

# ゲスト内での virtio パフォーマンス測定
# 従来のエミュレートデバイス（e1000）
ethtool -i eth0 | grep driver  # driver: e1000
iperf3 -c server_ip            # 結果：約500Mbps

# virtio デバイス
ethtool -i eth0 | grep driver  # driver: virtio_net  
iperf3 -c server_ip            # 結果：約2.5Gbps（5倍向上）

# virtio の動作原理：
# 1. ゲストドライバがリクエストをvirtqueueに配置
# 2. ホストに通知（VM Exitを最小限に）
# 3. ホストがバッチ処理で複数リクエストを処理
# 4. 完了をゲストに通知
```

**準仮想化の適用判断**

```bash
# 適用が効果的な場面：
# 1. I/O集約的なワークロード
echo "データベースサーバー：30〜50%性能向上"
echo "Web サーバー：20〜40%性能向上"
echo "ファイルサーバー：40〜60%性能向上"

# 2. レガシーハードウェア（VT-x/AMD-V非対応）
echo "古いCPUでの仮想化実現"

# 3. 特定のセキュリティ要件
echo "ハイパーバイザーレベルでの詳細な制御"

# 適用が困難な場面：
echo "WindowsゲストOS（準仮想化対応限定的）"
echo "ベンダーサポート対象外OS"
echo "開発・テスト環境（管理の複雑化）"

# virtio-vsock（ホスト-ゲスト間通信）
# ネットワークを経由しない高速通信
modprobe vhost-vsock
qemu-system-x86_64 \
    -device vhost-vsock-pci,guest-cid=3

# ゲスト内でのテスト
socat - VSOCK-CONNECT:2:1234  # CID 2（ホスト）のポート1234に接続
```

## 8.2 メモリ仮想化の課題と解決

### EPT/NPTによる二段階アドレス変換

メモリ仮想化は仮想化技術の中で最も複雑な要素の一つである。ゲストの仮想アドレス、ゲストの物理アドレス、ホストの物理アドレスという3層のアドレス空間を効率的に管理する必要がある。

**Shadow Page Table（従来手法）の問題**

```text
従来のメモリ仮想化手法：

ゲスト仮想アドレス → ゲスト物理アドレス（ゲストページテーブル）
ゲスト物理アドレス → ホスト物理アドレス（シャドウページテーブル）

問題点：
1. 二重アドレス変換のオーバーヘッド
2. シャドウページテーブルの維持コスト
3. ゲストページテーブル変更時のVM Exit
4. TLBフラッシュの頻発

性能影響：
- メモリ集約的アプリケーション：20〜40%の性能低下
- TLBミス時のペナルティ：通常の4〜8倍
```

**EPT/NPTによる革新**

Extended Page Table（Intel）とNested Page Table（AMD）による解決：

```bash
# EPT/NPT機能の確認
grep -E "(ept|npt)" /proc/cpuinfo

# Intel EPT
cat /sys/module/kvm_intel/parameters/ept
# Y (有効)

# AMD NPT  
cat /sys/module/kvm_amd/parameters/npt
# 1 (有効)

# EPT/NPTの動作原理：
# 1. ハードウェアが二段階アドレス変換を直接実行
# 2. ゲストページテーブル変更でもVM Exit不要
# 3. ハードウェアTLB（EPT/NPT TLB）による高速化

# EPT違反の監視
cat /sys/kernel/debug/kvm/vcpu-*/ept_violation
# 原因別の統計情報：
# - ページ不在
# - 権限違反  
# - A/D ビット更新
```

**メモリパフォーマンス最適化**

```bash
# Large Page/Huge Page の活用
# ホスト側でのHuge Pages設定
echo 1024 > /proc/sys/vm/nr_hugepages  # 2GB分のHuge Pages

# QEMUでのHuge Pages使用
qemu-system-x86_64 \
    -mem-prealloc \           # メモリ事前割り当て
    -mem-path /dev/hugepages \ # Huge Pages使用
    -m 4096

# 効果の測定
# TLBミス率の比較：
echo "通常4KBページ：1GBメモリで256,000TLBエントリ必要"
echo "2MB Huge Page：1GBメモリで512TLBエントリのみ"
echo "TLBミス率：90%以上削減"

# NUMA 親和性の確保
numactl --membind=0 --cpunodebind=0 qemu-system-x86_64 \
    -numa node,mem=2048,cpus=0-1,nodeid=0 \
    -numa node,mem=2048,cpus=2-3,nodeid=1

# ゲスト内でのNUMA確認
numactl --hardware
# available: 2 nodes (0-1)
# node 0 cpus: 0 1
# node 0 size: 2047 MB
# node 1 cpus: 2 3  
# node 1 size: 2047 MB

# クロスNUMAアクセスの測定
numastat -p $(pgrep qemu)
```

### メモリバルーニングとオーバーコミット

メモリバルーニングは、動的なメモリ管理により物理メモリの効率的利用を実現する技術である。オーバーコミットと組み合わせることで、物理メモリ以上のメモリを仮想マシンに割り当てることが可能となる。

**バルーニングの動作原理**

```bash
# バルーンデバイスの設定
qemu-system-x86_64 \
    -device virtio-balloon-pci,id=balloon0 \
    -monitor unix:/tmp/monitor.sock,server,nowait

# QEMU Monitorでのバルーン操作
echo "info balloon" | socat - UNIX-CONNECT:/tmp/monitor.sock
# balloon: actual=1024

# メモリ回収（1GBから512MBに削減）
echo "balloon 512" | socat - UNIX-CONNECT:/tmp/monitor.sock

# ゲスト内でのバルーンドライバ動作：
# 1. ホストからの回収要求受信
# 2. ゲストOSがページを選択（使用頻度の低いページ）
# 3. 選択したページをバルーンドライバが確保
# 4. 物理ページをホストに返却
# 5. ゲスト内では該当ページが利用不可に

# バルーニング統計の確認
cat /proc/meminfo | grep -i balloon
# または
cat /sys/devices/virtio-pci/virtio*/statistics/deflate_count
```

**オーバーコミットの実装**

```bash
# KSM（Kernel Same-page Merging）の活用
echo 1 > /sys/kernel/mm/ksm/run

# KSM設定パラメータ
echo 100 > /sys/kernel/mm/ksm/sleep_millisecs     # スキャン間隔
echo 256 > /sys/kernel/mm/ksm/pages_to_scan       # 1回あたりのスキャンページ数

# KSM効果の確認
cat /sys/kernel/mm/ksm/pages_sharing    # 共有中のページ数
cat /sys/kernel/mm/ksm/pages_shared     # 共有されているページ数
cat /sys/kernel/mm/ksm/pages_unshared   # 共有対象外のページ数

# 削減メモリ量の計算
shared_pages=$(cat /sys/kernel/mm/ksm/pages_shared)
sharing_pages=$(cat /sys/kernel/mm/ksm/pages_sharing)
saved_memory=$(( (sharing_pages - shared_pages) * 4 ))  # KB単位
echo "Saved memory: ${saved_memory} KB"

# 透明Huge Pageの調整
echo madvise > /sys/kernel/mm/transparent_hugepage/enabled
# always：常に有効（メモリ使用量増加の可能性）
# madvise：アプリケーション要求時のみ
# never：無効

# スワップ動作の調整
echo 1 > /proc/sys/vm/swappiness  # バルーニング優先、スワップ最小限
```

**オーバーコミット監視**

```bash
#!/bin/bash
# メモリオーバーコミット監視スクリプト

# ホスト物理メモリ
host_total=$(awk '/MemTotal/ {print $2}' /proc/meminfo)

# 全VM割り当てメモリの合計
vm_total=0
for vm in $(virsh list --name); do
    if [[ -n "$vm" ]]; then
        vm_mem=$(virsh dominfo "$vm" | awk '/Max memory/ {print $3}')
        vm_total=$((vm_total + vm_mem))
    fi
done

# オーバーコミット率
overcommit_ratio=$(echo "scale=2; $vm_total / $host_total" | bc)

echo "Host Memory: ${host_total} KB"
echo "VM Total Memory: ${vm_total} KB"  
echo "Overcommit Ratio: ${overcommit_ratio}"

# アラート条件
if (( $(echo "$overcommit_ratio > 1.5" | bc -l) )); then
    echo "WARNING: High overcommit ratio detected!"
    
    # バルーニング推奨
    echo "Consider balloon deflation for less active VMs"
    
    # KSM効果確認
    ksm_saved=$(cat /sys/kernel/mm/ksm/pages_shared)
    echo "KSM saved pages: $ksm_saved"
fi
```

## 8.3 I/O仮想化の実装方式

### 完全仮想化vs準仮想化ドライバ

I/O仮想化は、仮想マシンと物理デバイス間の効率的な橋渡しを実現する重要な技術である。実装方式により、性能と互換性に大きな違いが生じる。

**完全仮想化I/Oの特徴**

```bash
# エミュレートデバイスの例（QEMU）
qemu-system-x86_64 \
    -netdev user,id=net0 \
    -device e1000,netdev=net0 \      # Intel e1000 エミュレーション
    -drive file=disk.qcow2,if=ide \  # IDE コントローラーエミュレーション
    -usb -device usb-tablet          # USB デバイスエミュレーション

# エミュレーションのオーバーヘッド：
# 1. ゲストドライバ → エミュレート層 → ホストドライバ
# 2. 各I/O操作でVM Exit発生
# 3. QEMU プロセスでのソフトウェア処理
# 4. システムコール経由でホストカーネルアクセス

# 性能測定例（IDE vs virtio-blk）
# IDE エミュレーション
fio --name=ide_test --filename=/dev/sda --rw=randread --bs=4k \
    --iodepth=1 --size=1G --runtime=60
# 結果：~5,000 IOPS

# virtio-blk
fio --name=virtio_test --filename=/dev/vda --rw=randread --bs=4k \
    --iodepth=32 --size=1G --runtime=60  
# 結果：~45,000 IOPS（9倍向上）
```

**virtio アーキテクチャの詳細**

```bash
# virtio-ring の構造
# ゲストとホスト間の効率的通信メカニズム

# Available Ring：ゲスト→ホスト（リクエスト）
# Used Ring：ホスト→ゲスト（完了通知）
# Descriptor Table：実際のデータバッファ情報

# virtqueue 情報の確認
cat /sys/devices/virtio-pci/virtio*/virtqueue*/vq_index
cat /sys/devices/virtio-pci/virtio*/virtqueue*/vq_num

# virtio-net の詳細設定
qemu-system-x86_64 \
    -netdev tap,id=net0,ifname=tap0,vhost=on \
    -device virtio-net-pci,netdev=net0,mq=on,vectors=10
# vhost=on：カーネル内での高速処理
# mq=on：マルチキュー対応
# vectors=10：MSI-X割り込みベクタ

# マルチキュー性能の確認
ethtool -l eth0
# Channel parameters for eth0:
# Pre-set maximums:
# RX:		0
# TX:		0
# Other:		1
# Combined:	4
# Current hardware settings:
# RX:		0
# TX:		0
# Other:		1
# Combined:	4

# キューごとの統計
cat /proc/interrupts | grep virtio
#  24:     123456          0          0          0   PCI-MSI-edge      virtio0-input.0
#  25:      78901          0          0          0   PCI-MSI-edge      virtio0-output.0
#  26:          0     234567          0          0   PCI-MSI-edge      virtio0-input.1
#  27:          0     345678          0          0   PCI-MSI-edge      virtio0-output.1
```

**DPDK による超高速I/O**

```bash
# DPDK（Data Plane Development Kit）環境の設定
# ユーザー空間でのNIC直接制御

# DPDK用のHuge Pages設定
echo 1024 > /proc/sys/vm/nr_hugepages

# UIO（Userspace I/O）の設定
modprobe uio_pci_generic

# NICをDPDK用に設定
./dpdk-devbind.py --bind=uio_pci_generic 0000:01:00.0

# DPDK アプリケーションの実行
./testpmd -l 0-3 -n 4 -- -i --nb-cores=2 --nb-ports=2

# 性能測定結果例：
# 標準NICドライバ：~1.5 Mpps（Million packets per second）
# virtio-net：~2.5 Mpps
# DPDK：~14.8 Mpps（約10倍向上）

# ただし、制約事項：
# - CPU専有（ポーリング駆動）
# - メモリ占有量大
# - 特殊なアプリケーション開発が必要
```

### SR-IOVの原理と適用判断

SR-IOV（Single Root I/O Virtualization）は、単一の物理デバイスを複数の仮想機能（VF）に分割し、仮想マシンに直接割り当てる技術である。

**SR-IOVの基本構造**

```bash
# SR-IOV対応デバイスの確認
lspci | grep -i ethernet
# 08:00.0 Ethernet controller: Intel Corporation 82599ES 10-Gigabit SFI/SFP+ (rev 01)

# SR-IOV機能の確認
lspci -v -s 08:00.0 | grep -i sr-iov
# Capabilities: [160] Single Root I/O Virtualization (SR-IOV)

# Virtual Function (VF) の有効化
echo 4 > /sys/class/net/eth0/device/sriov_numvfs

# 作成されたVFの確認
lspci | grep Virtual
# 08:10.0 Ethernet controller: Intel Corporation 82599 Ethernet Virtual Function (rev 01)
# 08:10.2 Ethernet controller: Intel Corporation 82599 Ethernet Virtual Function (rev 01)
# 08:10.4 Ethernet controller: Intel Corporation 82599 Ethernet Virtual Function (rev 01)
# 08:10.6 Ethernet controller: Intel Corporation 82599 Ethernet Virtual Function (rev 01)

# PF（Physical Function）とVF（Virtual Function）の関係：
# PF：物理デバイス全体の管理
# VF：個別の仮想機能（ゲストVMに直接割り当て可能）
```

**VFIO による デバイス直接割り当て**

```bash
# VFIO（Virtual Function I/O）の設定
# ハードウェアによる完全な分離を実現

# IOMMU の有効化確認
dmesg | grep -i iommu
# IOMMU enabled

# VFIO モジュールロード
modprobe vfio-pci

# VF をVFIOに割り当て
echo 0000:08:10.0 > /sys/bus/pci/drivers/ixgbevf/unbind
echo 8086 10ed > /sys/bus/pci/drivers/vfio-pci/new_id

# QEMU での VF 割り当て
qemu-system-x86_64 \
    -device vfio-pci,host=08:10.0 \
    -m 4096

# 利点：
# 1. ネイティブ性能（オーバーヘッドほぼゼロ）
# 2. ハードウェア機能の完全利用
# 3. ゲストからの直接制御

# 制約：
# 1. ハードウェア依存（SR-IOV、IOMMU必須）
# 2. ライブマイグレーション困難
# 3. 管理の複雑化
```

**SR-IOV 性能測定**

```bash
# 性能比較テスト

# 1. 従来仮想化（virtio-net）
iperf3 -c server_ip -t 60 -P 4
# [ SUM]   0.00-60.00  sec  24.2 GBytes  3.47 Gbits/sec    0             sender

# 2. SR-IOV（直接割り当て）
iperf3 -c server_ip -t 60 -P 4  
# [ SUM]   0.00-60.00  sec  58.8 GBytes  8.42 Gbits/sec    0             sender

# CPU 使用率の比較
# virtio-net：ホストCPU使用率 ~25%
# SR-IOV：ホストCPU使用率 ~5%（DMA直接転送）

# レイテンシ測定
# virtio-net：平均100μs、P99 500μs
# SR-IOV：平均15μs、P99 50μs

# パケット処理能力
# virtio-net：~2.5 Mpps
# SR-IOV：~14.88 Mpps（理論上限）
```

**適用判断の基準**

```bash
# SR-IOV 適用が効果的な場面：
echo "高性能計算（HPC）クラスター"
echo "ネットワーク集約的アプリケーション"
echo "レイテンシクリティカルなワークロード"
echo "NFV（Network Function Virtualization）"

# 制約により適用困難な場面：
echo "クラウド環境（ライブマイグレーション必須）"
echo "頻繁なVM作成・削除"
echo "レガシーハードウェア環境"
echo "複雑な運用を避けたい環境"

# ハイブリッドアプローチ：
# 1. 高性能要求：SR-IOV
# 2. 標準要求：virtio-net
# 3. 管理・監視：エミュレートデバイス

# QoS（Quality of Service）設定例
# SR-IOV VF の帯域制限
ip link set dev eth0 vf 0 rate 1000  # VF 0を1Gbpsに制限
ip link set dev eth0 vf 1 rate 500   # VF 1を500Mbpsに制限

# VLAN 設定
ip link set dev eth0 vf 0 vlan 100   # VF 0をVLAN 100に配置
ip link set dev eth0 vf 1 vlan 200   # VF 1をVLAN 200に配置
```

## 8.4 ハイパーバイザーアーキテクチャ比較

### Type1：Xen、VMware ESXiの設計

Type1 ハイパーバイザー（ベアメタル型）は、物理ハードウェア上で直接動作し、最小限のオーバーヘッドで仮想化を実現する。

**Xen のマイクロカーネル設計**

```bash
# Xen アーキテクチャの確認
xl info

# 出力例：
# host                   : xenserver
# release                : 4.4.0
# version                : #1 SMP
# machine                : x86_64
# nr_cpus                : 8
# max_cpu_id             : 7
# nr_nodes               : 2
# cores_per_socket       : 4
# threads_per_core       : 1
# cpu_mhz                : 2400
# hw_caps                : bfebfbff:28100800:00000000:00000940:00000000:00000000:00000000:00000000
# virt_caps              : hvm hvm_directio
# total_memory           : 32751
# free_memory            : 16234

# Xen の構成要素：
# 1. Xen Hypervisor：最小限のマイクロカーネル（~1MB）
# 2. Dom0：特権ドメイン（管理機能、デバイスドライバ）
# 3. DomU：非特権ドメイン（ゲストOS）

# Dom0 での管理操作
xl list
# Name                                        ID   Mem VCPUs      State   Time(s)
# Domain-0                                     0  4096     4     r-----      45.2
# centos7-guest                                1  2048     2     -b----      12.3
# windows10-guest                              2  4096     4     r-----      89.1
```

**Xen の準仮想化実装**

```bash
# PV（準仮想化）ゲストの作成
cat > /etc/xen/pv-guest.cfg << EOF
name = "pv-linux"
kernel = "/boot/vmlinuz-xen"
ramdisk = "/boot/initrd-xen.img"
memory = 2048
vcpus = 2
disk = [
    'phy:/dev/vg_guests/pv-linux,xvda,w'
]
vif = [
    'bridge=xenbr0'
]
EOF

xl create /etc/xen/pv-guest.cfg

# PV vs HVM 性能比較：
# PV：
# - CPU仮想化：hypercall使用、VM Exit最小
# - メモリ：準仮想化MMU、ページテーブル直接操作
# - I/O：準仮想化ドライバ（netfront/netback、blkfront/blkback）

# HVM：
# - CPU仮想化：ハードウェア支援（VT-x/AMD-V）
# - メモリ：EPT/NPT使用
# - I/O：エミュレーション または 準仮想化ドライバ

# 性能測定例：
echo "CPU集約：PV ≈ HVM（VT-x使用時）"
echo "I/O集約：PV > HVM（準仮想化ドライバ使用時）"
echo "互換性：HVM > PV（既存OS対応）"
```

**VMware ESXi の商用最適化**

```bash
# ESXi の特徴的機能

# 1. Memory Compression
# スワップ前にメモリ圧縮でメモリ使用量削減
# 圧縮率：通常50%程度、スワップ回避による性能向上

# 2. Transparent Page Sharing (TPS)
# 同一内容ページの自動共有
# 効果：同種OSの複数VM環境で30〜60%メモリ削減

# 3. CPU スケジューラー
# Co-scheduling：マルチCPU VMのCPU同時実行保証
# Gang scheduling：関連プロセスの同期実行

# 4. Network I/O Control (NIOC)
# ネットワーク帯域の細粒度制御
# VM・vSwitch・アップリンクレベルでのQoS

# ESXi での性能監視（PowerCLI）
Connect-VIServer -Server vcenter.example.com

# CPU Ready Time（CPUスケジューリング待ち時間）
Get-Stat -Entity (Get-VM) -Stat cpu.ready.summation

# メモリバルーニング状況
Get-Stat -Entity (Get-VM) -Stat mem.vmmemctl.average

# ストレージレイテンシ
Get-Stat -Entity (Get-VM) -Stat virtualDisk.totalReadLatency.average
```

### Type2：KVM、VirtualBoxの実装

Type2 ハイパーバイザー（ホスト型）は、既存OSの上で動作し、より柔軟な運用を可能にする。

**KVM のハイブリッドアプローチ**

```bash
# KVM は特殊な位置づけ：
# - Linuxカーネルモジュールとして実装
# - Type1的な直接ハードウェアアクセス
# - Type2的なホストOSとの協調動作

# KVM の構成要素確認
lsmod | grep kvm
# kvm_intel             245760  4
# kvm                   737280  1 kvm_intel

# /dev/kvm デバイス確認
ls -l /dev/kvm
# crw-rw-rw- 1 root kvm 10, 232 Dec  1 10:00 /dev/kvm

# QEMU + KVM の動作確認
ps aux | grep qemu
# qemu     1234  5.2  2.1 2048000 687432 ?      Sl   10:00   0:52 /usr/bin/qemu-system-x86_64 -enable-kvm ...

# KVM の性能最適化
# 1. CPU Pinning
virsh vcpupin vm-name 0 0     # vCPU 0を物理CPU 0に固定
virsh vcpupin vm-name 1 1     # vCPU 1を物理CPU 1に固定

# 2. NUMA トポロジー設定
virsh numatune vm-name --mode strict --nodeset 0

# 3. IRQ アフィニティ最適化
echo 2 > /proc/irq/24/smp_affinity    # IRQ 24をCPU 1に固定

# KVM の利点：
echo "既存Linuxシステムとの統合"
echo "豊富な管理ツール（libvirt、oVirt）"
echo "コストパフォーマンス"
echo "オープンソース"
```

**QEMU/KVM の内部アーキテクチャ**

```bash
# QEMU プロセスの詳細分析
pmap -x $(pgrep qemu-system-x86_64)

# 主要メモリ領域：
# ゲストメモリ：実際のVMメモリ
# デバイスエミュレーション：仮想デバイス状態
# TCG：動的バイナリ変換（非KVM時）
# KVM：カーネルとのインターフェース

# QEMU Monitor での詳細情報
echo "info registers" | socat - UNIX-CONNECT:/tmp/monitor.sock
echo "info cpus" | socat - UNIX-CONNECT:/tmp/monitor.sock
echo "info memory-devices" | socat - UNIX-CONNECT:/tmp/monitor.sock

# KVM統計情報
cat /sys/kernel/debug/kvm/kvm_stat
# kvm statistics:
# efer_reload                 0
# exits                   12345
# fpu_reload               1234
# halt_exits                567
# halt_successful_poll      123
# halt_wakeup                44

# パフォーマンス分析
perf kvm stat record -p $(pgrep qemu)
perf kvm stat report

# VM Exit の最適化：
# 1. 頻発するExitの特定
# 2. virtio使用によるI/O Exit削減
# 3. CPU親和性設定によるキャッシュ効率向上
```

**VirtualBox の開発・テスト特化**

```bash
# VirtualBox の特徴
# デスクトップ仮想化に特化した設計

# Guest Additions による統合機能
# ホスト-ゲスト間でのファイル共有、クリップボード共有

# Snapshot機能
VBoxManage snapshot vm-name take "snapshot-name"
VBoxManage snapshot vm-name restore "snapshot-name"

# ネストした仮想化
VBoxManage modifyvm vm-name --nested-hw-virt on

# 性能特性：
echo "デスクトップ用途：優秀"
echo "サーバー用途：制限的"
echo "管理の簡単さ：最優秀"
echo "エンタープライズ機能：限定的"

# 適用場面：
echo "開発環境"
echo "テスト環境"  
echo "教育・トレーニング"
echo "デモンストレーション"
```

## 8.5 コンテナ技術の実装詳細

### namespace：プロセス分離の仕組み

コンテナ技術は、OS レベルでの仮想化により、軽量な分離環境を実現する。namespace はその中核技術の一つである。

**Linuxネームスペースの種類**

```bash
# 利用可能な namespace の確認
ls /proc/self/ns/
# cgroup  ipc  mnt  net  pid  pid_for_children  user  uts

# 各 namespace の詳細：

# 1. PID namespace：プロセスID空間の分離
unshare --pid --fork --mount-proc bash
ps aux
# PID 1 から始まる独立したプロセス空間

# 2. Network namespace：ネットワーク空間の分離
ip netns add container1
ip netns exec container1 ip link list
# lo: <LOOPBACK> mtu 65536 qdisc noop state DOWN mode DEFAULT
# 独立したネットワークスタック

# 3. Mount namespace：ファイルシステム空間の分離
unshare --mount bash
mount -t tmpfs tmpfs /tmp
# 他のプロセスに影響しない独立したマウント空間

# 4. UTS namespace：ホスト名の分離
unshare --uts bash
hostname container-host
hostname  # container-host（他のプロセスは影響なし）

# 5. IPC namespace：プロセス間通信の分離
unshare --ipc bash
ipcs -q  # 独立したメッセージキュー空間

# 6. User namespace：ユーザーID空間の分離
unshare --user bash
id  # uid=65534(nobody) gid=65534(nogroup)
# 内部では異なるUID/GIDマッピング

# 7. Cgroup namespace：cgroup階層の分離
unshare --cgroup bash
cat /proc/self/cgroup
# 独立したcgroup階層ビュー
```

**namespace の実装原理**

```bash
# namespace 作成のシステムコール
# clone() システムコールにフラグを指定
clone(CLONE_NEWPID | CLONE_NEWNET | CLONE_NEWNS, ...)

# または unshare() システムコール  
unshare(CLONE_NEWPID | CLONE_NEWNET | CLONE_NEWNS)

# namespace の確認
readlink /proc/self/ns/pid
# pid:[4026531836]

# 異なるプロセスの namespace 比較
readlink /proc/1/ns/pid
# pid:[4026531836]
readlink /proc/12345/ns/pid  
# pid:[4026532198]  ← 異なる namespace

# namespace への参加
nsenter --target 12345 --pid --net bash
# プロセス12345と同じPIDとネットワーク namespace で bash 起動

# Docker での namespace 確認
docker run -d --name test-container nginx
docker_pid=$(docker inspect -f '{{.State.Pid}}' test-container)
readlink /proc/$docker_pid/ns/pid
# 独立したPID namespace を確認
```

**namespace による分離効果**

```bash
# コンテナ内外でのプロセス可視性比較

# ホスト側
ps aux | wc -l
# 142  （多数のプロセス）

# コンテナ内
docker exec test-container ps aux
# USER       PID %CPU %MEM    VSZ   RSS TTY      STAT START   TIME COMMAND
# root         1  0.0  0.1  32932  5632 ?        Ss   10:00   0:00 nginx: master
# nginx       29  0.0  0.0  33472  2816 ?        S    10:00   0:00 nginx: worker
# 限定されたプロセス数のみ表示

# ネットワーク分離の確認
# ホスト側
ip addr show | grep inet
# 多数のネットワークインターフェース

# コンテナ内
docker exec test-container ip addr show
# 1: lo: <LOOPBACK,UP,LOWER_UP> mtu 65536
# 2: eth0@if123: <BROADCAST,MULTICAST,UP,LOWER_UP> mtu 1500
# 限定されたネットワークインターフェース

# ファイルシステム分離
# ホスト側
ls /
# bin boot dev etc home lib ...（完全なルートファイルシステム）

# コンテナ内  
docker exec test-container ls /
# bin boot dev etc home lib ...（コンテナ用のルートファイルシステム）
# ただし、ホストとは完全に独立
```

### cgroup：リソース制御の実装

Control Groups（cgroup）は、プロセスグループのリソース使用量を制限・監視する機能である。コンテナの動作リソースを制御する重要な仕組みである。

**cgroup v1 vs cgroup v2**

```bash
# cgroup バージョンの確認
mount | grep cgroup
# cgroup on /sys/fs/cgroup type cgroup (rw,nosuid,nodev,noexec,relatime,memory)
# cgroup2 on /sys/fs/cgroup type cgroup2 (rw,nosuid,nodev,noexec,relatime,nsdelegate)

# cgroup v1 の構造（コントローラー別）
ls /sys/fs/cgroup/
# blkio  cpu  cpuacct  cpuset  devices  freezer  hugetlb  memory  net_cls  net_prio  perf_event  pids  systemd

# cgroup v2 の統合構造
ls /sys/fs/cgroup/
# cgroup.controllers  cgroup.max.depth  cgroup.max.descendants  ...
# user.slice  system.slice  init.scope

# Docker での cgroup 使用状況
docker run -d --memory=512m --cpus=1.5 --name resource-test nginx

# メモリ制限の確認（cgroup v1）
cat /sys/fs/cgroup/memory/docker/$(docker inspect -f '{{.Id}}' resource-test)/memory.limit_in_bytes
# 536870912  （512MB）

# CPU制限の確認
cat /sys/fs/cgroup/cpu/docker/$(docker inspect -f '{{.Id}}' resource-test)/cpu.cfs_quota_us
# 150000
cat /sys/fs/cgroup/cpu/docker/$(docker inspect -f '{{.Id}}' resource-test)/cpu.cfs_period_us  
# 100000
# 150000/100000 = 1.5 CPU cores
```

**リソース制御の詳細設定**

```bash
# メモリ制御の詳細
echo 268435456 > /sys/fs/cgroup/memory/test_group/memory.limit_in_bytes  # 256MB制限
echo 134217728 > /sys/fs/cgroup/memory/test_group/memory.soft_limit_in_bytes  # 128MB soft制限

# メモリ使用状況の監視
cat /sys/fs/cgroup/memory/test_group/memory.usage_in_bytes
cat /sys/fs/cgroup/memory/test_group/memory.stat
# cache 12345678
# rss 8765432
# mapped_file 2345678
# pgfault 123456
# pgmajfault 789

# CPU制御（Completely Fair Scheduler 統合）
echo 51200 > /sys/fs/cgroup/cpu/test_group/cpu.cfs_quota_us   # 50%制限
echo 100000 > /sys/fs/cgroup/cpu/test_group/cpu.cfs_period_us # 100ms周期

# CPU統計情報
cat /sys/fs/cgroup/cpu/test_group/cpu.stat
# nr_periods 1234
# nr_throttled 56
# throttled_time 789012345

# ブロックI/O制御
echo "8:0 1048576" > /sys/fs/cgroup/blkio/test_group/blkio.throttle.read_bps_device
# デバイス8:0（通常 /dev/sda）への読み込みを1MB/sに制限

# I/O統計
cat /sys/fs/cgroup/blkio/test_group/blkio.io_service_bytes
# 8:0 Read 12345678
# 8:0 Write 8765432
# 8:0 Sync 9876543
# 8:0 Async 11111111
```

**Docker でのリソース制御実践**

```bash
# 包括的なリソース制限
docker run -d \
  --memory=1g \              # メモリ制限
  --memory-swap=2g \         # スワップ込み制限
  --cpus=1.5 \              # CPU制限
  --cpu-shares=512 \         # CPU重み（デフォルト1024）
  --blkio-weight=500 \       # I/O重み（デフォルト500）
  --device-read-bps=/dev/sda:1mb \  # 読み込み帯域制限
  --device-write-bps=/dev/sda:1mb \ # 書き込み帯域制限
  --pids-limit=100 \         # プロセス数制限
  --ulimit nofile=1000:2000 \ # ファイルディスクリプタ制限
  --name resource-controlled nginx

# リソース使用量の監視
docker stats resource-controlled
# CONTAINER    CPU %   MEM USAGE / LIMIT   MEM %   NET I/O       BLOCK I/O   PIDS
# resource     45.2%   512MiB / 1GiB       50.0%   1.2kB/648B    1.2MB/0B    15

# cgroup イベント監視
docker exec resource-controlled cat /sys/fs/cgroup/memory/memory.oom_control
# oom_kill_disable 0
# under_oom 0
# oom_kill 0

# プロセス単位での cgroup 制御
systemd-run --uid=testuser --gid=testgroup --slice=user-test.slice \
  --property=MemoryLimit=256M --property=CPUQuota=50% \
  command_to_run
```

### overlayfsとイメージ管理

OverlayFS は、複数のディレクトリを重ね合わせて単一のファイルシステムビューを提供する技術である。Dockerなどのコンテナランタイムで、効率的なイメージ管理を実現している。

**OverlayFS の基本構造**

```bash
# OverlayFS のマウント構成
# lowerdir：読み取り専用の下位層（複数可）
# upperdir：読み書き可能な上位層
# workdir：OverlayFS内部作業ディレクトリ
# merged：統合されたビュー（マウントポイント）

# 手動でのOverlayFS作成例
mkdir -p /tmp/overlay/{lower1,lower2,upper,work,merged}

# 下位層にファイル作成
echo "base file" > /tmp/overlay/lower1/file1.txt
echo "app file" > /tmp/overlay/lower2/file2.txt

# OverlayFS マウント
mount -t overlay overlay \
  -o lowerdir=/tmp/overlay/lower2:/tmp/overlay/lower1,upperdir=/tmp/overlay/upper,workdir=/tmp/overlay/work \
  /tmp/overlay/merged

# 統合ビューの確認
ls /tmp/overlay/merged/
# file1.txt  file2.txt

# 上位層での変更
echo "modified" > /tmp/overlay/merged/file1.txt  # 既存ファイル変更
echo "new file" > /tmp/overlay/merged/new.txt    # 新規ファイル作成

# 変更の確認
ls /tmp/overlay/upper/
# file1.txt  new.txt（変更・新規ファイルのみ上位層に保存）

ls /tmp/overlay/lower1/
# file1.txt（元ファイルは変更されず）
```

**Docker でのOverlayFS使用**

```bash
# Docker のストレージドライバ確認
docker info | grep "Storage Driver"
# Storage Driver: overlay2

# Docker イメージの層構造確認
docker pull nginx:latest
docker history nginx:latest

# 出力例：
# IMAGE          CREATED        CREATED BY                                      SIZE      COMMENT
# 92b11f67642b   2 weeks ago    /bin/sh -c #(nop)  CMD ["nginx" "-g" "daemon   0B        
# <missing>      2 weeks ago    /bin/sh -c #(nop)  STOPSIGNAL SIGQUIT           0B        
# <missing>      2 weeks ago    /bin/sh -c #(nop)  EXPOSE 80                    0B        
# <missing>      2 weeks ago    /bin/sh -c #(nop) COPY file:0fd5fca330dcd6a7   1.04kB    
# <missing>      2 weeks ago    /bin/sh -c #(nop) COPY file:08a7c0ce69a54a72   4.61kB    

# イメージ層の物理的な場所
ls /var/lib/docker/overlay2/
# 各層がディレクトリとして保存

# 特定コンテナの層構造確認
docker run -d --name test-nginx nginx
docker inspect test-nginx | grep -A 10 '"GraphDriver"'

# 出力例：
# "GraphDriver": {
#     "Data": {
#         "LowerDir": "/var/lib/docker/overlay2/abcd1234.../diff:/var/lib/docker/overlay2/efgh5678.../diff",
#         "MergedDir": "/var/lib/docker/overlay2/ijkl9012.../merged",
#         "UpperDir": "/var/lib/docker/overlay2/ijkl9012.../diff",
#         "WorkDir": "/var/lib/docker/overlay2/ijkl9012.../work"
#     },
#     "Name": "overlay2"
# }
```

**Copy-on-Write の効果測定**

```bash
# 同一イメージから複数コンテナ起動
for i in {1..5}; do
  docker run -d --name nginx-$i nginx sleep 3600
done

# ディスク使用量の確認
docker system df
# TYPE            TOTAL     ACTIVE    SIZE      RECLAIMABLE
# Images          1         0         133.3MB   133.3MB (100%)
# Containers      5         5         25B       0B (0%)
# Local Volumes   0         0         0B        0B
# Build Cache     0         0         0B        0B

# 実際のディスク使用量
du -sh /var/lib/docker/overlay2/*/diff | grep -v "4.0K"

# 結果：
# - ベースイメージ：133.3MB（1回のみ）
# - 各コンテナ：数KB（変更分のみ）
# - 5コンテナでも総使用量：約133.5MB

# ファイル変更時のCopy-on-Write動作確認
docker exec nginx-1 sh -c "echo 'modified' > /etc/nginx/nginx.conf"

# 変更したコンテナの上位層を確認
container_id=$(docker inspect -f '{{.Id}}' nginx-1)
upper_dir="/var/lib/docker/overlay2/${container_id:0:12}*/diff"
find $upper_dir -name "nginx.conf" -type f
# /var/lib/docker/overlay2/abc123.../diff/etc/nginx/nginx.conf

# 他のコンテナは影響を受けない
docker exec nginx-2 cat /etc/nginx/nginx.conf
# 元の設定ファイル内容（変更されていない）
```

**イメージ最適化のベストプラクティス**

```bash
# レイヤー数を最小化するDockerfile例

# 悪い例（レイヤー数が多い）
FROM ubuntu:24.04
RUN apt-get update
RUN apt-get install -y nginx
RUN apt-get install -y curl
RUN apt-get clean
RUN rm -rf /var/lib/apt/lists/*

# 良い例（レイヤー数を最小化）
FROM ubuntu:24.04
RUN apt-get update && \
    apt-get install -y nginx curl && \
    apt-get clean && \
    rm -rf /var/lib/apt/lists/*

# マルチステージビルドによる最適化
FROM golang:1.19 AS builder
WORKDIR /app
COPY . .
RUN go build -o main .

FROM alpine:latest
RUN apk --no-cache add ca-certificates
COPY --from=builder /app/main /main
ENTRYPOINT ["/main"]

# .dockerignore による不要ファイル除外
echo ".git
*.log
node_modules
*.tmp" > .dockerignore

# イメージサイズの比較
docker images --format "table {{.Repository}}\t{{.Tag}}\t{{.Size}}"
# REPOSITORY    TAG       SIZE
# app-multi     latest    10.2MB   ← マルチステージビルド
# app-single    latest    350MB    ← 単一ステージビルド
```

## まとめ

仮想化技術は、物理リソースの抽象化という共通の目標を持ちながら、その実装アプローチは大きく異なっている。CPU、メモリ、I/O それぞれの仮想化技術は、ハードウェアの進歩とともに継続的に進化している。

ハイパーバイザー型仮想化は、完全な分離と高い互換性を提供する一方で、一定のオーバーヘッドが存在する。コンテナ型仮想化は、軽量性と効率性に優れるが、セキュリティ分離のレベルに制約がある。

重要なのは、これらの技術特性を理解し、アプリケーション要件に応じた適切な選択を行うことである。単一の技術ですべての要求を満たすことは困難であり、多くの場合、複数の仮想化技術を組み合わせたハイブリッドアプローチが現実的な解決策となる。

次章では、これらの仮想化基盤上で動作するシステムの運用自動化について探る。仮想化により複雑化したインフラストラクチャを、いかに効率的かつ信頼性高く管理するかという課題に取り組む。
