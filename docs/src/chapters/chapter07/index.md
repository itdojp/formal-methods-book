# 第7章：ストレージアーキテクチャ

データの永続化を担うストレージシステムは、単なるデータの入れ物ではない。アクセスパターン、信頼性要求、性能目標に応じて、適切なストレージアーキテクチャを選択し、最適化することが重要である。

なぜRAIDは複数のレベルに分かれているのか。ファイルシステムによって性能と機能がなぜこれほど違うのか。バックアップ戦略において、なぜRPOとRTOという概念が重要なのか。これらの背景には、信頼性、性能、コストの間の複雑なトレードオフが存在している。

## 7.1 ブロックデバイスの抽象化層

### デバイスマッパーの実装原理

Linux のブロックデバイス管理において、デバイスマッパー（Device Mapper）は重要な抽象化層を提供する。物理的なブロックデバイスを論理的に組み合わせ、より高度な機能を実現する。

**デバイスマッパーの基本構造**

```
アプリケーション
    ↓
ファイルシステム（ext4, XFS等）
    ↓  
仮想ファイルシステム（VFS）
    ↓
ブロック層
    ↓
デバイスマッパー （← ここで論理的な変換）
    ↓
物理デバイスドライバ（SCSI, NVMe等）
    ↓
実際のストレージデバイス
```

**論理ボリューム管理（LVM）**

LVMは、デバイスマッパーを基盤とした論理ボリューム管理システムである：

```bash
# 物理ボリューム（PV）の作成
pvcreate /dev/sdb1 /dev/sdc1

# ボリュームグループ（VG）の作成
vgcreate vg_data /dev/sdb1 /dev/sdc1

# 論理ボリューム（LV）の作成
lvcreate -L 500G -n lv_database vg_data

# 結果として作成されるデバイス
ls -l /dev/mapper/vg_data-lv_database
# /dev/mapper/vg_data-lv_database -> ../dm-2

# デバイスマッパーテーブルの確認
dmsetup table vg_data-lv_database
# 出力例：
# 0 1048576000 linear 8:17 0
# 意味：セクタ0から1048576000まで、8:17（/dev/sdb1）のセクタ0から線形マッピング
```

**ストライピングによる性能向上**

```bash
# 複数デバイスにわたるストライピング
lvcreate -L 1T -i 2 -I 64 -n lv_stripe vg_data
# -i 2: 2つのデバイスにストライピング
# -I 64: 64KBのストライプサイズ

# デバイスマッパーテーブル
dmsetup table vg_data-lv_stripe
# 出力例：
# 0 2097152000 striped 2 128 8:17 0 8:33 0
# 意味：2つのデバイスに128セクタ（64KB）単位でストライピング

# 性能効果の測定
fio --name=stripe_test --rw=read --bs=64k --size=1G \
    --filename=/dev/mapper/vg_data-lv_stripe --direct=1

# 期待される効果：
# 単一デバイス：500MB/s
# 2-way stripe：900〜1000MB/s（理論値の90〜95%）
```

**スナップショット機能**

```bash
# 読み書き可能スナップショットの作成
lvcreate -L 100G -s -n lv_database_snap /dev/vg_data/lv_database

# Copy-on-Write（COW）の動作原理：
# 1. スナップショット作成時：メタデータのみコピー
# 2. 元ボリュームへの書き込み発生時：
#    a. 書き込み対象の元データをスナップショット領域に退避
#    b. 新しいデータを元ボリュームに書き込み
# 3. スナップショットからの読み込み：
#    - 変更されたブロック：スナップショット領域から読み込み  
#    - 未変更ブロック：元ボリュームから読み込み

# パフォーマンス影響の監視
dmsetup status vg_data-lv_database_snap
# 出力例：
# 0 1048576000 snapshot 204800/204800 2048
# 意味：204800セクタ中204800セクタ使用、2048セクタのチャンクサイズ

# 使用率が90%を超えた場合の警告設定
lvdisplay vg_data/lv_database_snap | grep "Allocated to snapshot"
```

### I/Oスケジューラーの選択基準

I/Oスケジューラーは、アプリケーションからの I/O要求を適切な順序で物理デバイスに送信する役割を担う。デバイスの特性とワークロードに応じた適切な選択が重要である。

**従来型HDDでのスケジューリング**

回転ディスクでは、物理的なシーク時間が性能を大きく左右する：

```bash
# CFQ（Complete Fair Queuing）スケジューラー
echo cfq > /sys/block/sda/queue/scheduler

# CFQの特徴：
# - プロセスごとのキューを維持
# - タイムスライスベースの公平性
# - シーク距離を考慮した最適化
# - 読み込み優先（レイテンシ重視）

# パラメータ調整例
echo 8 > /sys/block/sda/queue/iosched/quantum        # タイムスライスあたりのリクエスト数
echo 300 > /sys/block/sda/queue/iosched/slice_sync   # 同期I/Oのタイムスライス（ms）
echo 100 > /sys/block/sda/queue/iosched/slice_async  # 非同期I/Oのタイムスライス（ms）

# Deadline スケジューラー（低レイテンシ重視）
echo deadline > /sys/block/sda/queue/scheduler

# Deadlineの特徴：
# - 読み込み・書き込み別のキュー
# - デッドライン制限（読み込み500ms、書き込み5s）
# - エレベーターアルゴリズム（シーク最適化）

echo 500 > /sys/block/sda/queue/iosched/read_expire   # 読み込みデッドライン
echo 5000 > /sys/block/sda/queue/iosched/write_expire # 書き込みデッドライン
```

**SSDでの最適化**

SSDでは、シーク時間が存在しないため、異なる最適化戦略が必要：

```bash
# NOOP スケジューラー（SSD推奨）
echo noop > /sys/block/nvme0n1/queue/scheduler

# NOOPの特徴：
# - 最小限の並び替えのみ
# - オーバーヘッドが最小
# - SSDの内部スケジューリングに委ねる

# mq-deadline（マルチキュー対応）
echo mq-deadline > /sys/block/nvme0n1/queue/scheduler

# マルチキューの利点：
# - CPUコアごとの独立したキュー
# - NUMA親和性の向上
# - スケーラビリティの改善

# キュー深度の確認と調整
cat /sys/block/nvme0n1/queue/nr_requests    # デフォルト：128
echo 256 > /sys/block/nvme0n1/queue/nr_requests

# NVMe の場合、デバイス固有のキュー設定
cat /sys/block/nvme0n1/queue/max_hw_sectors_kb  # ハードウェア最大値
cat /sys/block/nvme0n1/queue/max_sectors_kb     # カーネル制限値
```

**ワークロード別の最適化**

```bash
# データベースワークロード（小サイズ、低レイテンシ）
echo mq-deadline > /sys/block/nvme0n1/queue/scheduler
echo 16 > /sys/block/nvme0n1/queue/iosched/writes_starved  # 読み込み優先度向上
echo 1 > /sys/block/nvme0n1/queue/iosched/front_merges     # フロントマージ有効

# ストリーミング・バックアップ（大サイズ、スループット）
echo noop > /sys/block/nvme0n1/queue/scheduler
echo 1024 > /sys/block/nvme0n1/queue/max_sectors_kb        # 大きなI/Oサイズ許可
echo 512 > /sys/block/nvme0n1/queue/nr_requests            # 深いキュー

# 仮想化環境（ゲストOS）
echo noop > /sys/block/vda/queue/scheduler
# ホストOSでスケジューリングを行うため、ゲストでは最小限に
```

**性能測定とチューニング**

```bash
# I/O性能の測定
iostat -x 1

# 重要な指標：
# r/s, w/s：読み書きIOPS
# rkB/s, wkB/s：読み書きスループット  
# await：平均応答時間
# %util：デバイス使用率

# fio による詳細測定
# ランダム読み込み（データベース想定）
fio --name=random_read --rw=randread --bs=4k --iodepth=32 \
    --size=1G --runtime=60 --time_based --filename=/dev/nvme0n1

# シーケンシャル書き込み（ログ想定）
fio --name=seq_write --rw=write --bs=64k --iodepth=1 \
    --size=1G --runtime=60 --time_based --filename=/dev/nvme0n1

# 結果の評価：
# IOPS：データベース用途では 50,000+ が目安
# スループット：ログ用途では 500MB/s+ が目安
# レイテンシ：P99レイテンシが 10ms以下が目安
```

## 7.2 RAID実装の詳細分析

### ソフトウェアRAIDとハードウェアRAIDの差異

RAID（Redundant Array of Independent Disks）は、複数の物理ディスクを組み合わせて、性能向上と冗長性確保を実現する技術である。実装方式により、特性と適用場面が大きく異なる。

**ハードウェアRAIDの特徴**

```
専用RAIDコントローラーによる実装：

利点：
1. CPU負荷の軽減：
   - ホストCPUはRAID処理に関与しない
   - 専用プロセッサーによる並列処理
   - 暗号化・圧縮の専用ハードウェア

2. 高速なキャッシュ：
   - 専用のWrite-Backキャッシュ（512MB〜8GB）
   - バッテリーバックアップ付き（停電時データ保護）
   - Read-Aheadキャッシュによる先読み

3. ホットスワップ対応：
   - 運用中のディスク交換
   - 自動リビルド開始
   - 管理ツールによる監視

制約：
1. ベンダーロックイン：
   - 特定ベンダーのディスクのみサポート
   - コントローラー故障時の代替困難
   - ライセンス費用

2. 可視性の制限：
   - OS からの詳細監視困難
   - デバッグ情報の制限
   - 性能チューニングの制約
```

**ソフトウェアRAIDの特徴**

Linux のmd（Multiple Device）による実装：

```bash
# RAID1（ミラーリング）の構築
mdadm --create /dev/md0 --level=1 --raid-devices=2 /dev/sdb1 /dev/sdc1

# RAID構成の確認
cat /proc/mdstat
# md0 : active raid1 sdc1[1] sdb1[0]
#       976762624 blocks super 1.2 [2/2] [UU]

# 詳細情報の確認
mdadm --detail /dev/md0

# ソフトウェアRAIDの利点：
# 1. 柔軟性：任意のディスクでRAID構成可能
# 2. 可視性：詳細な状態監視とログ
# 3. コスト：追加ハードウェア不要
# 4. 移植性：異なるハードウェア間での移行可能

# CPU使用量の測定
iostat -c 1 & # CPU使用率監視
dd if=/dev/zero of=/dev/md0 bs=1M count=1000 oflag=direct
# RAID5/6では書き込み時にパリティ計算によるCPU負荷発生
```

**パフォーマンス比較**

```bash
# ベンチマーク測定例

# ハードウェアRAID（LSI MegaRAID）
fio --name=hw_raid --filename=/dev/sda --rw=randwrite --bs=4k \
    --iodepth=32 --size=1G --runtime=60

# 結果例：
# IOPS: 45,000
# CPU使用率: 15%
# レイテンシ: 0.7ms

# ソフトウェアRAID（Linux md）
fio --name=sw_raid --filename=/dev/md0 --rw=randwrite --bs=4k \
    --iodepth=32 --size=1G --runtime=60

# 結果例：
# IOPS: 42,000
# CPU使用率: 25%
# レイテンシ: 0.8ms

# 性能差の要因：
# 1. 専用キャッシュの有無
# 2. CPU処理オーバーヘッド
# 3. 最適化されたファームウェア
```

### RAIDレベル選択の判断基準

各RAIDレベルは、性能、容量効率、耐障害性の異なるトレードオフを提供する。適切な選択には、アプリケーション要件の明確な理解が必要である。

**RAID0（ストライピング）**

```bash
# 構築例
mdadm --create /dev/md0 --level=0 --raid-devices=4 \
      /dev/sdb1 /dev/sdc1 /dev/sdd1 /dev/sde1

# 特性：
# 容量効率：100%（全ディスク容量を利用）
# 耐障害性：なし（1台故障で全データ喪失）
# 性能：読み書き共に台数倍

# 適用場面：
# - 一時的な高速ストレージ（動画編集等）
# - データ損失が許容される環境
# - 高い読み書き性能が必要

# パフォーマンス測定
fio --name=raid0_test --filename=/dev/md0 --rw=read --bs=1M \
    --iodepth=1 --size=4G

# 期待値：
# 4台構成：単一ディスクの約3.5〜3.8倍の性能
# 理論値に対する効率：85〜95%
```

**RAID1（ミラーリング）**

```bash
# 特性：
# 容量効率：50%（半分の容量がミラー用）
# 耐障害性：1台故障まで許容
# 読み込み性能：約2倍（並列読み込み）
# 書き込み性能：単一ディスクと同等

# 適用場面：
# - データベースのトランザクションログ
# - 重要なシステムファイル
# - 高い可用性が要求される環境

# 障害時の動作確認
mdadm /dev/md0 --fail /dev/sdb1  # ディスク故障をシミュレート
cat /proc/mdstat
# md0 : active raid1 sdc1[1] sdb1[0](F)
#       976762624 blocks super 1.2 [2/1] [_U]

# 故障ディスクの交換
mdadm /dev/md0 --remove /dev/sdb1
mdadm /dev/md0 --add /dev/sdf1     # 新しいディスクを追加

# 自動リビルド開始
# リビルド中の性能影響：通常の60〜80%
```

**RAID5（分散パリティ）**

```bash
# 構築例（最小3台）
mdadm --create /dev/md0 --level=5 --raid-devices=3 \
      /dev/sdb1 /dev/sdc1 /dev/sdd1

# 特性：
# 容量効率：(n-1)/n × 100%（3台なら67%）
# 耐障害性：1台故障まで許容
# 読み込み性能：(n-1)倍
# 書き込み性能：複雑（パリティ計算）

# 書き込み処理の詳細：
# 1. 既存データとパリティを読み込み
# 2. 新しいパリティを計算
# 3. データとパリティを書き込み
# 結果：小さな書き込みで4回のディスクアクセス

# チューニングパラメータ
echo 8192 > /sys/block/md0/md/stripe_cache_size  # キャッシュサイズ増加
echo 1024 > /sys/block/md0/md/group_thread_cnt   # 処理スレッド数調整

# Write Holeの対策
echo write-intent > /sys/block/md0/md/bitmap  # 書き込み意図ビットマップ
```

**RAID6（二重パリティ）**

```bash
# 特性：
# 容量効率：(n-2)/n × 100%（4台なら50%）
# 耐障害性：2台同時故障まで許容
# 書き込み性能：RAID5より更に低下（複雑なパリティ計算）

# 適用判断：
# - 大容量ディスク（>2TB）使用時
# - リビルド時間中の2次故障リスクが高い
# - 高い可用性要求

# リビルド時間の計算：
# 4TB ディスク、100MB/s リビルド速度の場合
# 時間 = 4TB / 100MB/s = 40,000秒 ≈ 11時間

# この間の2次故障確率：
# AFR（年間故障率）0.5%のディスクの場合
# 11時間での故障確率 ≈ 0.0006%
# 10台構成なら 0.006%（無視できないレベル）
```

**適用指針のまとめ**

| 用途 | 推奨RAID | 理由 |
|------|----------|------|
| OS・システム | RAID1 | 高い可用性、高速起動 |
| データベースデータ | RAID10 | 高性能＋高可用性 |
| ログファイル | RAID1 | 書き込み性能重視 |
| バックアップ | RAID5/6 | 容量効率重視 |
| 一時作業領域 | RAID0 | 性能最優先 |

## 7.3 ファイルシステムの設計思想比較

### ext4：安定性重視の設計

ext4は、ext3の後継として開発されたファイルシステムである。下位互換性を保ちながら、性能と機能を大幅に向上させている。

**ext4の主要機能**

```bash
# ext4ファイルシステムの作成
mkfs.ext4 -F /dev/md0

# 主要な改善点の確認
tune2fs -l /dev/md0 | grep -E "(features|Block size|Inode size)"

# Filesystem features:      has_journal ext_attr resize_inode dir_index 
#                           filetype needs_recovery extent 64bit flex_bg 
#                           sparse_super large_file huge_file uninit_bg 
#                           dir_nlink extra_isize metadata_csum

# 重要な機能：
# 1. extent：連続ブロックの効率的管理
# 2. delayed allocation：書き込み遅延による最適化
# 3. multiblock allocation：連続ブロック確保
# 4. journal checksumming：ジャーナルの整合性確保
```

**エクステント（Extent）による効率化**

従来のext3では、ファイルの各ブロックを個別に管理していたが、ext4では連続ブロックをエクステントとして管理：

```bash
# エクステント情報の確認
debugfs -R "extent /path/to/large_file" /dev/md0

# 出力例：
# Level Entries       Logical      Physical Length Flags
#  0/ 1   1/  1     0 -  262143    65536 -  327679 262144 
#  0/ 1   2/  2 262144 -  524287   327680 -  590335 262144

# 解釈：
# 大きなファイルが2つのエクステントで構成
# 各エクステントは262,144ブロック（1GB、4KBブロック時）の連続領域

# パフォーマンスへの影響：
# - ファイル断片化の大幅な削減
# - メタデータサイズの削減
# - シーケンシャルアクセスの高速化
```

**遅延アロケーション（Delayed Allocation）**

```bash
# 遅延アロケーションの動作原理：
# 1. write()システムコール：メモリ上のページキャッシュに書き込み
# 2. ディスク書き込み遅延：実際のブロック割り当てを遅延
# 3. flush時に最適配置：連続した空きブロックに配置

# 効果の測定
echo 3 > /proc/sys/vm/drop_caches  # キャッシュクリア

# 小さなファイルを大量作成（遅延アロケーションのテスト）
time for i in {1..1000}; do echo "test data" > test_$i.txt; done

# sync後の断片化確認
sync
filefrag test_*.txt | grep -c "1 extent"  # 1エクステントのファイル数

# 遅延アロケーション無効化での比較
mount -o nodelalloc /dev/md0 /mnt/test
# 通常、断片化が増加し、性能が低下する
```

**ジャーナリング機能**

```bash
# ジャーナルモードの設定
tune2fs -o journal_data_writeback /dev/md0  # writeback（高速）
tune2fs -o journal_data_ordered /dev/md0    # ordered（デフォルト）
tune2fs -o journal_data /dev/md0            # journal（安全）

# 各モードの特徴：
# writeback：メタデータのみジャーナル、データは順序保証なし
# ordered：メタデータをジャーナル、データは事前書き込み
# journal：メタデータとデータの両方をジャーナル

# パフォーマンス測定
fio --name=journal_test --rw=randwrite --bs=4k --fsync=1 \
    --size=1G --filename=/mnt/test/testfile

# 結果例（相対値）：
# writeback: 100%（基準）
# ordered: 85%
# journal: 60%
```

### XFS：大規模ファイル対応の最適化

XFSは、Silicon Graphics（SGI）で開発された高性能ファイルシステムである。大規模ファイルと高いスループットに最適化されている。

**XFSの特徴的機能**

```bash
# XFSファイルシステムの作成
mkfs.xfs -f /dev/md0

# アロケーショングループの確認
xfs_info /dev/md0

# 出力例：
# meta-data=/dev/md0      isize=512    agcount=8, agsize=31457280 blks
# data     =              bsize=4096   blocks=251658240, imaxpct=25
# naming   =version 2     bsize=4096   ascii-ci=0 ftype=1
# log      =internal      bsize=4096   blocks=122880, version=2

# 重要なパラメータ：
# agcount：アロケーショングループ数（並列処理の単位）
# agsize：各グループのサイズ
# bsize：ブロックサイズ
```

**アロケーショングループによるスケーラビリティ**

```bash
# アロケーショングループの詳細分析
xfs_db -r -c "sb 0" -c "print agcount agblocks" /dev/md0

# 各グループは独立してメタデータを管理：
# - 独立したビットマップ
# - 独立したinode空間  
# - 並列アロケーション可能

# 並列書き込み性能の測定
fio --name=parallel_write --rw=write --bs=1M --numjobs=8 \
    --size=1G --filename_format=/mnt/xfs/testfile.\$jobnum \
    --group_reporting

# XFSの利点：
# - 複数スレッドでの並列書き込みが効率的
# - ファイル作成の並列性
# - 大規模ディスクでのスケーラビリティ
```

**リアルタイムサブボリューム**

```bash
# リアルタイム用の専用デバイス設定
mkfs.xfs -f -r rtdev=/dev/sdd1,size=100g /dev/md0

# リアルタイムファイルの作成
xfs_io -c "realtimeio" -c "extsize 1m" -f /mnt/xfs/realtime_file

# 特徴：
# - ファイルデータを専用デバイスに配置
# - 連続した領域の確保
# - データベースやストリーミング用途に最適

# 効果の確認
xfs_bmap -r /mnt/xfs/realtime_file
# リアルタイムデバイス上のエクステント情報表示
```

**defragmentation**

```bash
# XFSの断片化確認
xfs_db -r -c frag /dev/md0

# オンライン断片化解消
xfs_fsr /mnt/xfs  # ファイルシステム全体
xfs_fsr /mnt/xfs/large_file  # 特定ファイル

# 断片化の監視
xfs_db -r -c "frag -f" /dev/md0 | head -20
# 断片化率の高いファイルをリスト表示
```

### ZFS：統合的アプローチの利点と課題

ZFS（Zettabyte File System）は、Sun Microsystemsで開発された次世代ファイルシステムである。ファイルシステム、ボリューム管理、RAID機能を統合している。

**ZFSの革新的機能**

```bash
# ZFSプールの作成
zpool create datapool raidz2 /dev/sdb /dev/sdc /dev/sdd /dev/sde

# プール状態の確認
zpool status datapool

# データセットの作成
zfs create datapool/database
zfs create datapool/backup

# ZFSの統合的アプローチ：
# 1. プール：物理ストレージの抽象化層
# 2. データセット：論理的なファイルシステム
# 3. vdev：冗長性とパフォーマンスの管理単位
```

**Copy-on-Write と スナップショット**

```bash
# スナップショットの作成（瞬時）
zfs snapshot datapool/database@backup_20241201

# スナップショット一覧
zfs list -t snapshot

# ロールバック
zfs rollback datapool/database@backup_20241201

# Copy-on-Writeの利点：
# 1. 瞬時のスナップショット作成
# 2. スペース効率的な管理
# 3. データ整合性の保証

# スナップショット間の差分確認
zfs diff datapool/database@backup_20241201 datapool/database
```

**組み込まれたデータ整合性確保**

```bash
# チェックサム設定の確認
zfs get checksum datapool/database

# 利用可能なチェックサム：
# fletcher2, fletcher4, sha256, sha512, skein, edonr

# データスクラビング（整合性チェック）
zpool scrub datapool

# スクラブ状況の確認
zpool status -v datapool

# 自動修復機能：
# - 読み込み時のチェックサム検証
# - エラー検出時の自動修復（冗長性がある場合）
# - 修復不可能エラーの記録
```

**圧縮と重複排除**

```bash
# 圧縮の有効化
zfs set compression=lz4 datapool/database

# 圧縮率の確認
zfs get compressratio datapool/database

# 重複排除の有効化（注意：大量のRAMが必要）
zfs set dedup=on datapool/backup

# 重複排除率の確認
zpool get dedupratio datapool

# メモリ要件の見積もり：
# 重複排除テーブル：1GBのユニークデータあたり約5GBのRAM
# 大規模環境では慎重な検討が必要
```

**ZFSの課題**

```bash
# ライセンス問題：
# - CDDLライセンス（Linuxカーネルと非互換）
# - ユーザー空間での実装（ZFS on Linux/OpenZFS）
# - パフォーマンスオーバーヘッド

# メモリ使用量：
# ARC（Adaptive Replacement Cache）のサイズ確認
cat /proc/spl/kstat/zfs/arcstats | grep "size"

# ARCサイズ制限の設定
echo 8589934592 > /sys/module/zfs/parameters/zfs_arc_max  # 8GB制限

# パフォーマンス特性：
# - 書き込み：COWによる断片化
# - 読み込み：ARCによる高速化
# - CPUオーバーヘッド：チェックサム計算
```

## 7.4 ストレージ性能の最適化

### アライメントとブロックサイズの影響

ストレージデバイスの物理特性に合わせたアライメント設定は、性能に大きな影響を与える。特に、4Kネイティブセクターを持つ現代のSSDでは、この設定が重要である。

**4Kセクターアライメント**

```bash
# デバイスの物理セクターサイズ確認
cat /sys/block/nvme0n1/queue/physical_block_size    # 4096
cat /sys/block/nvme0n1/queue/logical_block_size     # 512

# パーティションのアライメント確認
fdisk -l /dev/nvme0n1

# 出力例：
# Device         Start      End  Sectors  Size Type
# /dev/nvme0n1p1  2048  2099199  2097152    1G Linux filesystem

# アライメント計算：
# 開始セクター 2048 × 512B = 1,048,576B = 1024KB
# 4KB = 4,096B で割り切れる → 正しくアライメント

# 非アライメントの問題例：
# 開始セクター 63 × 512B = 32,256B
# 4KB境界に合わない → 1回の論理書き込みで2回の物理書き込み発生
```

**ファイルシステムブロックサイズの最適化**

```bash
# 各ファイルシステムでのブロックサイズ設定

# ext4
mkfs.ext4 -b 4096 /dev/nvme0n1p1  # 4KBブロック

# XFS  
mkfs.xfs -b size=4096 /dev/nvme0n1p1

# ブロックサイズによる影響測定
for blocksize in 1024 2048 4096 8192; do
    echo "Testing block size: ${blocksize}"
    mkfs.ext4 -F -b $blocksize /dev/md1 >/dev/null 2>&1
    mount /dev/md1 /mnt/test
    
    # 小さなファイルの大量作成テスト
    time (for i in {1..1000}; do 
        echo "test data" > /mnt/test/file_$i.txt
    done; sync)
    
    umount /mnt/test
done

# 結果例：
# 1KB ブロック：遅い（メタデータオーバーヘッド大）
# 4KB ブロック：最適（デバイス特性と一致）
# 8KB ブロック：やや低下（無駄な読み込み発生）
```

**ストライプサイズの最適化**

```bash
# RAIDストライプサイズとファイルシステムの調整
# RAID5、3台構成、64KBストライプの場合

# 最適なファイルシステム設定
mkfs.xfs -f -d su=64k,sw=2 /dev/md0
# su: stripe unit（64KB）
# sw: stripe width（2、データディスク数）

# ext4での同等設定
mkfs.ext4 -F -E stride=16,stripe-width=32 /dev/md0
# stride: ストライプサイズ/ブロックサイズ = 64KB/4KB = 16
# stripe-width: stride × データディスク数 = 16 × 2 = 32

# パフォーマンス測定
fio --name=stripe_aligned --filename=/mnt/test/testfile \
    --rw=write --bs=128k --size=1G --direct=1

# 128KBの書き込みがストライプサイズの倍数になることで：
# - 単一ストライプへの書き込み
# - パリティ計算の最適化
# - 読み込み時の効率向上
```

### キャッシュ階層の活用戦略

現代のストレージシステムでは、複数レベルのキャッシュが性能に大きく影響する。各レベルの特性を理解し、適切に設定することが重要である。

**ページキャッシュの最適化**

```bash
# ページキャッシュの状況確認
cat /proc/meminfo | grep -E "(MemTotal|MemFree|Cached|Buffers)"

# 出力例：
# MemTotal:       32946720 kB  
# MemFree:         2347648 kB
# Buffers:          789312 kB   # ブロックデバイスキャッシュ
# Cached:         28934576 kB   # ページキャッシュ

# ページキャッシュ使用率：約88%（効果的に活用されている）

# ファイル毎のキャッシュ状況確認
vmtouch /path/to/database/file

# 出力例：
#            Files: 1
#      Directories: 0
#   Resident Pages: 245760/245760  100%
#         Elapsed: 0.123456 seconds

# 戦略的なキャッシュ管理
# 重要なファイルのプリロード
vmtouch -t /path/to/critical/files/*

# 大きなファイルでキャッシュが汚染される場合の対策
dd if=/dev/urandom of=/mnt/backup/large_file bs=1M count=10000 oflag=direct
# O_DIRECT使用によりページキャッシュをバイパス
```

**SSDキャッシュによる階層ストレージ**

```bash
# bcache による SSD キャッシュ設定
# バックングデバイス（HDD）の準備
make-bcache -B /dev/sdb1

# キャッシュデバイス（SSD）の準備  
make-bcache -C /dev/sdc1

# キャッシュセットの確認
ls /sys/fs/bcache/

# キャッシュセットの関連付け
echo [キャッシュセットUUID] > /sys/block/bcache0/bcache/attach

# キャッシュモードの設定
echo writeback > /sys/block/bcache0/bcache/cache_mode

# キャッシュモードの特徴：
# writethrough：書き込みは両方に、読み込みはキャッシュ優先
# writeback：書き込みはキャッシュのみ、後でバックングに反映
# writearound：書き込みはバックングのみ、読み込みのみキャッシュ

# キャッシュ効率の監視
cat /sys/block/bcache0/bcache/stats_total/cache_hits
cat /sys/block/bcache0/bcache/stats_total/cache_misses

# ヒット率の計算
# ヒット率 = ヒット数 / (ヒット数 + ミス数) × 100
```

**NVMeキャッシュの活用**

```bash
# Intel Optane のような高速NVMeをキャッシュとして使用
# dm-cache による設定

# メタデータデバイス（小容量SSD）
pvcreate /dev/nvme0n1p1
vgcreate cache_vg /dev/nvme0n1p1
lvcreate -L 1G -n cache_meta cache_vg

# キャッシュデバイス（高速NVMe）
lvcreate -L 100G -n cache_data cache_vg

# オリジンデバイス（大容量HDD）
pvcreate /dev/sdb1
vgcreate origin_vg /dev/sdb1  
lvcreate -L 1T -n origin_data origin_vg

# キャッシュの作成
dmsetup create cached --table "0 $(blockdev --getsz /dev/origin_vg/origin_data) cache \
  /dev/cache_vg/cache_meta /dev/cache_vg/cache_data /dev/origin_vg/origin_data \
  1 writethrough default 0"

# キャッシュ統計の確認
dmsetup status cached

# 出力例：
# 0 2097152000 cache 8 1024/1024 512 1847/2000 1 0 1 writethrough 2 \
#   migration_threshold 2048 mq 10 random_threshold 4 sequential_threshold 512

# 解釈：
# 1847/2000：ヒット/総アクセス → ヒット率92%
# migration_threshold：ホット判定の閾値
```

## 7.5 バックアップアーキテクチャの設計

### スナップショットの実装方式比較

スナップショット機能は、データの一貫性を保ちながら迅速なバックアップを可能にする重要な技術である。実装方式により、性能特性と制約が大きく異なる。

**Copy-on-Write（COW）方式**

```bash
# LVM スナップショット（COW実装）
lvcreate -L 10G -s -n database_snap /dev/vg_data/database

# COWの動作原理：
# 1. スナップショット作成：メタデータのみコピー（瞬時）
# 2. 元ボリュームへの書き込み時：
#    a. 変更前データをスナップショット領域にコピー
#    b. 新データを元ボリュームに書き込み
# 3. スナップショットからの読み込み：
#    - 変更済みブロック：スナップショット領域から
#    - 未変更ブロック：元ボリュームから

# パフォーマンス影響の測定
# スナップショット作成前
fio --name=baseline --filename=/dev/vg_data/database \
    --rw=randwrite --bs=4k --size=1G --runtime=60

# スナップショット作成後
lvcreate -L 5G -s -n db_snap /dev/vg_data/database
fio --name=with_snapshot --filename=/dev/vg_data/database \
    --rw=randwrite --bs=4k --size=1G --runtime=60

# 典型的な結果：
# ベースライン：20,000 IOPS
# スナップショット後：12,000 IOPS（40%低下）
# 原因：COW処理による追加I/O
```

**Redirect-on-Write（ROW）方式**

```bash
# ZFS スナップショット（ROW実装）
zfs snapshot datapool/database@backup_$(date +%Y%m%d_%H%M%S)

# ROWの動作原理：
# 1. スナップショット作成：メタデータのみコピー（瞬時）
# 2. 元データセットへの書き込み時：
#    a. 新しいブロックを別の場所に書き込み
#    b. メタデータを更新して新ブロックを指す
#    c. 元ブロックはスナップショットが参照し続ける

# パフォーマンス特性：
# - 書き込み性能への影響が最小
# - 断片化が進行する可能性
# - 読み込み性能は一時的に低下する場合がある

# スナップショット容量の確認
zfs list -t snapshot -o name,used,refer

# 出力例：
# NAME                                    USED  REFER
# datapool/database@backup_20241201_1000    0B   10G
# datapool/database@backup_20241201_1200  150M   10G
# datapool/database@backup_20241201_1400  280M   10G

# 各スナップショット作成後の変更量がUSED列に表示
```

**ストレージアレイレベルのスナップショット**

```bash
# ハードウェアRAIDコントローラーによるスナップショット
# （実装例：LSI MegaRAIDの場合）

# スナップショット機能の確認
MegaCli -LDInfo -Lall -aALL | grep -i snapshot

# スナップショット作成
MegaCli -LDMakeSnapshot -L0 -aALL

# 特徴：
# 1. ホストCPUに負荷をかけない
# 2. 専用ハードウェアによる高速処理
# 3. アプリケーションから透明
# 4. ベンダー固有の実装

# 利点：
# - 最小限のパフォーマンス影響
# - アプリケーション停止不要
# - 高速なリストア

# 制約：
# - ベンダーロックイン
# - 管理の複雑性
# - 容量制限（一般的に元ボリュームの10〜20%）
```

### RPO/RTOを満たすバックアップ戦略

Recovery Point Objective（RPO）とRecovery Time Objective（RTO）は、バックアップ戦略の要件を定義する重要な指標である。

**RPO/RTO要件の分析**

```
RPO（目標復旧時点）：データ損失の許容範囲
- RPO = 0：一切のデータ損失を許容しない（同期レプリケーション）
- RPO = 1時間：最大1時間分のデータ損失を許容
- RPO = 24時間：日次バックアップ（前日分まで復旧可能）

RTO（目標復旧時間）：システム停止の許容時間
- RTO = 1分：Hot Standby、自動フェイルオーバー
- RTO = 1時間：迅速な手動復旧プロセス
- RTO = 24時間：標準的な復旧プロセス

ビジネス影響の定量化：
時間当たりの損失 = (売上損失 + 生産性損失 + 機会損失) / 時間
例：ECサイト
- 売上損失：100万円/時間
- 信頼性損失：500万円（一回限り）
- RTO = 1時間なら最大600万円の損失
```

**段階的バックアップ戦略**

```bash
#!/bin/bash
# 包括的バックアップスクリプト例

# レベル0：フルバックアップ（週次）
if [ $(date +%w) -eq 0 ]; then  # 日曜日
    echo "Performing full backup..."
    
    # データベースのコンシステントバックアップ
    mysql -e "FLUSH TABLES WITH READ LOCK; SYSTEM snapshot_script.sh; UNLOCK TABLES;"
    
    # ファイルシステム全体のバックアップ  
    rsync -avz --delete /data/ backup-server:/backups/$(date +%Y%m%d)/
    
    # ZFSスナップショットのレプリケーション
    zfs send datapool/database@weekly_$(date +%Y%m%d) | \
        ssh backup-server zfs receive backup_pool/database_$(date +%Y%m%d)

# レベル1：増分バックアップ（日次）
else
    echo "Performing incremental backup..."
    
    # 前日からの変更のみ
    rsync -avz --link-dest=/backups/latest /data/ \
        backup-server:/backups/$(date +%Y%m%d)/
    
    # ZFS増分スナップショット
    zfs send -i @daily_$(date -d yesterday +%Y%m%d) \
        datapool/database@daily_$(date +%Y%m%d) | \
        ssh backup-server zfs receive backup_pool/database_inc
fi

# RPO/RTOの検証
# RPO：最新の日次バックアップまで（最大24時間）
# RTO：rsyncからのリストアに約4時間（1TBデータの場合）
```

**高可用性要求への対応**

```bash
# 同期レプリケーション（RPO=0）
# DRBD（Distributed Replicated Block Device）設定例

# drbd.conf設定
cat > /etc/drbd.d/database.res << EOF
resource database {
    device /dev/drbd0;
    disk /dev/vg_data/database;
    meta-disk internal;
    
    on primary-server {
        address 192.168.1.10:7788;
    }
    
    on secondary-server {
        address 192.168.1.11:7788;
    }
    
    syncer {
        verify-alg sha1;
        rate 100M;  # 同期速度制限
    }
    
    net {
        protocol C;  # 同期レプリケーション
        cram-hmac-alg sha1;
        shared-secret "secret_key";
    }
}
EOF

# 初期同期
drbdadm create-md database
drbdadm up database
drbdadm primary --force database

# 同期状況の監視
cat /proc/drbd
# version: 8.4.11 (api:1/proto:86-101)
# 0: cs:Connected ro:Primary/Secondary ds:UpToDate/UpToDate C r-----

# RPO=0の達成：
# - プライマリへの書き込み完了時点で、セカンダリも書き込み完了済み
# - ネットワーク障害やセカンダリ障害時は書き込みブロック（一貫性重視）

# 非同期レプリケーション（RPO>0、性能重視）
# Protocol B: ローカル書き込み＋ネットワーク送信完了で応答
# Protocol A: ローカル書き込み完了で応答（最高性能）
```

**災害復旧サイトでの運用**

```bash
# 地理的に分散したバックアップ
# AWS S3 Glacier Deep Archive への長期保存

aws configure set default.region us-west-2

# 月次フルバックアップのアーカイブ
tar czf - /data | aws s3 cp - s3://company-dr-backups/monthly/$(date +%Y%m).tar.gz \
    --storage-class DEEP_ARCHIVE

# 復旧時間の計算：
# - Deep Archive からの取り出し：12〜48時間
# - ダウンロード時間：1TBで約3時間（100Mbps接続時）
# - 展開・復旧時間：約2時間
# 総RTO：最大53時間

# より高速な復旧のためのハイブリッド戦略：
# 1. ローカル：日次増分（RTO: 4時間）
# 2. リージョン内：週次フル（RTO: 8時間）  
# 3. クロスリージョン：月次アーカイブ（RTO: 48時間）

# 復旧テストの自動化
#!/bin/bash
# 月次復旧テスト
restore_test() {
    local backup_date=$1
    echo "Testing restore from backup: $backup_date"
    
    # テスト環境での復元
    rsync -avz backup-server:/backups/$backup_date/ /test/restore/
    
    # データ整合性チェック
    md5sum -c /test/restore/checksums.md5
    
    # アプリケーション起動テスト
    systemctl start test-database
    
    # 機能テスト実行
    python /scripts/database_functional_test.py
    
    echo "Restore test completed: $(date)"
}

# 毎月第一日曜日に実行
if [ $(date +%d) -le 7 ] && [ $(date +%w) -eq 0 ]; then
    restore_test $(date -d "last month" +%Y%m%d)
fi
```

## まとめ

ストレージアーキテクチャの設計は、データの永続化という基本機能を超えて、システム全体の性能、可用性、運用性を左右する重要な要素である。ブロックデバイスの抽象化、RAID実装の選択、ファイルシステムの特性、バックアップ戦略。これらすべてが相互に関連し合い、全体としてのストレージソリューションを形成している。

特に重要なのは、技術的な優秀性だけでなく、実際の運用要件との適合性を考慮することである。ZFSは多くの優れた機能を提供するが、ライセンス制約や運用の複雑性がある。NVMeキャッシュは高性能だが、障害時の影響範囲が拡大する可能性がある。

現代のストレージ設計においては、これらのトレードオフを理解し、RPO/RTOなどの明確な要件に基づいた段階的なアプローチを取ることが重要である。完璧なソリューションを追求するのではなく、制約条件下での最適解を見つけることが、持続可能なストレージアーキテクチャの構築につながる。

次章では、このストレージ基盤の上で動作する仮想化技術の実装原理を探る。物理リソースを論理的に分割し、効率的に利用するための技術がどのような設計思想に基づいているかを詳細に解析する。