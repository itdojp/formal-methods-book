# CI examples

## PR向け（関連する軽量check）

ローカルで引数なしに実行すると、`pr-quick` 7件をすべて実行する。

```bash
bash examples/ci/pr-quick-check.sh
```

GitHub Actionsではbase/head SHAを渡し、`examples/example-manifest.json`のasset、reference、config、wrapperに関連するentryだけを選ぶ。
tool/example manifest、runner、bootstrap、workflow等の共通基盤が変わった場合は、fail-safeで全quick entryを実行する。

## Nightly matrix

scheduleと`workflow_dispatch`では、`matrix-plan` jobが次のplannerを使い、manifestで許可されたtool/profileだけをJSON matrixにする。

```bash
node scripts/plan-formal-matrix.js --event schedule --lane nightly --tool all
```

`tool-matrix`は`fail-fast: false`でtool単位に独立し、Alloy/TLC/Apalache/Dafnyのdeep profileと、SPIN/NuSMV/CBMC/Quint/PRISM/Tamarin/SymbiYosys/cvc5のnightly entryを実行する。
SPIN/NuSMVとcvc5だけが`examples/ci/prepare-tool.sh`からsource-build prerequisitesを導入する。cvc5は`rustup`、`build-essential`、`m4`だけを追加導入する。
PRISMはSHA-256を固定した公式Linux x86-64 archiveを一時取得し、tool binaryをartifactへ含めず数値結果だけを保持する。
Tamarinと対応Maudeも固定公式archiveから毎回再展開し、tool binaryではなくlemma結果と欠陥版のattack graphだけを保持する。
cvc5はchecksum、member数、展開size、layoutを検査した公式ZIPを毎回安全に再展開する。Carcaraも同じ境界でsource archiveを再展開してCargo.lockを照合後、Rust 1.87.0で毎回`--locked` rebuildする。Rustの公式channel manifest digestはprovenance sentinelとして検査し、rustup導入後のrustc/Cargo commitとhostも照合する。cvc5/Carcara binaryやarchiveはartifactへ含めず、1 MiB上限を満たす`certificate.alethe`、64 KiB上限のchecker output、`results.json`、`summary.log`だけを保持する。checker bypass、holes、`--ignore-unknown-rules`、`--allowed-rules`は使用しない。
1 toolが失敗しても、他toolの実行とartifact uploadは継続する。

## Optional / manual

Kaniは追加の公式archiveと固定Rust nightlyを必要とするため、scheduleやPRから実行しない。
Actionsの`workflow_dispatch`で`lane=optional`、`tool=kani`または`all`を明示して実行する。
workflow全体の権限は`contents: read`だけで、untrusted PRのcodeをwrite token付きで実行しない。

ローカルで必要なplatform要件を満たす場合は次を使う。

```bash
node scripts/run-example-manifest.js --lane optional
```

## Evidence and retention

成功・失敗にかかわらず`.artifacts/manifest/<id>/`をuploadする。
各IDには`metadata.json`、`command.txt`、`stdout.log`、`stderr.log`があり、metadataはtool version、command、入力hash、実行制約、exit code、outcomeを記録する。
環境変数、host、secretは記録しない。
artifact retentionは14日、stdout/stderrは16 MiB、tool outputは64 MiBを1 entry当たりの上限とする。
`timeoutSeconds`とstdout/stderr上限はrunnerが強制し、retained tool outputは実行後に検査する。`memoryMiB`はjob容量計画用のdeclared budgetであり、OS/cgroup上限としては強制しない。したがって`resource-exhausted`は検出可能な出力超過を表し、OOM killの完全な分類は保証しない。

Ubuntu 24.04 x86-64向けの詳細なローカル前提は付録Bを参照する。
