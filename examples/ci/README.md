# CI examples

## PR向け（軽量チェック）

```bash
bash examples/ci/pr-quick-check.sh
```

## 夜間向け（深い探索）の例

実運用では、夜間に探索深度を上げるジョブを追加します。
以下は概念例です（実際にはツール導入が必要です）。

```yaml
name: formal-checks
on:
  schedule:
    - cron: "0 2 * * *"

jobs:
  nightly-deep:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - name: Deep Alloy/TLC checks (example)
        run: |
          ./tools/alloy-check.sh --scope large --timeout 1800
          ./tools/tlc-run.sh specs/Queue.tla --depth 10000 --time-limit 1800
```
