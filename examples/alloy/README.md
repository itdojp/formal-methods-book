# Alloy example

最小構成のAlloyモデル例です（Alloy 6.x想定）。

## 実行（CLI）

```bash
bash tools/bootstrap.sh
bash tools/alloy-check.sh --verbose examples/alloy/collection.als
```

状態遷移（Alloy 6 の `var` + temporal）例：

```bash
bash tools/alloy-check.sh --verbose examples/alloy/trash-temporal.als
```
