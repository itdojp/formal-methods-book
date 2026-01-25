# TLA+ example

最小構成のTLA+仕様例です。`QueueBounded.tla` は有限状態になるように作ってあり、TLC/Apalacheで再現できます。

## 実行（TLC）

```bash
bash tools/bootstrap.sh
bash tools/tlc-run.sh --config examples/tla/QueueBounded.cfg examples/tla/QueueBounded.tla
```
