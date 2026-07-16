# SymbiYosys RTL arbiter contract

2 要求の同期 arbiter を対象に、`smtbmc bitwuzla` と depth 6 を固定する。

- `arbiter-flawed.sv` / `arbiter-flawed.sby`: 初期サイクルだけ reset を asserted とし、その後は deasserted を仮定する。要求は非制約であり、同時 grant の禁止は step 3 の反例/VCD で `FAIL` になる。
- `arbiter-fixed.sv` / `arbiter-fixed.sby prove`: 同じ mutual exclusion を base case と induction の両方で `PASS` にする。
- `arbiter-fixed.sv` / `arbiter-fixed.sby cover`: 前の要求サンプルで `req0=req1=1` のとき `req0` 優先の `grant0=1, grant1=0` に到達する VCD を `PASS` で残す。

`tools/sby-check.sh` は checksummed OSS CAD Suite を再展開し、正規化された `results.json`、`summary.log`、必要な VCD だけを artifact に残す。suite archive と binary は artifact に含めない。
