# CI examples

## PR向け（軽量チェック）

```bash
bash examples/ci/pr-quick-check.sh
```

このスクリプトは `examples/example-manifest.json` の `pr-quick` lane をそのまま実行します。SPIN、NuSMV、CBMC の取得・ビルドは行いません。

## 夜間・手動実行

```bash
node scripts/run-example-manifest.js --lane nightly
```

`.github/workflows/formal-checks.yml` の schedule / workflow_dispatch は、`nightly-deep` job で既存の Alloy/TLC/Apalache/Dafny の deep 条件を維持したうえで `nightly` lane を実行します。Ubuntu 24.04 上で source build する SPIN/NuSMV のため、この job だけが build-essential、flex、bison、m4、patch、Python 3、Meson、Ninja、pkg-config を導入します。

ローカル実行は Ubuntu 24.04 x86-64 または互換環境に限定します。apt package と hash 固定した Python build tool の準備手順は付録Bを参照してください。他OSでは `workflow_dispatch` を利用します。

成功・失敗にかかわらず `.artifacts/manifest/<id>/` を artifact として upload します。各 ID には `metadata.json`、`command.txt`、`stdout.log`、`stderr.log` があり、metadata は実行環境を記録しません。
