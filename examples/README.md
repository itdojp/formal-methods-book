# Examples

このディレクトリは、形式的手法の自己完結した実行例と、その機械可読な実行契約を管理します。

`example-manifest.json` が唯一の inventory です。各 entry は `id`、`tool`、`version`、`chapter`（`chapterNN` または `appendix-ID`）、`anchor`、JA/EN source/public の `references`、`assets`、任意の `config`、実ツール `command`、`lane`、期待 exit code/stdout marker を持ちます。

- `examples/alloy/`: Alloyの最小モデル
- `examples/ch04/`: 第4章（Alloy）の例題ファイル
- `examples/ch08/`: 第8章（SPIN / NuSMV / CBMC）の自己完結した最小例
- `examples/tla/`: TLA+の最小モデル
- `examples/apalache/`: Apalache の最小モデル
- `examples/dafny/`: Dafny の最小検証例
- `examples/ci/`: PR向けの軽量チェック例

## 使い方（概要）

```bash
# manifest と本文参照契約の検証
node scripts/check-tool-example-links.js --self-test
node scripts/check-tool-example-links.js

# 個別 example / lane の実行
node scripts/run-example-manifest.js --id tlc-queue-bounded
bash examples/ci/pr-quick-check.sh
node scripts/run-example-manifest.js --lane nightly
```

`pr-quick` は Alloy/TLC/Apalache/Dafny の7件、`nightly` は SPIN/NuSMV/CBMC の5件です。各実行の証跡は常に `.artifacts/manifest/<id>/` に保存されます。

source manuscript の asset link は同じ Git revision 内の相対 path を指します。公開 `docs/**` では Jekyll の `site.github.build_revision` を使い、Pages を生成した commit の asset へ固定します。
