# Examples

このディレクトリは、形式的手法をCIに組み込むための最小構成テンプレートです。
実運用ではツール導入や検証パラメータの調整が必要です。

- `examples/alloy/`: Alloyの最小モデル
- `examples/ch04/`: 第4章（Alloy）の例題ファイル
- `examples/tla/`: TLA+の最小モデル
- `examples/ci/`: PR向けの軽量チェック例

## 使い方（概要）

PR向けの最小チェックは `examples/ci/pr-quick-check.sh` を参照してください。
夜間の深い探索は `examples/ci/README.md` の例をベースに拡張します。
