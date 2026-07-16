# Examples

このディレクトリは、形式的手法の自己完結した実行例と、その機械可読な実行契約を管理します。

`tools/tool-manifest.json`がtool/serviceのlaneとversionの正本で、`example-manifest.json`が実行可能exampleの正本です。各example entryは`id`、`tool`、`chapter`（`chapterNN`または`appendix-ID`）、`anchor`、JA/EN source/publicの`references`、`assets`、任意の`config`、実tool `command`、`lane`、期待outcome、timeout/memory/seed/scope/depth/boundを持ちます。versionはexampleへ重複させません。

- `examples/alloy/`: Alloyの最小モデル
- `examples/ch04/`: 第4章（Alloy）の例題ファイル
- `examples/ch08/`: 第8章（SPIN / NuSMV / CBMC）の自己完結した最小例
- `examples/tla/`: TLA+の最小モデル
- `examples/apalache/`: Apalache の最小モデル
- `examples/dafny/`: Dafny の最小検証例
- `examples/quint/`: Quintのtypecheck/test例
- `examples/prism/`: PRISMの確率的・定量的模型検査例と期待値契約
- `examples/tamarin/`: Tamarinの欠陥/修正protocol model、期待lemma、attack trace契約
- `examples/proof-certificates/`: cvc5が生成する自己完結QF_UF Alethe UNSAT証明書をCarcaraで独立再検査する例
- `examples/kani/`: manual dispatch用Kani proof harness
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
node scripts/run-example-manifest.js --lane optional
```

`pr-quick`はAlloy/TLC/Apalache/Dafnyの7件、`nightly`はSPIN/NuSMV/CBMC/Quint/PRISM/Tamarin/SymbiYosys/cvc5の13件、`optional`はKani 1件です。Alloy/TLC/Apalache/Dafnyの代表entryにはnightly deep profileもあります。cvc5例は固定cvc5 1.3.4がAletheを出力し、固定sourceからRust 1.87.0で毎回再buildするCarcara 1.1.0が再検査します。certificateは1 MiB、checker outputは64 KiBで制限し、tool outputには`certificate.alethe`、`results.json`、`summary.log`だけを保持します。各実行の証跡は常に`.artifacts/manifest/<id>/`に保存されます。

source manuscript の asset link は同じ Git revision 内の相対 path を指します。公開 `docs/**` では Jekyll の `site.github.build_revision` を使い、Pages を生成した commit の asset へ固定します。
