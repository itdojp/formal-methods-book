# 形式的手法の基礎と応用（formal-methods-book）

本リポジトリは、形式的手法（仕様記述・模型検査・定理証明）を体系的に学ぶための技術書のソースです。
Markdown で執筆し、日本語版を `docs/`、英語版を `docs/en/` に公開する bilingual repository として運用します。

## 構成

- `src/ja/`:
  - 日本語版の原稿。章構成と技術内容の source-of-truth
- `src/en/`:
  - 英語版の原稿。`src/ja/` と 1:1 対応する翻訳版
- `shared/`:
  - 言語非依存の共通資産。配置境界は `shared/README.md`
- `docs/`:
  - `src/ja/**` から生成する公開用の日本語版。reader-facing Markdown は直接編集しない
- `docs/en/`:
  - `src/en/**` から生成する公開用の英語版。reader-facing Markdown は直接編集しない
- `book-config.json`:
  - repository manifest。edition 構成と policy の入口
- `book-config.ja.json` / `book-config.en.json`:
  - edition ごとの title / description / order / URL / locale UI metadata の source-of-truth
- `translation-status.json`:
  - 全英語 reader page の source / translation commit、digest、`synced | partial | stale`、確認日、追跡 Issue の正本
- `publication-config.json`:
  - Jekyll / mobile の言語非依存 static policy
- `docs/_config.yml` / `docs/_data/{navigation,locales}.yml` / `mobile-config.*.json`:
  - edition config と publication config から生成する公開メタデータ。直接編集しない
- `BILINGUAL-WORKFLOW.md`:
  - source-of-truth / translation / release policy
- `package.json`:
  - スクリプト・開発ツール

## セットアップとビルド

- 依存（任意）: Node.js 20.18.1+（QA 依存の `cheerio` / `undici` が要求する最低バージョン）
- セットアップ: `npm ci`
- ビルド: `npm run build`
  - ビルドスクリプトは、最初に公開メタデータを生成し、その後 `src/ja/**` と `src/en/**` から両 edition の reader-facing Markdown を更新します。
  - bilingual build / deploy の運用基準は `BILINGUAL-WORKFLOW.md` を参照してください。
- 推奨チェック: `npm test`
  - メタデータ整合性、`markdownlint`、構造lint、リンクチェックをまとめて実行します。
- 依存関係監査: `npm audit`
- 個別実行:
  - メタデータ整合性: `npm run check:metadata`
  - 公開メタデータ生成: `npm run generate:metadata`
  - metadata renderer unit test: `npm run test:metadata-renderer`
  - source → publish renderer unit test: `npm run test:publication-build`
  - translation status / structural contract unit test: `npm run test:bilingual-integrity`
  - bilingual QA と JSON report: `npm run qa:bilingual`
  - status、見出し level / numbered ID 順序 inventory: `npm run qa:bilingual:inventory`
  - TLA+ 意味論・対象 source/publish 整合: `npm run check:tla-semantics`
  - 模型検査・論理・CAP/FLP の保証境界: `npm run check:guarantees`
  - 実行可能 example manifest: `npm run check:example-manifest`
  - example lane / workflow / reader文書同期: `npm run check:example-workflow`
  - strict tool label 登録: `npm run check:tool-blocks`
  - PR 向け実行例: `npm run examples:pr-quick`
  - Lint: `npm run lint`
  - 構造lint: `npm run lint-structure`
  - リンク: `npm run check-links`

```bash
npm ci
npm run build:all
git diff --exit-code -- docs mobile-config.ja.json mobile-config.en.json
npm run qa:bilingual
npm test
npm audit
```

本文は `src/<locale>/**` だけを編集し、`docs/**` の reader-facing Markdown は `npm run build:all` で再生成します。章・付録の title、description、order、path、part、special page、locale UI label を変更するときは、対象の `book-config.<locale>.json` だけを編集します。Jekyll / mobile の言語非依存設定は `publication-config.json` を編集します。生成対象の手編集や古い生成結果は byte-for-byte checker と CI の generated-artifact check が検出します。

英語版の公開ページには `translation-status.json` から status、監査対象の日本語 commit、確認日、追跡 Issue を生成します。`synced` は意味確認済みかつ機械構造契約一致、`partial` は監査済みの既知差分あり、`stale` は監査後の内容変更ありを表します。詳細な状態定義と checkpoint commit の更新手順は `BILINGUAL-WORKFLOW.md`、CI report は `.artifacts/translation-status/report.json` を参照してください。

## 依存関係と Book QA の管理

- root の JavaScript 依存関係の正本は `package.json` と `package-lock.json` です。`node_modules/` は `npm ci` が生成するローカル成果物であり、Git へ追加しません。
- CI、Pages、ローカル検証はいずれも tracked `node_modules/` に依存せず、clean checkout から `npm ci` で復元します。依存を変更した PR では lockfile の差分と `npm audit` の結果を確認します。
- Book QA は `.github/workflows/book-qa.yml` で外部リポジトリ `itdojp/book-formatter` の監査済み commit `69eb5c12f5a750b65614bc9bbbc3d7abd5aa6f6c` を固定 checkout します。mutable な `main` や major tag は使用しません。
- formatter pin を更新するときは、旧 SHA と候補 SHA の CLI、schema、warning/failure 条件、artifact、同期安全性、依存監査を比較し、代表的な書籍で pilot してから、このリポジトリでは formatter pin だけの PR として更新します。workflow の `ref` と本節の SHA は同じ commit に保ちます。

リポジトリ衛生契約は `npm run check:repository-hygiene` で検証します。tracked 生成依存物、Jekyll の `_site`、旧テンプレート文書、formatter pin の文書 drift、存在しない npm script の案内を検出します。

## 実行可能 example と CI

`examples/example-manifest.json` は、本文の strict tool label と自己完結した asset、固定ツール版、実行 command、期待 exit code/stdout marker、CI lane を結ぶ正本です。現在の inventory は Alloy 4件、TLC 1件、Apalache 1件、Dafny 1件、SPIN 2件、NuSMV 2件、CBMC 1件の計12件です。

個別契約または lane は manifest runner から実行します。

```bash
node scripts/run-example-manifest.js --id alloy-collection
node scripts/run-example-manifest.js --lane pr-quick
node scripts/run-example-manifest.js --lane nightly
```

- `pr-quick`: Alloy 6.2.0、TLC 1.7.4、Apalache 0.52.1、Dafny 4.11.0
- `nightly`: SPIN 6.5.2、NuSMV 2.7.1、CBMC 6.10.0
- 実行証跡: `.artifacts/manifest/<id>/metadata.json`、`command.txt`、`stdout.log`、`stderr.log`

runner は成否にかかわらず4ファイルを作成します。`metadata.json` は manifest 上の tool/version、command、期待値、実測 exit code、marker 判定を記録しますが、環境変数、ホスト、OS 等の実行環境情報は記録しません。

schedule / workflow dispatch では `pr-quick` 7件も実行し、`nightly-deep` job は既存の Alloy/TLC/Apalache/Dafny の深い探索条件を維持してから `nightly` 5件を実行します。

ローカルの `nightly` lane は Ubuntu 24.04 x86-64 または互換環境を対象とします。必要な apt package、hash 固定した Meson/Ninja の導入手順、他OSで GitHub Actions を使う境界は付録Bに記載しています。

PR quick は nightly tool を取得しません。nightly の NuSMV は、Ubuntu 24.04 で `libedit.so.0` を要求する公式バイナリを使用せず、公式 LGPL 2.7.1 source（SHA-256 `f1e11931f71d98aa9b84181eed67db584d7111100c2e967c904a31c15f823f60`）を `-Dwith-shell=disabled` で release build します。nightly workflow が GCC/G++、flex、bison、m4、patch、Python 3、pkg-config と、hash 固定した `tools/nusmv-build-requirements.txt` の Meson 1.7.2 / Ninja 1.11.1.4 を準備します。

nightly tool の取得元は次の値に固定しています。

| Tool | 固定対象 | SHA-256 |
|---|---|---|
| SPIN 6.5.2 | upstream commit `4883fbb1b1ef1f75fa9dda78efe1ad8910baf819` の tarball | `6f4963a4d6ca38f1af9ceaa76a815fbbd92e7ed7f2c424f1af88f67ec3f289f6` |
| NuSMV 2.7.1 | `https://nusmv.fbk.eu/distrib/2.7.1/NuSMV-2.7.1.tar.xz` | `f1e11931f71d98aa9b84181eed67db584d7111100c2e967c904a31c15f823f60` |
| CBMC 6.10.0 | official Ubuntu 24.04 x86-64 deb | `d716c219c5318a54f5298f9d5f66766d599e2e37bede33224437a8ad487fc504` |

## 執筆ルール（抜粋）

- 各章ファイルの先頭に見出し `# 第N章 ...` を置く
- 図表は SVG を推奨
- 1文1行を推奨（差分を読みやすくするため）

## バイリンガル運用

- 日本語版の正本管理、英語版の追従方針、release 条件は `BILINGUAL-WORKFLOW.md` を参照してください。
- 共通資産の配置可否は `shared/README.md` を参照してください。
- 翻訳や構造変更を行う前に `CONTRIBUTING.md` の bilingual workflow を確認してください。

## ライセンス

本リポジトリは、本文系コンテンツとコード資産で既定ライセンスを分離しています。

- 本文・図版・付録などの reader-facing コンテンツ: `CC BY-NC-SA 4.0`（`LICENSE`）
- コード例・ツール・ビルド・サイト実装などの再利用可能資産: `Apache-2.0`（`LICENSES/Apache-2.0.txt`）
- 適用範囲の詳細: `LICENSE-SCOPE.md`
- 商用利用窓口: `COMMERCIAL.md`
- 商標: `TRADEMARKS.md`
- third-party / upstream 資産: `THIRD_PARTY_NOTICES.md`
