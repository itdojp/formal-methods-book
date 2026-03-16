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
  - 公開用の日本語版
- `docs/en/`:
  - 公開用の英語版
- `book-config.json`:
  - repository manifest。edition 構成と policy の入口
- `book-config.ja.json` / `book-config.en.json`:
  - edition ごとの目次メタデータ
- `BILINGUAL-WORKFLOW.md`:
  - source-of-truth / translation / release policy
- `package.json`:
  - スクリプト・開発ツール

## セットアップとビルド

- 依存（任意）: Node.js 20+
- ビルド: `npm run build`
  - 現行のビルドスクリプトは repository 管理下の公開物を更新します。
  - bilingual build / deploy の運用基準は `BILINGUAL-WORKFLOW.md` を参照してください。
  - 章（`docs/chapters/*`）は Jekyll フロントマターを含むため本ビルダーでは変更しません。
- 推奨チェック: `npm test`
  - `markdownlint`、構造lint、リンクチェックをまとめて実行します。
- 個別実行:
  - Lint: `npm run lint`
  - 構造lint: `npm run lint-structure`
  - リンク: `npm run check-links`

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
