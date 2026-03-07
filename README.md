# 形式的手法の基礎と応用（formal-methods-book）

本リポジトリは、形式的手法（仕様記述・模型検査・定理証明）を体系的に学ぶための技術書のソースです。Markdown で執筆し、`docs/` に静的ファイルを配置します。

## 構成

- `src/`:
  - `introduction/`, `chapters/`, `appendices/`, `afterword/` の原稿
- `docs/`:
  - 公開用の生成物（GitHub Pages で公開想定）
- `book-config.json`: 目次メタデータ
- `package.json`: スクリプト・開発ツール

## セットアップとビルド

- 依存（任意）: Node.js 20+
- ビルド: `npm run build`
  - `src/appendices/*` を `docs/appendices/<id>/index.md` にコピーします。
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

## ライセンス

本作品は `CC-BY-NC-SA-4.0` で提供します。法的全文は `LICENSE`、運用上の補足と商用利用に関する窓口は `LICENSE.md` を参照してください。
