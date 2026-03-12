# ライセンス適用範囲

本リポジトリは、reader-facing な本文系コンテンツと、再利用可能なコード／ビルド資産を分離して管理します。

- root `LICENSE`: `CC BY-NC-SA 4.0` の正規文面
- `LICENSES/Apache-2.0.txt`: コード／ビルド資産に適用する `Apache-2.0` の正規文面
- `COMMERCIAL.md`: 本文系コンテンツの商用利用窓口
- `TRADEMARKS.md`: 商標・ロゴ等の扱い
- `THIRD_PARTY_NOTICES.md`: third-party / upstream 資産の扱い

## 基本原則

- 各ファイルに個別の `LICENSE` / `NOTICE` / per-file header がある場合は、その個別表記を優先します。
- 商標・ロゴ・製品名は、CC / Apache の既定ライセンス対象に含めません。詳細は `TRADEMARKS.md` を参照してください。
- third-party / upstream / vendored assets は、first-party の既定ライセンス対象に含めません。詳細は `THIRD_PARTY_NOTICES.md` を参照してください。
- 新規ファイルは、既存の同種ディレクトリと同じ原則で扱います。

## CC BY-NC-SA 4.0 の適用範囲

以下の reader-facing コンテンツは、別注記がない限り `CC BY-NC-SA 4.0` とします。

- `docs/afterword/**`
- `docs/appendices/**`
- `docs/chapters/**`
- `docs/glossary/**`
- `docs/introduction/**`
- `docs/index.md`
- `src/**`
- `manuscript/**`
- `glossary-terms.md`
- `glossary.json`
- `book-config.json`
- `book-config.sample.json`
- `mobile-config.json`
- `docs/assets/figures/**`
- `docs/assets/images/**`
- `docs/assets/diagrams/**`

## Apache-2.0 の適用範囲

以下のコード／ビルド／運用資産は、別注記がない限り `Apache-2.0` とします。

- `.devcontainer/**`
- `.github/**`
- `docs/_includes/**`
- `docs/_layouts/**`
- `docs/assets/css/**`
- `docs/assets/js/**`
- `formal-methods-book/docs/assets/**`
- `examples/**`
- `project-management/**`
- `scripts/**`
- `templates/**`
- `tools/**`
- `.markdownlint.json`
- `CHANGELOG.md`
- `CLAUDE.md`
- `COMPARISON.md`
- `CONTRIBUTING.md`
- `DESIGN-PREVIEW.md`
- `DIAGRAM_ENHANCEMENT_REPORT.md`
- `EPUB-PDF-GUIDE.md`
- `FEEDBACK-COLLECTION.md`
- `HANDOVER-SUMMARY.md`
- `HANDOVER.md`
- `INTEGRATION_CHECKLIST.md`
- `MIGRATION-PLAN.md`
- `NEW-FEATURES.md`
- `QUALITY_REPORT.md`
- `README.md`
- `book-formatter-config.json`
- `book-template-guide.md`
- `cspell.json`
- `design-preview.html`
- `it_book_proofreading_prompt.md`
- `jest.e2e.config.js`
- `package-lock.json`
- `package.json`

## `docs/_data/**` の監査結果

`docs/_data/**` は file-by-file で確認しました。

- `docs/_data/navigation.yml`: 章タイトル・付録タイトル・見出しなど reader-facing なラベルを含むため、`CC BY-NC-SA 4.0`

今後 `docs/_data/**` に新規ファイルを追加する場合は、reader-facing なラベル・説明を主とするものは `CC BY-NC-SA 4.0`、サイト生成のための純粋なメタデータは `Apache-2.0` とします。

## 埋め込みコードの carve-out

以下の CC 側ファイルに含まれる executable code snippets, shell commands, formal-spec fragments, machine-readable examples は、別注記がない限り `Apache-2.0` とします。

- `docs/**`
- `src/**`
- `manuscript/**`

## 除外対象

以下は first-party の既定ライセンス対象に含めません。

- `.book-formatter/**`
- `node_modules/**`
- vendored theme / font / asset subtree
- 個別の `LICENSE` / `NOTICE` / per-file header を持つもの

## 商用利用

reader-facing な本文系コンテンツの商用利用窓口は `COMMERCIAL.md` を参照してください。
