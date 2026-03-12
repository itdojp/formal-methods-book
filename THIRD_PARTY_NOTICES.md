# Third-Party Notices

本ファイルは、first-party の既定ライセンス（`CC BY-NC-SA 4.0` / `Apache-2.0`）の対象外となる third-party / upstream / vendored assets を整理するための台帳です。

## 既定ライセンスの対象外

- `.book-formatter/**`
  - upstream ツール設定・補助資産として扱い、元の条件がある場合はその条件を維持します。
- `node_modules/**`
  - 依存パッケージのインストール成果物です。各パッケージは upstream の個別ライセンスに従います。
- vendored theme / font / asset subtree
  - 元ライセンス、付随する `LICENSE` / `NOTICE`、または配布元の条件を維持します。
- 個別の `LICENSE` / `NOTICE` / per-file header を持つファイル
  - その個別表記を優先します。

## 現時点の運用メモ

- `package-lock.json` は依存解決の記録であり、依存パッケージ自体のライセンス台帳ではありません。
- third-party 資産を新たに vendoring する場合は、このファイルにパス・出典・適用ライセンス・必要な notice を追記してください。
