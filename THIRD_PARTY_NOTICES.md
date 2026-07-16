# Third-Party Notices

本ファイルは、first-party の既定ライセンス（`CC BY-NC-SA 4.0` / `Apache-2.0`）の対象外となる third-party / upstream / vendored assets を整理するための台帳です。

## 既定ライセンスの対象外

- `.book-formatter/**`
  - upstream ツール設定・補助資産として扱い、元の条件がある場合はその条件を維持します。
- `node_modules/**`
  - `npm ci` がローカルまたは CI で生成する非追跡のインストール成果物です。各パッケージは upstream の個別ライセンスに従います。
- vendored theme / font / asset subtree
  - 元ライセンス、付随する `LICENSE` / `NOTICE`、または配布元の条件を維持します。
- 個別の `LICENSE` / `NOTICE` / per-file header を持つファイル
  - その個別表記を優先します。

## 現時点の運用メモ

- `package-lock.json` は依存解決の記録であり、依存パッケージ自体のライセンス台帳ではありません。
- `node_modules/**` は vendoring せず、Git 管理しません。再現性は root `package-lock.json` と `npm ci` で保証します。
- third-party 資産を新たに vendoring する場合は、このファイルにパス・出典・適用ライセンス・必要な notice を追記してください。

## Nightlyで取得・buildするRTLola

- `rtlola-cli 0.1.2`
  - 出典：<https://github.com/reactive-systems/RTLola-Interpreter/tree/11b6bb080a5fa487645fb023fb3d0baea6874e73/crates/rtlola-cli>
  - license：Apache-2.0
  - `tools/bootstrap.sh`が固定SHA-256のcrates.io source packageを取得し、固定Rust toolchainと埋め込み`Cargo.lock`でbuildします。
  - source package、依存crate、生成binaryはGit、Pages、CI artifactへ再配布しません。各依存crateは自身のlicenseに従います。
