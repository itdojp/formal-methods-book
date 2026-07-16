# Changelog

本書の reader-facing content、実行例、検証・公開基盤に対する主要な変更を記録します。
記載形式は [Keep a Changelog](https://keepachangelog.com/en/1.1.0/) を基準とします。

現在の書籍メタデータ上の版は `1.0.0` です。tag、GitHub Release、公開版、source commit を同期する次回 release は Issue #319 で確定します。本ファイルだけで未公開版を公開済みとは扱いません。

## [Unreleased]

### Changed

- TLA+、模型検査、論理、CAP、FLP の保証範囲と成立条件を精密化
- 「そのまま動く」例を、固定 tool version、command、期待結果、CI lane、標準 artifact を持つ 12 件の manifest contract へ移行
- JavaScript 依存の再現性を root `package-lock.json` と clean-checkout の `npm ci` に一元化
- Book QA で利用する外部 `book-formatter` を監査済み commit SHA pin として文書化
- edition config を章・付録・special page・part・locale UI metadata の正本とし、Jekyll config、navigation、mobile config、トップ目次を決定的に生成
- 日本語・英語の reader-facing Markdown を `src/<locale>/**` から決定的に生成し、`docs/**` の本文二重管理を解消
- 全英語 reader page の翻訳状態を commit/digest 付き manifest に移行し、公開ページへ status と監査日を生成

### Removed

- Git 管理されていた `node_modules/**` と Jekyll 生成物 `docs/_site/**`
- 本書で利用していない book-publishing-template の移行、引継ぎ、比較、preview、sample config、未実装 PDF/EPUB 手順
- 参照されていない重複 asset subtree と旧テンプレート用 screenshot / CSS / JavaScript

### Quality

- tracked 生成物、旧テンプレート残骸、formatter pin drift、存在しない npm script の案内を検出する repository hygiene gate を追加
- title / description / order / path、JA/EN 1:1 対応、生成物の完全一致を検証する publication metadata renderer test / CI gate を追加
- source と公開 Markdown の byte-for-byte 一致、直接編集、stale page、asset / example link 変換、cleanup safety を検証する publication build test / CI gate を追加
- `synced` ページの見出し順、コード、表、tool label、example path、外部参照と snapshot drift を検証し、partial/stale 一覧を JSON artifact にする bilingual QA を追加
