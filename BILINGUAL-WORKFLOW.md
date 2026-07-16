# Bilingual Workflow

本書は、日本語版を基準に英語版を追従させる bilingual repository として運用します。
本書の repository architecture と editorial workflow の基準文書は本ファイルです。

## Repository Architecture

| Path | 役割 | 原則 |
| --- | --- | --- |
| `src/ja/**` | 日本語版の原稿 | 本文構造と技術内容の source-of-truth |
| `src/en/**` | 英語版の原稿 | `src/ja/**` と 1:1 対応する翻訳原稿 |
| `docs/**` | 日本語版の公開物 | `src/ja/**` から生成し、`main` から公開する既定版 |
| `docs/en/**` | 英語版の公開物 | `src/en/**` から生成する公開物 |
| `shared/**` | 共通資産 | 言語非依存の再利用資産だけを配置 |
| `book-config.json` | repository manifest | edition 構成と policy の入口 |
| `book-config.ja.json` | 日本語版メタデータ | 章構成・説明・ UX 設定の日本語版定義 |
| `book-config.en.json` | 英語版メタデータ | 英語版定義。`book-config.ja.json` と構造整合を保つ |
| `publication-config.json` | 公開 static policy | Jekyll / mobile の言語非依存設定 |
| `docs/_config.yml` / `docs/_data/*.yml` | Jekyll metadata | edition / publication config から生成し、直接編集しない |
| `mobile-config.ja.json` | 日本語版 mobile 設定 | edition / publication config から生成する `docs/` 向け設定 |
| `mobile-config.en.json` | 英語版 mobile 設定 | edition / publication config から生成する `docs/en/` 向け設定 |
| `docs/_includes/generated/**` | 公開トップ目次 | edition config から生成し、`src/*/index.md` から include する |

## Source of Truth

- 章順、付録順、見出し粒度、節の分割、技術的主張の正誤は `src/ja/**` を正本とします。
- 構造変更は、日本語版を先に更新し、その後に英語版を追従させます。
- 英語版で先に見つかった誤りでも、恒久修正は日本語版に反映してから英語版へ戻します。
- `shared/**` に置いた資産だけは locale-neutral な canonical source として扱います。
- `book-config.json` は manifest であり、本文メタデータの正本ではありません。edition ごとの本文メタデータは `book-config.ja.json` / `book-config.en.json` に置きます。
- title、description、order、path、part、special page、locale UI label は edition config を正本とし、`npm run build:all` で navigation、Jekyll metadata、mobile config、トップ目次へ反映します。
- Jekyll / mobile の言語非依存 static policy は `publication-config.json` を正本とします。生成済み YAML / JSON / include は手編集しません。
- `docs/**` と `docs/en/**` の reader-facing Markdown はすべて生成物です。本文は `src/<locale>/**` だけを編集し、`npm run build:<locale>` または `npm run build:all` で公開物へ反映します。
- builder は front matter、source path、locale、公開用 asset link、同一 revision の example link を決定的に付与・変換します。公開物だけの変更は正本へ逆流させません。

## Translation Policy

- 英語版は「日本語版を翻訳した別 edition」として扱い、章 ID・付録 ID・対応 URL を維持します。
- 翻訳 PR では、意味の等価性を優先し、説明順や章構造を独自に変更しません。
- コード、数式、記号、ツール入力は、言語を越えて同一である方が妥当な場合は翻訳しません。
- 言語依存の文言を含む例、図、スクリーンショットは `shared/` に置かず、各 edition 側で管理します。
- 日本語版に未反映の内容を英語版へ独自追加する場合は、事前に issue で source-of-truth の扱いを合意してください。

## Release Policy

- release branch / Pages publish の基準は `main` とします。
- 公開対象は日本語版 `docs/` と英語版 `docs/en/` の組です。
- 章構成やナビゲーションに影響する変更は、`book-config.json`、edition config、公開先パスの整合が取れてから release 対象にします。
- 英語版が追従中で同期遅延を許容する場合は、対応 issue を open にし、PR または release note で明示します。
- `shared/` の追加・削除は両 edition に影響し得るため、片方だけの都合で破壊的変更を入れません。

## Pull Request Checklist

- 変更対象が `ja` / `en` / `shared` のどこに属するかを明示した
- 構造変更なら `src/ja/**` と対応する `src/en/**` の差分方針を説明した
- 新しい共通資産を追加した場合は `shared/README.md` の境界に適合することを確認した
- manifest / config / workflow 文書への影響を確認した
- `npm run build:all` と `npm run check:metadata` を実行し、`git diff --exit-code -- docs mobile-config.ja.json mobile-config.en.json` で未生成・手編集・古い生成物がないことを確認した
