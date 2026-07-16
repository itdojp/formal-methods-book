# リリース手順

## 基本方針

- release 基準ブランチは `main` です。release branch は作りません。
- 公開対象は GitHub Pages の `docs/` と `docs/en/` です。
- GitHub Release は配布バイナリ置き場ではなく、release note と exact commit を固定する監査点として扱います。
- PDF / EPUB の release artifact は作成しません。このリポジトリには対応 pipeline がありません。
- tag 形式は `vMAJOR.MINOR.PATCH` とし、書籍 version と 1 対 1 に対応させます。

## 書籍 version policy

### MAJOR

次のいずれかを含む場合に上げます。

- 章構成、対象読者、教育方針の大幅な変更
- 公開 URL / permalink / edition 構造の破壊的変更
- reader-facing の metadata schema や provenance 表示の非互換変更
- 既存の release note や運用手順では追従できない公開契約変更

### MINOR

次のいずれかを含む場合に上げます。

- 新しい章・付録・事例・検索・公開導線など、reader-facing の実質的追加
- 新しい executable lane、manifest 契約、または再現性運用の拡張
- 既存章の意味内容を補強する大きな正誤修正

### PATCH

次のすべてを満たす場合に上げます。

- 章や付録の適用範囲を広げない
- 公開契約の破壊的変更を含まない
- 誤字、軽微な記述修正、release 文書、provenance、運用手順の修正に留まる

## version 一致条件

release 直前に、少なくとも次が同一 version であることを確認します。

- `book-config.json` の `project.version`
- `book-config.ja.json` の `version`
- `book-config.en.json` の `version`
- `package.json` の `version`
- `package-lock.json` の `version`
- `docs/_config.yml` の `version`
- `CHANGELOG.md` の対象 release 見出し
- `RELEASE_NOTES/vX.Y.Z.md` の対象 version

## clean preflight

作業ツリーが clean な `main` で、次を順に実行します。

```bash
git fetch origin --tags
git switch main
git pull --ff-only origin main
git status --short
npm ci
npm run build:all
node scripts/generate-build-provenance.js
node scripts/check-build-provenance.js
npm run qa:bilingual
npm run check:metadata
npm test
git diff --check
git diff --exit-code -- docs mobile-config.ja.json mobile-config.en.json
```

判定基準:

- `git status --short` は空であること。
- `npm test`、`npm run qa:bilingual`、`npm run check:metadata` が成功すること。
- `docs/**`、mobile config に未反映差分がなく、`node scripts/check-build-provenance.js` が一時 provenance data を検証できること。
- release note に書く翻訳件数、lane、version、既知の制約が、生成物と一致すること。

## merge から tag までの exact-commit 手順

### 1. release 対象 PR を `main` に merge する

- required check が green の PR だけを merge します。
- 章構成、translation status、search index、provenance を触る PR は、必ず `main` 上の実 run で再確認します。

### 2. release commit を固定する

```bash
git fetch origin --tags
RELEASE_SHA="$(git rev-parse origin/main)"
git show --no-patch --format='%H %s' "$RELEASE_SHA"
test -z "$(git status --porcelain)"
```

- `RELEASE_SHA` は GitHub Release と tag の唯一の対象 commit です。
- 以後、`main` が先に進んでも、対象 tag を別 commit へ動かしません。

### 3. 既存 tag の衝突を確認する

```bash
git rev-parse -q --verify "refs/tags/v${VERSION}" >/dev/null && echo "tag already exists" && exit 1 || true
gh release view "v${VERSION}" >/dev/null 2>&1 && echo "release already exists" && exit 1 || true
```

- 既存 tag または既存 release がある場合は、上書きせず原因を先に解消します。

### 4. annotated tag を exact commit に打つ

```bash
git tag -a "v${VERSION}" "$RELEASE_SHA" -m "formal-methods-book v${VERSION}"
git push origin "refs/tags/v${VERSION}"
git rev-parse "v${VERSION}^{commit}"
```

- `git rev-parse "v${VERSION}^{commit}"` の値が `RELEASE_SHA` と一致しなければ中止します。
- `gh release create --target main` のような自動 tag 作成は使いません。既存 tag を `--verify-tag` で使います。

### 5. GitHub Release を既存 tag から作成する

```bash
gh release create "v${VERSION}" \
  --verify-tag \
  --title "formal-methods-book v${VERSION}" \
  --notes-file "RELEASE_NOTES/v${VERSION}.md"
```

- release body の正本は `RELEASE_NOTES/vX.Y.Z.md` です。
- Pages 公開物が reader-facing artifact です。release 後に exact source commit と Pages run を結ぶ provenance JSON だけを監査用 asset として添付します。

### 6. release と tag の整合を確認する

```bash
gh release view "v${VERSION}" --json tagName,isDraft,isPrerelease,url
```

確認項目:

- `tagName` が `vX.Y.Z`
- draft ではない
- prerelease ではない
- release URL が生成されている
- local の `git rev-parse "vX.Y.Z^{commit}"` が `RELEASE_SHA` と一致する

## provenance JSON と Pages の検証

### 1. Pages run を exact commit で特定する

```bash
PAGES_RUN_ID="$(gh run list \
  --workflow Pages \
  --branch main \
  --commit "$RELEASE_SHA" \
  --json databaseId,headSha,conclusion \
  --jq 'map(select(.headSha == '"'"$RELEASE_SHA"'"' and .conclusion == "success")) | first.databaseId')"

test -n "$PAGES_RUN_ID"
gh run view "$PAGES_RUN_ID" --json headSha,conclusion,url,workflowName
```

- `headSha` が `RELEASE_SHA`
- `conclusion` が `success`
- `workflowName` が `Pages`

### 2. 公開 provenance JSON を確認する

```bash
curl -fsSL "https://itdojp.github.io/formal-methods-book/build-provenance.json" | jq .
```

確認項目:

- `version` が対象 version
- `release_tag` が `vX.Y.Z`
- `source_commit` が `RELEASE_SHA`
- `pages_run_id` が `PAGES_RUN_ID`
- `release_url` と `pages_run_url` が canonical URL

### 3. 公開 HTML の meta / data 属性を確認する

```bash
curl -fsSL "https://itdojp.github.io/formal-methods-book/" \
  | rg 'book-version|book-source-commit|book-generated-at|book-release|book-pages-run|data-book-version|data-source-commit'

curl -fsSL "https://itdojp.github.io/formal-methods-book/en/" \
  | rg 'book-version|book-source-commit|translation status|data-book-version|data-source-commit'
```

- 日本語トップと英語トップの両方で version / source commit 表示が取れること。
- 英語トップでは translation notice と source commit が見えること。

### 4. translation status artifact を確認する

```bash
BOOK_QA_RUN_ID="$(gh run list \
  --workflow 'Book QA (Unicode + Links + Textlint + Layout Risk + Markdown + Jekyll)' \
  --branch main \
  --commit "$RELEASE_SHA" \
  --json databaseId,headSha,conclusion \
  --jq 'map(select(.headSha == '"'"$RELEASE_SHA"'"' and .conclusion == "success")) | first.databaseId')"

mkdir -p .codex-local/tmp/release-audit/translation-status
gh run download "$BOOK_QA_RUN_ID" \
  -n translation-status-report \
  -D .codex-local/tmp/release-audit/translation-status

jq . .codex-local/tmp/release-audit/translation-status/report.json
```

- release note に記載する `partial` / `synced` / `stale` 件数と一致すること。
- `partial` / `stale` を公開する場合は、release note 側にも明示すること。

### 5. Release へ provenance asset を固定する

```bash
PROVENANCE_ASSET=".codex-local/tmp/release-audit/formal-methods-book-v${VERSION}-provenance.json"
mkdir -p "$(dirname "$PROVENANCE_ASSET")"

jq -n \
  --arg version "$VERSION" \
  --arg release_tag "v${VERSION}" \
  --arg source_commit "$RELEASE_SHA" \
  --arg pages_run_id "$PAGES_RUN_ID" \
  --arg pages_run_url "https://github.com/itdojp/formal-methods-book/actions/runs/${PAGES_RUN_ID}" \
  --arg public_provenance_url "https://itdojp.github.io/formal-methods-book/build-provenance.json" \
  '{schema_version:"1.0", version:$version, release_tag:$release_tag, source_commit:$source_commit, pages_run_id:$pages_run_id, pages_run_url:$pages_run_url, public_provenance_url:$public_provenance_url}' \
  > "$PROVENANCE_ASSET"

gh release upload "v${VERSION}" "$PROVENANCE_ASSET" --clobber
gh release view "v${VERSION}" --json assets --jq '.assets[].name'
```

- asset の `source_commit` と `pages_run_id` を公開 `build-provenance.json` と照合します。
- asset は公開 Pages artifact と GitHub Release を結ぶ監査記録です。認証情報、環境変数、Private 情報を含めません。

## safe rollback

### 原則

- 公開済み tag を動かしません。
- 公開済み release を「消してなかったことにする」より、訂正用 patch release を出すことを優先します。
- Pages 事故は tag を動かさず、`main` を revert して復旧します。

### 誤りが未公開の tag / release に限られる場合

条件:

- release が draft のまま、または公開前に誤りへ気づいた
- 外部告知、参照、運用利用がまだない

手順:

```bash
gh release delete "v${VERSION}" --yes
git push origin ":refs/tags/v${VERSION}"
git tag -d "v${VERSION}"
```

その後、正しい commit で tag と release を作り直します。

### 公開済み release note だけが誤っている場合

- tag と commit が正しいなら、release body を修正します。
- version は変えません。
- CHANGELOG と `RELEASE_NOTES/vX.Y.Z.md` を正として同期します。

### 公開済み tag / commit 自体が誤っている場合

- 既存 tag を動かしません。
- 誤りの内容を記録したうえで、必要なら `vX.Y.(Z+1)` の patch release を作成します。
- 旧 release には superseded であることを追記して残します。

### Pages 公開物が壊れた場合

- まず `main` を revert して Pages を復旧します。
- 例:

```bash
git switch main
git pull --ff-only origin main
git revert <bad-commit-sha>
git push origin main
```

- Pages 復旧後、正しい修正を別 PR で入れ、必要なら patch release を切ります。
- 既存の公開済み tag は触りません。

## release 完了条件

- `CHANGELOG.md`、`RELEASE_NOTES/vX.Y.Z.md`、GitHub Release 本文が一致している
- `gh release view vX.Y.Z` で release URL が確認できる
- `build-provenance.json` の `source_commit` が `RELEASE_SHA` を指す
- GitHub Release の provenance asset が公開 `build-provenance.json` と同じ commit / Pages run を指す
- 公開 HTML の version / source commit 表示が確認できる
- translation status artifact の件数が release note と一致する
- PDF / EPUB が「存在しないこと」を release note に明記している
