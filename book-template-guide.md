# 完全ガイド

このドキュメントは、Book Publishing Template v2.0を使用するための完全なガイドです。

## 目次

1. テンプレートの特徴
2. リポジトリ管理
3. デプロイ手順
4. テンプレート構造
5. チェックリスト

## 1. テンプレートの特徴

- **単一リポジトリシステム**: 1つのリポジトリで執筆から公開まで完結。
- **簡単セットアップ**: 1コマンドで初期設定完了。
- **高速ビルド**: 軽量な依存関係で高速にビルド。
- **プライベートコンテンツ保護**: ドラフトやプライベートコメントを自動フィルタリング。
- **GitHub Pages統合**: トークン不要で簡単に公開。

## 2. リポジトリ管理

### プロジェクト情報

| 項目 | 値の例 |
|------|--------|
| GitHubのユーザー名または組織名 | `yourusername` |
| 連絡先メールアドレス | `knowledge@itdo.jp` |
| 組織名 | `ITDO Inc.` |

### リポジトリ構成

- **単一リポジトリ**: 執筆・編集・公開を1つのリポジトリで管理。
- **ビルド出力**: /docs フォルダにHTMLを出力し、GitHub Pagesで公開。

## 3. デプロイ手順

### 初期セットアップ

1. テンプレートをクローン。
2. `node easy-setup.js` を実行。
3. GitHub Pagesを有効化（Settings > Pages > main/docs）。

### デプロイ方法

```bash
# ビルド
npm run build

# コミット＆プッシュ
git add .
git commit -m "Update content"
git push origin main
```

on:
  push:
    branches:
      - main

jobs:
  deploy:
    runs-on: ubuntu-latest

    steps:
      - name: Checkout code
        uses: actions/checkout@v3

      - name: Setup Node.js
        uses: actions/setup-node@v3
        with:
          node-version: '16'

      - name: Install dependencies
        run: npm install

      - name: Build project
        run: npm run build

      - name: Deploy to GitHub Pages
        env:
          GITHUB_TOKEN: ${{ secrets.DEPLOY_TOKEN }}
        run: |
          git config --global user.name "github-actions"
          git config --global user.email "github-actions@github.com"
          git add .
          git commit -m "Deploy to GitHub Pages"
          git push origin gh-pages
```

## 4. テンプレート構造

以下はテンプレートの基本構造です：

```plaintext
your-book-private/
├── package.json
├── _config.yml
├── .gitignore
├── README.md
├── index.md
├── _layouts/
│   └── default.html
├── assets/
│   └── images/
│       └── favicon.png
├── scripts/
│   ├── build.js
│   ├── build-incremental.js
│   ├── deploy.sh
│   └── init-template.js
├── src/
│   └── chapters/
│       └── chapter01/
│           └── index.md
├── .github/
│   └── workflows/
│       └── deploy.yml
└── template-config.json
```

## 5. チェックリスト

### 事前準備

- [ ] GitHubアカウントの準備
- [ ] ローカル開発環境の準備（Node.js, Git）
- [ ] 元プロジェクトファイルへのアクセス

### ファイル作成

- [ ] ディレクトリ構造の作成
- [ ] 必要なスクリプトと設定ファイルのコピー
- [ ] LICENSEファイルの設定

### GitHub Actions

- [ ] `.github/workflows/deploy.yml` の設定

これでテンプレートの全体像を把握できます。
