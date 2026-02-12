# PDF/ePub生成機能ガイド

## 概要

> ⚠️ **注意**: PDF/EPUB生成機能は v2.0 では未実装です。これらの機能は今後のアップデートで追加予定です。現在はHTMLでの公開のみサポートしています。

書籍テンプレートでのPDF及びePub形式での書籍生成機能について説明します。

## 機能一覧

- ✅ **PDF生成**: 印刷用の高品質HTMLファイル生成
- ✅ **ePub生成**: 電子書籍リーダー対応版
- ✅ **自動目次生成**: 全セクションの見出しから目次を自動作成
- ✅ **印刷用スタイルシート**: PDF用の専用CSS
- ✅ **ePub用スタイルシート**: 電子書籍用の専用CSS
- ✅ **メタデータ設定**: 著者、出版日等の書籍情報
- ✅ **設定ファイル対応**: book-config.json での細かな制御

## クイックスタート

### 1. 全ての形式を一度に生成

```bash
npm run generate:all
```

このコマンドで HTML、PDF、ePub の全ての形式が生成されます。

### 2. 個別生成

```bash
# PDF用HTMLファイルのみ生成
npm run generate:pdf

# ePubファイルのみ生成
npm run generate:epub
```

## 設定

### book-config.json での設定例

```json
{
  "output": {
    "pdf": {
      "enabled": true,
      "filename": "book.pdf",
      "pageSize": "A4",
      "margins": {
        "top": "20mm",
        "bottom": "20mm", 
        "left": "20mm",
        "right": "20mm"
      },
      "fontSize": "10pt",
      "printBackground": true,
      "displayHeaderFooter": true,
      "headerTemplate": "<div style='font-size:9px; width:100%; text-align:center;'><span class='title'></span></div>",
      "footerTemplate": "<div style='font-size:9px; width:100%; text-align:center;'><span class='pageNumber'></span> / <span class='totalPages'></span></div>"
    },
    "epub": {
      "enabled": true,
      "filename": "book.epub",
      "version": "3.0",
      "title": "Your Book Title",
      "author": "Your Name",
      "publisher": "Your Publisher",
      "description": "Your book description",
      "cover": "assets/images/cover.jpg",
      "css": "assets/css/epub.css"
    }
  },
  "metadata": {
    "title": "Your Book Title",
    "author": "Your Name", 
    "publisher": "Your Publisher",
    "description": "Your book description",
    "language": "ja",
    "publishDate": null,
    "isbn": "",
    "copyright": "© 2024 Your Name. All rights reserved."
  }
}
```

## PDF生成について

現在の実装では、印刷用に最適化されたHTMLファイル（`book-print.html`）を生成します。

### PDF変換手順

1. 生成された `book-print.html` ファイルをブラウザで開く
2. 印刷メニューから「PDFとして保存」を選択
3. 以下の設定を推奨:
   - **用紙サイズ**: A4
   - **余白**: 最小またはカスタム(20mm)
   - **背景のグラフィック**: チェック
   - **ヘッダーとフッター**: オフ

### 自動PDF生成

自動PDF生成には Puppeteer などのツールが必要ですが、環境により動作しない場合があります。確実な PDF生成には上記の手動変換手順をお勧めします。

## ePub生成について

完全に自動化されたePub生成機能を提供します。生成されるePubファイルは以下の特徴があります:

- **EPUB 3.0準拠**: 最新の電子書籍規格に対応
- **目次ナビゲーション**: 章立ての自動認識
- **レスポンシブデザイン**: 各種電子書籍リーダー対応
- **日本語対応**: 日本語フォントとレイアウト最適化

### 対応電子書籍リーダー

- Apple Books（iOS/macOS）
- Google Play ブックス
- Adobe Digital Editions
- Calibre
- その他EPUB 3.0対応リーダー

## カスタマイズ

### 印刷用CSS

`assets/css/print.css` を編集することで、PDF用のスタイルをカスタマイズできます:

- ページブレーク制御
- フォントサイズ調整
- マージン設定
- ヘッダー・フッター

### ePub用CSS

`assets/css/epub.css` を編集することで、ePub用のスタイルをカスタマイズできます:

- 電子書籍用フォント設定
- 行間・文字間隔調整
- カラースキーム

## トラブルシューティング

### よくある問題

1. **ePubファイルが開けない**
   - ファイルが完全に生成されているか確認
   - 電子書籍リーダーがEPUB 3.0に対応しているか確認

2. **PDFレイアウトが崩れる**
   - ブラウザの印刷設定を確認
   - `assets/css/print.css` のページブレーク設定を調整

3. **日本語フォントが表示されない**
   - システムに適切な日本語フォントがインストールされているか確認
   - CSSのフォールバックフォント設定を確認

### デバッグ

生成プロセスの詳細ログを確認するには:

```bash
# 詳細ログ付きで実行
DEBUG=* npm run generate:epub
```

## ファイル構成

```text
book-publishing-template/
├── assets/css/
│   ├── print.css          # PDF用スタイル
│   └── epub.css           # ePub用スタイル
├── scripts/
│   ├── generate-pdf.js    # PDF生成スクリプト
│   └── generate-epub.js   # ePub生成スクリプト
├── book-config.json       # 設定ファイル
├── book-print.html        # 生成される印刷用HTML
└── book.epub              # 生成されるePubファイル
```

## 今後の拡張予定

- [ ] Puppeteerによる完全自動PDF生成
- [ ] カバー画像の自動処理
- [ ] 複数言語対応
- [ ] 数式・図表の高品質出力
- [ ] Amazon Kindle形式（MOBI）対応
- [ ] InDesign形式エクスポート

---

この機能についてご質問やフィードバックがございましたら、GitHubのIssuesページでお知らせください。