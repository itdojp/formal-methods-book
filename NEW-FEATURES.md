# 書籍コンテンツ作成システム - 新機能ガイド

> ⚠️ **注意**: このドキュメントで説明されている機能の一部は v2.0 では未実装です。基本的な機能は動作しますが、高度な機能は今後のアップデートで追加予定です。

## 🎯 自動目次生成機能

### 概要
書籍作成システムに自動目次生成機能が追加されました。すべてのMarkdownファイルから見出しを自動抽出し、構造化された目次を生成します。

### 特徴
- **自動抽出**: すべてのセクションのMarkdownファイルから見出しを自動抽出
- **階層構造**: 見出しレベル（H1, H2, H3...）に基づく階層表示
- **自動番号付け**: 章や付録の自動番号付け
- **柔軟な設定**: 深度、番号付け、出力ファイル名などカスタマイズ可能

### 生成例
```markdown
# 目次

- [はじめに](introduction/index.md#はじめに)
  - [本書の構成](introduction/index.md#本書の構成)
  - [対象読者](introduction/index.md#対象読者)
- [第1章: 基礎概念](chapters/chapter01/index.md#基礎概念)
  - [1.1 概要](chapters/chapter01/index.md#11-概要)
- [チュートリアル1: 基本操作](tutorials/tutorial01/index.md#チュートリアル1-基本操作)
- [付録A: 参考資料](appendices/appendix01/index.md#付録a-参考資料)
- [あとがき](afterword/index.md#あとがき)
```

## 🔧 柔軟なコンテンツ構成システム

### 概要
`book-config.json` による設定ファイルベースの柔軟なコンテンツ構成システムを追加しました。

### 主な改善点
- **カスタムセクション**: 独自のコンテンツセクションを追加可能
- **順序制御**: セクションの表示順序を自由に設定
- **有効/無効切り替え**: セクションの公開を個別に制御
- **番号付けカスタマイズ**: 各セクションの番号付けルールをカスタマイズ

### 設定例

#### 基本設定
```json
{
  "contentSections": [
    {
      "name": "introduction",
      "title": "はじめに",
      "directory": "introduction",
      "enabled": true,
      "order": 1
    },
    {
      "name": "chapters",
      "title": "本章",
      "directory": "chapters",
      "enabled": true,
      "order": 2,
      "numbering": true
    },
    {
      "name": "tutorials",
      "title": "チュートリアル",
      "directory": "tutorials",
      "enabled": true,
      "order": 3,
      "numbering": true
    }
  ]
}
```

#### 目次設定
```json
{
  "tableOfContents": {
    "enabled": true,
    "outputFile": "table-of-contents.md",
    "title": "目次",
    "maxDepth": 3,
    "includeNumbers": true
  }
}
```

## 🚀 使用方法

### 1. 設定ファイルの作成
プロジェクトルートに `book-config.json` を作成してコンテンツ構成をカスタマイズします。

### 2. コンテンツの作成
設定したディレクトリ構造に従ってコンテンツを作成します。

### 3. ビルド実行
```bash
npm run build
```

### 4. 目次の確認
生成された `public/table-of-contents.md` で目次を確認できます。

## 💡 活用例

### 技術書構成
- introduction（はじめに）
- basics（基礎編）
- advanced（応用編）
- references（参考資料）

### 教材構成
- introduction（導入）
- lessons（レッスン）
- exercises（演習）
- solutions（解答例）※無効化可能

### ブログ構成
- about（このブログについて）
- posts（記事）
- tutorials（チュートリアル）
- resources（リソース）

## 🔄 後方互換性

既存のプロジェクトでも設定ファイルなしで従来通り動作します。`book-config.json` がない場合はデフォルト設定が使用されます。