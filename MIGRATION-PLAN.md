# 📈 既存テンプレートからv2.0への段階的移行計画

## 🎯 移行の目的

既存の`book-publishing-template`からv2.0への円滑な移行を実現し、ユーザーの利便性を最大化する。

## 📊 移行戦略

### Phase 1: 並行運用期（1-2ヶ月）

#### 1.1 v2.0テンプレートの公開
- ✅ `book-publishing-template2`リポジトリの作成
- ✅ 改善機能の実装完了
- ✅ 単一リポジトリ構成への変更
- 🔄 テンプレートリポジトリとして設定
- 🔄 ドキュメント整備

#### 1.2 既存テンプレートへの改善案組み込み
```bash
# 既存リポジトリに改善ファイルを段階的に追加
git checkout -b feature/easy-setup
cp v2.0/easy-setup.js .
cp v2.0/scripts/build-simple.js scripts/
cp v2.0/QUICK-START.md .
```

#### 1.3 ユーザー向け移行ガイド作成
- 既存ユーザー向けアップグレード手順
- 新規ユーザー向け推奨テンプレート案内
- 比較表の作成

### Phase 2: 段階的移行（2-3ヶ月）

#### 2.1 既存テンプレートのREADME更新
```markdown
# 📚 Book Publishing Template

⚠️ **新バージョン利用可能**: より使いやすくなったv2.0が利用可能です
👉 [Book Publishing Template v2.0](https://github.com/itdojp/book-publishing-template2)

## 新規ユーザーの方
v2.0テンプレートの使用を強く推奨します：
- 1コマンドセットアップ
- 軽量・高速ビルド
- 日本語エラーメッセージ
- 5分で始められる
- 単一リポジトリでシンプル

## 既存ユーザーの方
[移行ガイド](#migration-guide)を参照してください
```

#### 2.2 Issues/Discussionsでの案内
- 新しい質問: v2.0への誘導
- 既存の問題: v2.0での解決確認
- 移行支援の提供

#### 2.3 機能の逆移植
```javascript
// 人気機能を既存テンプレートにも追加
// scripts/setup-wizard.js
const EasySetup = require('./easy-setup-legacy');
// 既存コードベースに適合させた軽量セットアップ
```

### Phase 3: 完全移行（4-6ヶ月）

#### 3.1 既存テンプレートのアーカイブ準備
```markdown
# ⚠️ アーカイブ予定のお知らせ

このテンプレートは20XX年XX月にアーカイブ予定です。
新しいプロジェクトには v2.0 をご利用ください。

移行支援: [migration-support@example.com]
```

#### 3.2 データ移行ツールの提供
```bash
# migrate-to-v2.js
node migrate-to-v2.js --from=./old-project --to=./new-project
```

#### 3.3 完全移行
- 既存テンプレートをread-only/archived状態に
- v2.0を公式テンプレートとして確立
- リダイレクト設定

## 🛠️ 技術的移行タスク

### 既存テンプレートへの改善追加

#### 1. Easy Setupの追加
```bash
# 既存テンプレートに追加
cp easy-setup.js ../book-publishing-template/
cd ../book-publishing-template
git checkout -b feature/easy-setup
git add easy-setup.js
git commit -m "Add easy setup wizard for better UX"
```

#### 2. 軽量ビルドオプションの追加
```bash
# 既存のpackage.jsonに追加
"scripts": {
  "build:simple": "node scripts/build-simple.js",
  "setup:easy": "node easy-setup.js"
}

# 注意: v2.0はdocs/フォルダへ出力、v1はpublic/フォルダへ出力
```

#### 3. ドキュメント改善
- QUICK-START.mdの追加
- README.mdにv2.0への案内を追加
- トラブルシューティングの改善

### v2.0テンプレートの完成

#### 1. テンプレートリポジトリ設定
```bash
# GitHubでSettings → Template repository を有効化
```

#### 2. 完全なドキュメント
- API リファレンス
- 移行ガイド
- ベストプラクティス
- FAQ

#### 3. CI/CD設定
```yaml
# .github/workflows/test-template.yml
name: Test Template
on: [push, pull_request]
jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - name: Test Easy Setup
        run: |
          echo "Test Book" | node easy-setup.js --test
      - name: Test Build
        run: node scripts/build-simple.js
```

## 📊 移行メトリクス

### 成功指標
- [ ] v2.0テンプレート使用開始: 50プロジェクト/月
- [ ] 既存テンプレートのIssue減少: 70%削減
- [ ] セットアップ成功率: 95%以上
- [ ] ユーザー満足度: 4.5/5.0以上

### 追跡項目
- Template使用数（GitHub Insights）
- Issue数の推移
- Setup失敗率
- ユーザーフィードバック

## 🗓️ スケジュール

| 期間 | タスク | 責任者 | 状況 |
|------|--------|--------|------|
| Week 1-2 | v2.0テンプレート公開 | Dev Team | ✅ |
| Week 3-4 | 既存テンプレートにEasy Setup追加 | Dev Team | 🔄 |
| Week 5-8 | ユーザー案内・移行支援 | Support Team | 📋 |
| Month 3-4 | 段階的移行実施 | All Teams | 📋 |
| Month 5-6 | 完全移行・アーカイブ | All Teams | 📋 |

## 🔄 リスク管理

### 想定リスク
1. **既存ユーザーの混乱**
   - 対策: 明確な案内とサポート強化
   - 軽減: 段階的移行とドキュメント充実

2. **互換性問題**
   - 対策: 移行ツールの提供
   - 軽減: テスト環境での事前検証

3. **採用率の低さ**
   - 対策: メリットの明確化
   - 軽減: 既存ユーザーへの個別サポート

### 緊急時対応
- ロールバック手順の準備
- 緊急サポート体制の構築
- コミュニティフィードバックの迅速対応

## 📞 サポート体制

### 移行支援チーム
- **技術サポート**: 移行手順の案内
- **ドキュメント**: ガイド作成・更新  
- **コミュニティ**: フィードバック収集・対応

### 連絡先
- Issues: GitHub Issues
- 緊急時: knowledge@itdo.jp
- コミュニティ: Discussions

---

**この移行計画により、ユーザーにとって最適な書籍出版環境を提供し続けます。**