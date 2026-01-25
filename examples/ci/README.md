# CI examples

## PR向け（軽量チェック）

```bash
bash examples/ci/pr-quick-check.sh
```

## 夜間向け（深い探索）の例

`.github/workflows/formal-checks.yml` に、`schedule`（夜間）ジョブの例を含めています。  
探索深度・反例保存・artifact化の運用は、対象モデルに合わせて調整してください。

