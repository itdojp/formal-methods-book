# 付録B：ツールインストールガイド

Alloy Analyzer、TLC、SPIN、Coq などの基本的な導入手順とトラブルシューティングの要点をまとめます（後続版で各 OS 別に詳細化）。

## クイックコマンド集

- Alloy（CLI系ツール利用時の例）
  - 実行: `alloy-cli check model.als --scope 5 --timeout 60`
- TLA+/TLC
  - 実行（bounded）: `tlc -config Spec.cfg -deadlock -depth 100 Spec.tla`
- SPIN
  - 検証: `spin -a model.pml && gcc pan.c -o pan && ./pan -a -m10000`
- Coq
  - バッチ: `coqc -Q . Project Main.v`

よくあるトラブル
- Java環境（Alloy/TLA+）: `JAVA_HOME`/`PATH` の未設定 → JDKのパスを確認
- 権限: 実行ビット不足 → `chmod +x`、WSL/権限境界の確認
- 時間制限: CIでのタイムアウト → 小スコープ/浅い深さでPR段階運用
