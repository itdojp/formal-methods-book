# 変更履歴

本書に関する注目すべき変更を記録します。
記載方針は [Keep a Changelog](https://keepachangelog.com/ja/1.1.0/) と、書籍向けの運用ルールに従います。

## [Unreleased]

### Added

- #325 第8章、付録、用語集にSymbiYosysによる同期RTL形式検証を追加し、欠陥arbiterのBMC反例、修正版のk-induction、cover witnessをOSS CAD Suite 20260716・Bitwuzla 0.9.1・固定digestのnightly契約で再実行できるようにしました。
- #324 第13章、付録、用語集にTamarin Prover 1.12.0によるDolev–Yao攻撃者下のsymbolic protocol verificationを追加し、再送欠陥と修正版をMaude 3.5.1・固定digest・nightly artifact契約で再実行できるようにしました。
- #323 第8章、付録、用語集にPRISM 4.10.1による確率的・定量的模型検査を追加し、bounded retry DTMCの到達確率、閾値、定常確率、期待costを固定digestのnightly契約で再実行できるようにしました。

## [1.1.0] - 2026-07-16

Roadmap #328 の Phase 0 と Phase 1 を対象にした書籍更新です。対象 Issue は #295-#301 と #313-#322 であり、Phase 2 の #323-#327 は本版に含めません。

### Added

#### 読者向け変更

- #295 第4章に Alloy 6 の時相・振る舞いモデリング、bounded trace semantics、TLA+ との橋渡し説明を追加しました。
- #296 第7章・第8章・第12章を、TLC / Apalache / Quint / CI を中心とした現行の TLA+ ツールチェーン説明へ更新しました。
- #297 第10章に Rust の形式検証ツール群と、Aeneas を含む周辺導線を追加しました。
- #298 第9章・付録Fに Lean / Rocq / LLM 支援証明の最新動向を追加しました。
- #299 第12章に、検証成果物の CI 管理、再実行可能な証跡、SMT-LIB v3 / cvc5 動向を追加しました。
- #300 第13章に Cedar、生成AIガードレール、スマートコントラクト検証の事例を追加しました。
- #301 付録B・C・E・F、用語集、第9章の要約と次の一歩を 2026 年版の内容に合わせて整合させました。
- #321 日本語版・英語版の全 reader page を対象にした書籍横断検索を追加し、別名検索、断片リンク、要約スニペットに対応しました。

#### サイトとアクセシビリティ

- #317 英語 reader page に translation status、source commit、review 日、追跡 Issue を公開し、partial / stale を黙って公開しない運用へ変更しました。
- #318 日本語版・英語版のトップ、章、付録、special page の metadata と導線を正規化し、生成物の drift を検出できるようにしました。
- #319 `build-provenance.json` と公開ページ上の version / source commit / generated-at / release / Pages run 表示を、release 検証対象として明文化しました。
- #321 検索 UI を combobox / listbox のキーボード操作と text-node-only rendering を前提に実装し、reader-facing の探索性を改善しました。

### Fixed

#### 技術的正確性

- #313 第7章の TLA+ 記述を修正し、next / prime、stuttering を許容する仕様形、`~>` / WF / SF、公正性、refinement の方向、mapping / hiding の境界を明確化しました。
- #314 模型検査・論理・分散理論の保証表現を精密化し、CAP / FLP の前提、soundness / completeness の適用範囲、trusted kernel / axiom / solver / extraction の境界を明示しました。

### Changed

#### ツールと再現性

- #315 「そのまま動く」と扱う範囲を 12 個の manifest 契約に限定し、Alloy 6.2.0、TLC 1.7.4、Apalache 0.52.1、Dafny 4.11.0、SPIN 6.5.2、NuSMV 2.7.1、CBMC 6.10.0 の実行証跡を CI lane と結び付けました。
- #316 日本語公開章を `src/ja/**` から決定的に生成する構成へ移行し、`docs/chapters/**` の本文二重管理を解消しました。
- #317 `translation-status.json` を正本にし、英語版 23 ページの同期状態、review 日、追跡 Issue、差分種別を機械検証できるようにしました。
- #318 `book-config.json`、edition config、publication config から、ナビゲーション・Jekyll 設定・locale metadata・mobile config を生成する構成へ整理しました。
- #319 v1.1.0 向けの CHANGELOG、release notes、release 手順書を整備し、release 時に確認すべき provenance / source commit / Pages 検証の観点を文書化しました。
- #320 追跡済み `node_modules/**`、`docs/_site/**`、旧テンプレート残骸を削除し、`package-lock.json` と `npm ci` を依存契約として一本化しました。
- #322 `tools/tool-manifest.json` を導入し、PR / nightly / optional の lane ごとに version、配布物 digest、artifact 制約、documentation-only 区分を明示しました。

### Removed

- #320 Git 管理されていた `node_modules/**`、Jekyll 生成物 `docs/_site/**`、ネストした重複ツリー、未使用の template 由来ファイル群を削除しました。
- #320 PDF / EPUB 用の旧 template 残骸、印刷用 CSS、未使用 JavaScript、比較・移行・preview 用文書を削除しました。

[Unreleased]: https://github.com/itdojp/formal-methods-book/compare/v1.1.0...HEAD
[1.1.0]: https://github.com/itdojp/formal-methods-book/releases/tag/v1.1.0
