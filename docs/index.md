---
layout: book
title: "形式的手法の基礎と応用"
locale: "ja"
lang: "ja"
source_path: "src/ja/index.md"
---
# 形式的手法の基礎と応用

仕様記述、模型検査、定理証明の統合的理解 - ソフトウェアの数学的設計入門

## 概念マップ

本書の構造を最短で把握したい場合は、まず全体の概念マップを確認してください。

![概念マップ：形式的手法学習の体系的ロードマップ（4部13章構成、図1-2）]({{ '/assets/images/diagrams/formal-methods-roadmap.svg' | relative_url }})

- 4部13章の役割分担を俯瞰できる。
- 詳細は [第1章の学習ロードマップ]({{ '/chapters/chapter01/' | relative_url }}) を参照すると、読み進める順序を定めやすい。
- 章末の `summary` / `nextSteps` と併用すると、必要な戻り先と次の読解順を固定しやすい。

## 学習成果

- 形式的手法が必要とされる背景とメリット・限界を理解し、「どのような問題に対してどの程度のコストで適用するのか」を説明できるようになる。
- Alloy / Z / CSP / TLA+ など代表的な形式仕様記述言語や模型検査・定理証明技法の位置づけを整理し、自分の関心やプロジェクトに合った手法を選定する際の観点を持てるようになる。
- 小規模な仕様やプロトコルを対象に、簡単な形式仕様を書き、ツールを用いた模型検査や性質検証を実行するまでの一連の流れを体験できるようになる。
- 実務や研究において、形式的手法の考え方を「完全導入」だけでなく、設計レビュー・テスト設計・ドキュメント改善など部分的な導入にも応用する発想を持てるようになる。

## 読み方ガイド

- 形式的手法に初めて触れる読者は、第I部（第1〜3章）を順に読み、「なぜ必要か」「どのような数学的基盤があるか」を押さえたうえで、第II部以降の個別手法に進むことを推奨する。
- すでに特定の手法（例: TLA+ や Alloy）に興味がある読者は、該当章から読み始めつつ、第1章〜2章を参照して背景や比較の観点を補完する読み方も有効である。
- 検証技術やツール運用に関心が高い読者は、第III部（模型検査・定理証明・プログラム検証）を軸に読み、前後の章を必要に応じて行き来する形で活用してほしい。
- 実務への適用を検討している読者は、第IV部（事例研究・適用パターン）を中心に読みつつ、関係する基礎章を併せて確認することで、自組織への導入シナリオをイメージしやすくなる。


## 学習導線の補足

- 全体像の把握には、[第1章の学習ロードマップ]({{ '/chapters/chapter01/' | relative_url }}) を起点にすると、部ごとの役割が追いやすい。
- 用語の意味や略語は [用語集（Glossary）]({{ '/glossary/' | relative_url }}) で確認し、記法や構文の差分は [付録C: 記法対照表]({{ '/appendices/appendix-c/' | relative_url }}) で確認する。
- 長い章を読むときは、[第9章]({{ '/chapters/chapter09/' | relative_url }}) など章末に `summary` と `nextSteps` が用意されている章では、先にそれらを確認して、必要な戻り先と次の読解順を固定する。

## 安全に使うための注意

- 形式仕様、模型検査、定理証明の結果は、前提条件と抽象化の置き方に依存する。検証結果だけでシステム全体の安全性や完全性を断定しない。
- 実務へ適用する場合は、検証対象の範囲、未検証の前提、環境差分をレビューや設計文書に残し、関係者の合意を取ってから利用する。
- ツールの構文やオプションは変わるため、付録Bや第8章〜第12章の手順を再利用する前に、利用中ツールの公式ドキュメントを確認する。

## 想定読者

本書は以下の方を対象としています。

主対象は、ソフトウェア設計・品質保証・安全性向上に形式的手法を部分導入したい実務エンジニアです。学生・研究者は、理論と実践の橋渡しとして活用できます。

- **ソフトウェア設計・開発に従事するエンジニア**：より厳密で信頼性の高いソフトウェア設計手法を学びたい方
- **品質保証・テストエンジニア**：数学的検証による品質保証手法を習得したい方
- **安全クリティカルシステム開発者**：形式的手法による安全性保証が求められる分野の技術者
- **コンピュータサイエンス学生・研究者**：理論と実践を結ぶ形式的手法の理解を深めたい方

## 前提知識

本書を効果的に活用するために、以下の基礎知識があることを前提としています。

- **プログラミング分野**：基本的なプログラミング経験、データ構造とアルゴリズムの基本概念、オブジェクト指向プログラミングの基礎
- **数学分野**：高校数学レベル（集合、論理、関数の概念）、離散数学の基礎（特に集合論と論理学の初歩）、証明の基本的な考え方
- **ソフトウェア工学分野**：要求分析と設計の基本概念、テスト手法の基礎知識、ソフトウェアライフサイクルの理解

本書では数学的記法を多用しますが、すべて基本的なレベルから説明します。高度な数学知識は必要ありません。

## 所要時間

目安（全体を通して学ぶ場合）:

- 本文の通読: 約8〜16時間
- 演習（章末課題・ツール実行）を含む: 約25〜40時間

読者の背景や演習の取捨選択により所要時間は変動します。章単位で区切って進めることを推奨します。

## 目次

- [はじめに]({{ '/introduction/' | relative_url }})
- [用語集（Glossary）]({{ '/glossary/' | relative_url }})

### 第I部　基礎編：形式的手法の基盤

- [第1章 なぜ形式的手法が必要なのか]({{ '/chapters/chapter01/' | relative_url }})
- [第2章 数学とプログラムの橋渡し]({{ '/chapters/chapter02/' | relative_url }})
- [第3章 仕様記述の基本]({{ '/chapters/chapter03/' | relative_url }})

### 第II部　手法編：主要な形式的手法の理解

- [第4章 軽量形式的手法入門 - Alloyで始める仕様記述]({{ '/chapters/chapter04/' | relative_url }})
- [第5章 状態ベース仕様記述 - Z記法の基礎]({{ '/chapters/chapter05/' | relative_url }})
- [第6章 プロセス中心の記述 - CSPによる並行システム]({{ '/chapters/chapter06/' | relative_url }})
- [第7章 時間を扱う仕様記述 - TLA+入門]({{ '/chapters/chapter07/' | relative_url }})

### 第III部　検証編：システムの正しさの確認

- [第8章 模型検査入門]({{ '/chapters/chapter08/' | relative_url }})
- [第9章 定理証明の基礎]({{ '/chapters/chapter09/' | relative_url }})
- [第10章 プログラム検証]({{ '/chapters/chapter10/' | relative_url }})

### 第IV部　実践編：実際のプロジェクトでの活用

- [第11章 開発プロセスとの統合]({{ '/chapters/chapter11/' | relative_url }})
- [第12章 ツールと自動化]({{ '/chapters/chapter12/' | relative_url }})
- [第13章 事例研究]({{ '/chapters/chapter13/' | relative_url }})

補足: 各章末の演習についての解答の骨子・採点観点は、[付録D: 演習問題解答]({{ '/appendices/appendix-d/' | relative_url }})を参照してください。

## 付録

- [付録A: 数学的基礎の復習]({{ '/appendices/appendix-a/' | relative_url }})
- [付録B: ツールインストールガイド]({{ '/appendices/appendix-b/' | relative_url }})
- [付録C: 記法対照表]({{ '/appendices/appendix-c/' | relative_url }})
- [付録D: 演習問題解答]({{ '/appendices/appendix-d/' | relative_url }})
- [付録E: 参考文献とWebリソース]({{ '/appendices/appendix-e/' | relative_url }})
- [付録F: AI支援の実践ガイド]({{ '/appendices/appendix-f/' | relative_url }})
- [おわりに]({{ '/afterword/' | relative_url }})

## 利用と更新情報

<!-- markdownlint-disable MD034 -->
{% assign repo_url = site.github.repository_url | default: site.repository_url | default: site.repository.github | default: site.repository %}
{% if repo_url and repo_url != '' %}
{% unless repo_url contains 'http' %}
{% assign repo_url = 'https://github.com/' | append: repo_url %}
{% endunless %}
{% endif %}
{% assign repo_branch = site.repository_branch | default: 'main' %}
<!-- markdownlint-enable MD034 -->

- 公開ページ: [GitHub Pages](https://itdojp.github.io/formal-methods-book/)
- リポジトリ: [GitHub]({{ repo_url }})
- 更新確認先: [コミット履歴]({{ repo_url }}/commits/{{ repo_branch }}/)、[PR 一覧]({{ repo_url }}/pulls)
- 付録Eは一次情報や関連資料の入口、付録Fは AI支援併用時の注意点の入口として使ってください。

## ライセンス

本書の本文・図版・付録などの reader-facing コンテンツは `CC BY-NC-SA 4.0`、コード例・ツール・ビルド資産は `Apache-2.0` で提供します。

<!-- markdownlint-disable MD034 -->
{% assign repo_url = site.github.repository_url | default: site.repository_url | default: site.repository.github | default: site.repository %}
{% if repo_url and repo_url != '' %}
{% unless repo_url contains 'http' %}
{% assign repo_url = 'https://github.com/' | append: repo_url %}
{% endunless %}
{% endif %}
{% assign repo_branch = site.repository_branch | default: 'main' %}

- [CC BY-NC-SA 4.0 の法的全文]({{ repo_url }}/blob/{{ repo_branch }}/LICENSE)
- [ライセンス適用範囲]({{ repo_url }}/blob/{{ repo_branch }}/LICENSE-SCOPE.md)
- [商用利用窓口]({{ repo_url }}/blob/{{ repo_branch }}/COMMERCIAL.md)
- [商標の扱い]({{ repo_url }}/blob/{{ repo_branch }}/TRADEMARKS.md)
- [third-party / upstream 資産]({{ repo_url }}/blob/{{ repo_branch }}/THIRD_PARTY_NOTICES.md)
<!-- markdownlint-enable MD034 -->

**お問い合わせ**  
株式会社アイティードゥ（ITDO Inc.）  
Email: [knowledge@itdo.jp](mailto:knowledge@itdo.jp)

---

**著者:** 太田和彦（株式会社アイティードゥ）  
**バージョン:** 1.0.0  
**最終更新:** {{ site.time | date: '%Y-%m-%d' }}  
**GitHub Pages:** 自動デプロイ対応
