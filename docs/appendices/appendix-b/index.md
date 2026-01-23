# 付録B：ツールインストールガイド

本付録は、主要ツールの導入手順とトラブルシューティングをまとめたものです。コマンドは代表例であり、配布形式や前提は変更される可能性があります。必ず公式ドキュメントも参照してください。

## B.1 Alloy Analyzer

### システム要件
- Java 8以上（推奨：Java 11）
- メモリ：最低2GB、推奨4GB以上
- OS：Windows、macOS、Linux（Java対応OS）

### インストール手順

**Windows環境**
1. Javaの確認と設定
   ```cmd
   java -version
   ```
   Java 8以上がインストールされていない場合は、Oracle JDKまたはOpenJDKをインストールします。

2. Alloyのダウンロード
   - MIT Alloy公式サイト（alloytools.org）から最新版をダウンロード
   - `alloy-x.x.x.jar` を適切なディレクトリに配置

3. 実行の確認
   ```cmd
   java -jar alloy-x.x.x.jar
   ```
   **期待結果**: Alloy AnalyzerのGUIが起動すること。

**macOS環境**
1. Homebrewを使用したJavaインストール（推奨）
   ```bash
   brew install openjdk@11
   echo 'export PATH="/opt/homebrew/opt/openjdk@11/bin:$PATH"' >> ~/.zshrc
   ```

2. Alloyの配置と実行
   ```bash
   wget https://github.com/AlloyTools/org.alloytools.alloy/releases/download/v6.0.0/org.alloytools.alloy.dist.jar
   chmod +x org.alloytools.alloy.dist.jar
   java -jar org.alloytools.alloy.dist.jar
   ```
   **期待結果**: Alloy AnalyzerのGUIが起動すること。

**Linux環境**（Ubuntu/Debian例）
1. Javaのインストール
   ```bash
   sudo apt update
   sudo apt install openjdk-11-jdk
   ```

2. Alloyの配置
   ```bash
   mkdir ~/alloy
   cd ~/alloy
   wget https://github.com/AlloyTools/org.alloytools.alloy/releases/download/v6.0.0/org.alloytools.alloy.dist.jar
   java -jar org.alloytools.alloy.dist.jar
   ```
   **期待結果**: Alloy AnalyzerのGUIが起動すること。

### トラブルシューティング

**起動しない場合**
- Javaのバージョン確認：`java -version`
- メモリ不足の場合：`java -Xmx4g -jar alloy-x.x.x.jar`
- ディスプレイ問題（Linux）：X11転送の設定確認

**性能問題**
- ヒープサイズの調整：`-Xmx8g`でメモリを増加
- ソルバーの設定：Alloy設定でSATソルバーを変更

## B.2 TLA+ ツールセット

### システム要件
- Java 8以上
- メモリ：最低4GB、推奨8GB以上（大規模モデル用）
- OS：Windows、macOS、Linux

### TLA+ Toolboxのインストール

**全プラットフォーム共通**
1. TLA+公式サイト（lamport.azurewebsites.net/tla）からTLA+ Toolboxをダウンロード
2. プラットフォーム別のインストーラーを実行

**追加設定**
- TLCチェッカーのメモリ設定例
  ```
  -Xmx4g -Xms1g
  ```
- 並列処理のワーカー数をCPU数に応じて調整

### コマンドラインツールのインストール

**tlaps（証明システム）**
1. 依存関係のインストール（Linux例）
   ```bash
   sudo apt install ocaml-interp opam
   opam init
   eval $(opam env)
   ```

2. TLAPSのビルド
   ```bash
   git clone https://github.com/tlaplus/tlapm.git
   cd tlapm
   ./configure && make && sudo make install
   ```

## B.3 SPIN模型検査器

### システム要件
- Cコンパイラ（GCC、Clang、MSVCなど）
- makeユーティリティ
- OS：Windows（MinGW/MSYS2）、macOS、Linux

### インストール手順

**Linux/macOS**
1. ソースコードのダウンロード
   ```bash
   wget http://spinroot.com/spin/Src/spin654.tar.gz
   tar -xzf spin654.tar.gz
   cd Spin/Src6.5.4
   ```

2. ビルドとインストール
   ```bash
   make
   sudo cp spin /usr/local/bin/
   ```

**Windows（MSYS2使用）**
1. MSYS2のインストール（公式サイトから）
2. 開発ツールのインストール
   ```bash
   pacman -S gcc make
   ```
3. 上記Linux手順に従ってビルド

### 動作確認

**簡単なテストファイルの作成**
```promela
// test.pml
active proctype P() {
    printf("Hello SPIN\n")
}
```

**実行テスト**
```bash
spin -a test.pml
gcc -o pan pan.c
./pan
```
**期待結果**: `Hello SPIN` が標準出力に表示されること。

## B.4 Coq証明支援系

### システム要件
- OCaml 4.09以上
- メモリ：最低2GB、推奨4GB以上

### インストール方法

**OPAM使用（推奨）**
1. OPAMのインストール
   ```bash
   # Ubuntu/Debian
   sudo apt install opam
   # macOS
   brew install opam
   ```

2. Coqのインストール
   ```bash
   opam init
   eval $(opam env)
   opam install coq
   ```

**CoqIDEのインストール**
```bash
opam install coqide
```

**VS Codeプラグイン**
- VS Codeに「VSCoq」拡張機能をインストール
- Coqへのパスを設定

### 初期設定と確認

**基本動作テスト**
```coq
(* test.v *)
Theorem identity : forall A : Prop, A -> A.
Proof.
  intros A H.
  exact H.
Qed.
```

**コンパイル確認**
```bash
coqc test.v
```
**期待結果**: エラーなくコンパイルが完了すること。

## B.5 統合開発環境の設定

## B.5.1 手動インストール不要の代替（Docker/Devcontainer）

手元の環境差異を減らしたい場合は、コンテナ経由の実行を推奨します。

**Docker（例）**
```bash
# 例: 公式/サードパーティのイメージは更新されるため、最新の配布URL/タグは公式を参照
docker run --rm -it -v "$PWD:/work" --workdir /work ghcr.io/<org>/<image>:<tag> <tool-command>
```

**Devcontainer（VS Code）**
1. `.devcontainer/devcontainer.json` を作成
2. 必要なツールを `Dockerfile` もしくは `features` で導入
3. VS Codeで「Reopen in Container」を実行

最小構成の例（概念サンプル）:
```json
{
  "name": "formal-methods",
  "image": "mcr.microsoft.com/devcontainers/base:ubuntu",
  "features": {},
  "postCreateCommand": "apt-get update && apt-get install -y openjdk-11-jre"
}
```

### VS Code環境設定

**必要な拡張機能**
- Alloy: "Alloy Language Support"
- TLA+: "TLA+"
- Coq: "VSCoq"
- SPIN: "Promela"（非公式）

**設定例（settings.json）**
```json
{
    "tlaplus.java.path": "/usr/bin/java",
    "tlaplus.tlc.jvmArgs": "-Xmx4g",
    "coq.format.enable": true,
    "alloy.analyzer.path": "/path/to/alloy.jar"
}
```

### Emacs環境設定

**必要なパッケージ**
```lisp
;; .emacsまたはinit.el
(require 'package)
(add-to-list 'package-archives
             '("melpa" . "https://melpa.org/packages/"))
(package-initialize)

;; パッケージのインストール
;; M-x package-install RET proof-general RET
;; M-x package-install RET company-coq RET
```

## B.6 共通的なトラブルシューティング

### CI上でのheadless実行

GUI前提のツールは、CIではCLIモードやheadless実行が必要です。
例:
- Alloy: コマンドライン実行 + 出力のログ化（GUIを前提にしない）
- TLC: `-dump` などのCLIオプションを活用

CIでは「短時間・小スコープ」での検証を優先し、実行時間と再現性の両立を図ってください。

### メモリ関連問題

**Java OutOfMemoryエラー**
```bash
# ヒープサイズの増加
java -Xmx8g -jar tool.jar

# ガベージコレクションの調整
java -XX:+UseG1GC -jar tool.jar
```

**大規模モデルでの性能問題**
- 段階的モデル作成による検証
- 抽象化レベルの調整
- 並列実行の活用

### パス・環境設定問題

**PATHの設定**
```bash
# .bashrc または .zshrc
export PATH="$PATH:/usr/local/bin:/path/to/tools"
export JAVA_HOME="/path/to/java"
```

**権限問題（Linux/macOS）**
```bash
# 実行権限の付与
chmod +x tool-binary

# ユーザ専用ディレクトリへのインストール例（推奨）
mkdir -p "$HOME/.local/bin"
mv tool-binary "$HOME/.local/bin/"

# どうしてもsudoが必要な場合は、特定のツール用ディレクトリに限定して権限を変更する
# ※ /usr/local/bin 全体を chown しないこと！
sudo chown "$USER":"$USER" /usr/local/lib/mytool/tool-binary
```

### ネットワーク・ファイアウォール問題

**プロキシ環境での設定**
```bash
# Java系ツール
java -Dhttp.proxyHost=proxy.company.com -Dhttp.proxyPort=8080

# パッケージマネージャ設定
opam config set https-proxy http://proxy.company.com:8080
```

このインストールガイドにより、主要な形式的手法ツールを確実にセットアップし、学習や実践に集中できる環境を構築できます。問題が発生した場合は、各ツールの公式ドキュメントとコミュニティフォーラムも併せて参照してください。
