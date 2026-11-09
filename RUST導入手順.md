# Rust 導入手順

Debian 環境で Rust を導入し、このリポジトリのリリースビルドを行う手順です。
Rust は公式推奨の rustup を使い、ユーザーのホームディレクトリにインストールします。

公式手順: https://rust-lang.org/tools/install/

## 1. 必要なパッケージをインストール

```bash
sudo apt-get update
sudo apt-get install -y curl ca-certificates build-essential libicu-dev
```

## 2. Rust をインストール

以下の操作に `sudo` は不要です。

```bash
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
```

選択画面では、標準インストールの `1` を選びます。

## 3. 現在のシェルに設定を反映

```bash
source "$HOME/.cargo/env"
rustc --version
cargo --version
```

このリポジトリは Rust 1.93 以上を要求しています。

## 4. 安定版をリポジトリに設定

通常のビルドには安定版（stable）を使用します。
標準インストールで導入されますが、以下のコマンドで更新と使用設定を行えます。

```bash
rustup toolchain install stable --profile minimal

cd /home/youmikou/git/a9Edit
rustup override set stable
```

リポジトリを別の場所に配置した場合は、`cd` のパスを置き換えてください。
`rustup override set stable` は、このディレクトリと配下で使用するツールチェーンを設定します。
以前に nightly を設定していた場合も、このコマンドで stable に切り替わります。

## 5. リリースビルド

リポジトリのルートで実行します。

```bash
cargo build --package a9edit --release --bin a9Edit --locked
```

生成されるバイナリは `target/release/a9Edit` です。

```bash
./target/release/a9Edit <ファイル名>
```

以降のビルドでは、検証時に使用した `/tmp` の Rust や、一時的な `CARGO_HOME`・`RUSTUP_HOME` の指定は不要です。
