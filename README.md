# Math Docs

## Environment

1. Install typst

```bash
brew install typst
```

2. Install Lean with Elan

```bash
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
source "$HOME/.elan/env"
lake exe cache get
```

Run the setup commands from the repository root. Elan reads `lean-toolchain`,
and `lake exe cache get` downloads the matching mathlib build cache.

## Lean

Check all Lean files in `alg-geo`:

```bash
pnpm -F @math-books/alg-geo lean
```

Check one Lean file from the repository root:

```bash
lake env lean books/alg-geo/src/sup/lean/ii-5-exe.lean
```

## Initialize

1. Initialize with template

```bash
typst init @preview/ilm:1.4.1 <DIR>
```

2. VScode formatter settings

```json
// settings.json
{
  // ...
  "tinymist.formatterMode": "typstfmt",
  "[typst]": {
    "editor.defaultFormatter": "myriad-dreamin.tinymist",
    "editor.formatOnSave": true
  }
}
```

## alg-geo Typst packages

alg-geo 使用兩個 repo 內的 [Typst packages](packages/README.md)：
`@steee-book/blocks` 提供 block／box 與補充教材編號，
`@steee-book/symbols` 提供數學符號。不需發布或全域安裝。
書籍 build/dev scripts 已設定 package 搜尋路徑。

從 repo 根目錄編譯：

```sh
typst compile --package-path packages books/alg-geo/src/main.typ books/alg-geo/dist/alg-geo.pdf
```
