# Repo-local Typst packages

兩個 package 各自獨立，不發布，也不安裝到使用者的全域 package 目錄。

```typst
#import "@steee-book/blocks:0.1.0": *
#import "@steee-book/symbols:0.1.0": *
```

Typst 的 package import 需要版本號，因此完整名稱包含 `:0.1.0`。
來源依 `<namespace>/<name>/<version>` 放在此目錄，CLI 以
`--package-path packages` 找到它們。

## Blocks

[blocks](steee-book/blocks/0.1.0/lib.typ) 封裝 Theorion 0.6.0 與原有客製化
block／box wrapper。正文與補充教材使用同一組名稱，書內不需知道上游樣式或
supplement 實作模組。

正文：

```typst
#import "@steee-book/blocks:0.1.0": *
#show: show-blocks

#theorem[Statement.]
#proof[Argument.]
#example(number: "1.1")[An example.]
#exercise(title: "Exercise 1.1")[A practice problem.]
```

補充教材：

```typst
#import "@steee-book/blocks:0.1.0": *
#show: show-blocks
#supplement-numbering("DEMO")

#theorem(key: "demo-1")[Statement.]
#proof[Argument.]
#example(key: "demo-2")[An example.]
#exercise(key: "demo-3")[A numbered exercise.]
#exercise(numbered: false, title: "Further practice")[An unnumbered exercise.]
```

`theorem`、`lemma`、`corollary`、`definition`、`proposition`、`example`、
`remark`、`exercise` 在補充教材中共用文章代碼與計數器。
`proof` 在此模式套用原有的清單標題分頁修正。
`show-blocks` 會讓每篇文章從正文模式開始；`supplement-numbering(prefix)`
切換至補充教材模式並重設編號，`main-numbering()` 可切回正文模式。

此 package 也提供 `notation`、其他 Theorion block wrapper，及
`book-link`／`supplement-link` 交叉引用工具。

## Symbols

[symbols](steee-book/symbols/0.1.0/lib.typ) 只包含數學記號，不依賴 blocks 或
Theorion。保留原有 `ops`、`cat`、`sym` module，以及 `idl`、`sch`、`shf`、
`tensor`、`fiber`、`ideal`、箭頭等定義與用法。

```typst
#import "@steee-book/symbols:0.1.0": *

$ops.spec A$, $tensor(M, N, over: A)$, $cat.sch$
```

`books/alg-geo/src/defs.typ` 僅保留為舊記號參考的相容入口。

## Other packages

書籍版面與圖表工具由書內直接匯入，與這兩個 package 分開：

```typst
#import "@preview/ilm:1.4.1": *
#import "@preview/fletcher:0.5.8" as fletcher: *
#import "@preview/cetz:0.3.4" as cetz: *
```

圖表套件先匯入，再匯入 blocks 與 symbols，讓既有自訂名稱優先。

## Compile and preview

從 repo 根目錄執行：

```sh
typst compile --package-path packages books/alg-geo/src/main.typ books/alg-geo/dist/alg-geo.pdf
typst compile --root . --package-path packages books/alg-geo/src/sup/blowups.typ /tmp/blowups.pdf
```

alg-geo 的 build/dev scripts 已包含 package 搜尋路徑。VS Code 的
`tinymist.typstExtraArgs` 也設定相同路徑；請以整個 repo 作為 workspace。

參考：[Typst packages](https://github.com/typst/packages/blob/main/README.md)、
[Tinymist compiler settings](https://myriad-dreamin.github.io/tinymist/feature/compiler-settings.html#packages-roots-and-certificates)。
