# SL — Sheaf locality and gluing

> 設計紀錄：保存選題、分工與條件；現行敘述與證明見 [sheaf-locality.typ](../../src/sup/sheaf-locality.typ)，教材分工見 [總覽](README.md)。

定位：只處理局部檢查與 gluing。Sheaf Hom、limits、tensor 等例子全部放在 SC。

## 正文參照：只連結

[II.1 正文](../../src/sec-2-1/part-1.typ)：presheaf／sheaf、stalk、morphism、restriction 的定義；Proposition 1.1 的 stalkwise isomorphism criterion；Proposition-Definition 1.2 的 sheafification。

## 內容範圍

| 標記 | 內容 | 精確邊界 |
| --- | --- | --- |
| SL-1 | Sections 與 sheaf morphisms 在 open cover 上判等 | Morphisms 的相等也可逐 stalk 檢查；依據正文 sheaf axioms，不再重新定義。 |
| SL-2 | 從 open basis 指定 sheaf | 明列 basis 上的 restriction、cover gluing，以及對任意 open 的延伸與唯一性。若使用兩個 basis elements 的交集，允許再以 basis cover 細分。 |
| SL-3 | Gluing morphisms | 局部 morphisms 在 overlaps 上相等，便得到唯一全域 morphism；同時保留指定代數結構。 |
| SL-4 | Gluing sheaves | 指定 open cover、overlap isomorphisms 與 cocycle；存在帶指定識別的全域 sheaf，唯一到相容的唯一同構。 |
| SL-5 | 從 germs 回到鄰域 | germs 相等可縮小到同一鄰域；有限多個相等可同時縮小，不能直接推廣到無限多個。 |
| SL-6 | Sheafification 的局部表示與關係 | 每個 associated-sheaf section 局部來自原 presheaf；相等局部可在原 presheaf 中檢查；stalk 比較映射是同構。 |

## 適用範疇

SL-1–SL-4 分別處理 sets、abelian groups、commutative unital rings，以及固定 sheaf of rings O 上的 O-modules。Modules 的 gluing 使用 O 的 restrictions；若連 O 本身一起 glue，需將 ring gluing 與 module action 的相容資料明列。

代數運算由局部運算 glue；不聲稱這些程序自動適用任意 category-valued sheaves。

## 與其他教材的分工

- Injectivity、surjectivity、exactness 的 stalkwise 判準放 SC，避免兩篇各寫一次。
- 本篇不加入 construction 示範；SC 直接引用 SL-2–SL-6。
- Schemes 的 underlying spaces 與 locally ringed structures 的 gluing 放 XL。

## 習題對照

[II.1 exercises](../../src/sec-2-1/exe.typ)：1.22 的 gluing 是本篇主題；1.15 的 morphism gluing 工具在本篇，sheaf Hom 命題在 SC；1.3–1.5 的相關局部工具由本篇供 SC 引用。
