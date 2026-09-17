# VS — Varieties and schemes

> 設計紀錄：保存選題、分工與條件；現行敘述與證明見 [varieties-schemes.typ](../../src/sup/varieties-schemes.typ)，教材分工見 [總覽](README.md)。

定位：整理 classical variety 與 associated scheme 之間最常用的識別。固定 algebraically closed field k，variety 採用 Chapter I 的慣例；不把結論無條件推廣到任意 base field。範圍限於核心內容。

## 正文參照：只連結

- [II.2, Proposition 2.6](../../src/sec-2-2/part-1.typ)：t 的建構與 fully faithfulness。
- 同節 Propositions 2.2、2.5：Spec／Proj 的 affine charts 與 structure sheaves。
- [II.4, Proposition 4.10 與 D4](../../src/sec-2-4/part-1.typ)：Chapter I varieties 所對應的 scheme 範圍，以及 abstract varieties 的定義。只設範圍提示，不另發展 abstract-variety 理論。

## 核心內容

| 標記 | 擬收錄內容 | 條件與分工 |
| --- | --- | --- |
| VS-1 | Classical points、closed scheme points 與 residue fields | V 的 points 對應 t(V) 的 closed points，亦即 residue field 為 k 的 points；generic points 與其他非閉點由 XP 的一般結果說明。Field-valued-point 的一般命題引用 MG-7。 |
| VS-2 | Affine／projective variety 的 Spec／Proj 識別 | Affine V 使用 coordinate ring A(V)，projective V 使用 homogeneous coordinate ring S(V)；明列 t(V) 與 Spec A(V)／Proj S(V) 的 canonical identification，連結其 affine charts、regular functions 與 structure-sheaf restrictions。正文已提供的公式只引用。 |
| VS-3 | Regular maps 與 scheme morphisms 的對應入口 | 引用正文 fully faithfulness，整理兩個方向如何回到 classical points 與 regular functions；k-morphisms 保留 k-rational points 的一般結果引用 MG-7。不重新證明 t 的 fully faithfulness。 |

## 核心比較例子

- A^1_k 的 classical points 與 Spec k[t]：maximal ideals (t-a) 對應 classical points，(0) 是新增的 generic point；不把 scheme 的所有 points 都視為 k-rational points。
- Projective variety 的標準 affine charts：以 projective line 的兩個標準 charts 對照 homogeneous coordinates 與 degree-zero localizations，僅引用正文計算。

## 習題對照

| 來源 | 位置與涵蓋範圍 |
| --- | --- |
| [II.2.14(d)](../../src/sec-2-2/exe.typ) | VS-2；II.2.14(a)–(c) 仍在 PJ。 |
| II.2.15(a)–(b) | VS-1、VS-3；一般 residue-field maps 與 k-rational-point 保留性引用 MG-7。 |
| II.2.15(c) | VS-3 的正文引用入口，不重述 Proposition 2.6。 |
| [II.1.21(a)–(b)](../../src/sec-2-1/exe.typ) | 本篇只提供 classical／scheme 識別；ideal／quotient 的應用主要位置是 CS-4。 |

## 範圍界線

II.3.23 的 varieties product 與 scheme fiber product 比較、一般 open／closed subvariety correspondence 的完整整理、II.2.10–II.2.11 的非代數閉域與有限域計算，均暫列 TODO。這些不因新增本篇就被標為已涵蓋。CS-4 所需的 closed-subvariety 識別只作其特定應用，不擴充成完整專題。

先備：II.2 正文、XP 的 generic points；需要 projective identification 時引用 PJ 的 chart 入口。與 CS 的關係是 VS 提供 classical／scheme 識別，CS 提供 ideal／closed-subscheme 工具，兩篇不互相依賴彼此的應用部分。
