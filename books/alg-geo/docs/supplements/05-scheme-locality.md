# XL — Scheme locality and gluing

> 設計紀錄：保存選題、分工與條件；現行敘述與證明見 [scheme-locality.typ](../../src/sup/scheme-locality.typ)，教材分工見 [總覽](README.md)。

定位：每次「縮到 affine」時可直接引用的工具。XL-1–7 先備 SL 與 II.2，並供 II.3 前閱讀 LP-1–15 使用；XL-8 的證明另需 II.5.2。

## 正文參照：只連結

- [II.2, Proposition 2.2、2.3 與 D2–D3](../../src/sec-2-2/part-1.typ)：structure sheaf、Spec 的 functoriality、locally ringed spaces、schemes。
- [II.3, Proposition 3.2](../../src/sec-2-3/part-1.typ)：locally Noetherian 的 affine criterion。
- [local-props.typ](../../src/sup/local-props.typ)：simultaneous distinguished neighborhoods、affine communication、source／target locality、whole-inverse-image criterion。本文不重證其命題。

## 內容範圍

| 標記 | 內容 | 查找用途 |
| --- | --- | --- |
| XL-1 | Distinguished open 作 open subscheme、任意 open subscheme | 由正文 localization 公式連到實際 open immersion；II.2.1–2.2。 |
| XL-2 | Morphisms into an affine scheme | Hom(X,Spec A) 與 Hom(A,Γ(X,O_X)) 的自然對應；II.2.4。 |
| XL-3 | Gluing scheme morphisms | 先 glue continuous maps，再用 SL glue structure-sheaf maps；locally ringed 條件在 stalks 上檢查。 |
| XL-4 | Gluing schemes | 記錄 underlying topological gluing、ring-sheaf gluing、stalk 的 local-ring 性質、affine charts；涵蓋 disjoint union。 |
| XL-5 | Isomorphism 的 target-cover criterion | 若每個 f^{-1}(V_i) → V_i 是 isomorphism，則 f 是 isomorphism；不能只檢查一組無相容關係的局部同構。 |
| XL-6 | Global principal opens X_f 與清分母 | Quasi-compact X 上的 vanishing after a power；quasi-compact quasi-separated X 上 Γ(X,O_X)_f → Γ(X_f,O_X) 的比較。 |
| XL-7 | Affineness criterion 的使用入口 | 完整的 unit-ideal criterion 證明留在本篇 II.2.17(b)；LP-13 引用此證明，LP-47 再套用 LP-13。 |
| XL-8 | Affine ring maps 的幾何判準 | A→B injective iff O_{Spec A}→f_*O_{Spec B} injective；Surjectivity／closed immersion 的判準統一引用 [CS-1](12-closed-subschemes.md)。Injectivity 部分引用正文 Spec functoriality 與 affine pushforward 公式，不重建這些工具。Dominance 的相關判準連到 XP。 |

XL-8 可分階段閱讀：II.2 時先讀結論與 structure-sheaf 版本；需要一般 module 計算時再連到 II.5。另設 principal-open 查找表，將 II.2.A 的 nilpotent／unit／zero-ring、radical ideals、quasi-compactness、closed points 六項分別連到正文 II.2.1–II.2.2、XP 與本篇既有結果；不另開重複命題。

## 邊界與例子

- Affine charts 的交集不是自動 affine；引用 MG 的 separatedness 判準。
- X_f 必須由 global section 定義；不要把只在某個 chart 上的函數直接視為 global section。
- 「locally an isomorphism on the source」不足以給 global isomorphism：兩份非空 scheme 的 disjoint union 映到同一份 scheme。
- Gluing 兩條 affine lines 沿 punctured lines 得到 doubled origin；非 separated 的計算集中於 XP-5，LP-52 引用它說明 GSS 失敗。

## 習題對照

[II.2 exercises](../../src/sec-2-2/exe.typ)：2.1–2.2、2.4、2.12、2.16–2.17。2.5–2.6 作为 CAT 的 initial／terminal 例子，在本篇提供 scheme 層的引用位置。

XL-6 的 module／invertible-sheaf 版本由 SE 連結正文 II.5.14，不另寫第二份清分母建構。

新增對照：II.2.18(b) → XL-8（dominance 部分見 XP），(c)–(d) → CS-1；II.2.18(a)、補充題 II.2.A → principal-open 查找表。II.3.1–3.4 的 affine-local criteria 直接連到既有 local-props，不在 XL 重述。
