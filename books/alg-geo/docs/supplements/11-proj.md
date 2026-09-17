# PJ — Proj and graded modules

> 設計紀錄：保存選題、分工與條件；現行敘述與證明見 [proj.typ](../../src/sup/proj.typ)，教材分工見 [總覽](README.md)。

定位：一個主題入口、兩個閱讀階段。只集中正文以外的 Proj 結果，不按原 exercise 的先後逐題敘述。

## 正文參照：只連結

- [II.2, D4、Proposition 2.5](../../src/sec-2-2/part-1.typ)：Proj、stalks、D_+(f) affine charts。
- [II.5.11–II.5.16](../../src/sec-2-5/part-1.typ)：graded associated sheaf、twists、Γ_*、section extension、reconstruction 與 projective schemes。
- II.5.17–II.5.20：Serre generation、finite-dimensional／finite-module sections 與 projective pushforward 的既有結果。
- [II.4 的 projective morphisms 定義與 Theorem 4.9](../../src/sec-2-4/part-1.typ)。

## Part A：Proj 的幾何與 functoriality

先備 II.2、XL；不依賴尚未閱讀的 II.5 modules。

| 標記 | 擬新增內容 | 條件與界線 |
| --- | --- | --- |
| PJ-1 | Empty Proj criterion | S 非負分次；Proj S 為空 iff S_+ 的每個元素 nilpotent，不等同 S_+ 必有共同 nilpotence exponent。 |
| PJ-2 | Graded map 的定義域 | Degree-preserving S→T 首先給 Proj T \ V(φ(S_+)T) → Proj S；列出成為全域 morphism 的條件。 |
| PJ-3 | High-degree invariance | Graded map 在充分高次為同構時誘導 Proj 同構；沿用 PJ-2 的定義域檢查。 |
| PJ-4 | Homogeneous quotients 與 closed subschemes | Surjective graded map 與 homogeneous ideals 的幾何意義；明列 ideal 的 high-degree truncation 不改變 closed subscheme，對應 II.3.12(b)。 |

## Part B：Graded modules 與 projective geometry

先備 II.5 的 graded sheaves、AL、SC、QC。涉及 standard graded 的結果，明列 S 由有限多個 degree-one elements 在 S_0 上生成；涉及 coherent sheaves 的有限性結果，另列 Noetherian 假設。

| 標記 | 擬新增內容 | 條件與界線 |
| --- | --- | --- |
| PJ-5 | M → Γ_*(tilde M) | 構造 canonical map、high-degree comparison；Noetherian standard graded S、finite graded M 的版本優先。正文 tilde Γ_*F ≅ F 只引用。 |
| PJ-6 | Saturation | S=A[x_0,…,x_r]、A Noetherian；homogeneous ideal 的 saturation、與 ideal sheaf 的對應、同一 closed subscheme 的判準。 |
| PJ-7 | Veronese | Standard graded S、正整數 d；Proj S^(d) 與 Proj S 的同構，以及 O(1)／O(d) 的對照。 |
| PJ-8 | Segre | Standard graded A-algebras S、T；diagonal graded tensor algebra ⊕_n(S_n⊗_A T_n) 的 Proj 與 product，並明列 O(1) 對應 p_1^*O(1)⊗p_2^*O(1)，以支援 II.5.11–II.5.12。 |
| PJ-9 | Very ample tensor products 與 composition | 利用 Segre；明列相對 base 與 projective／immersion 條件，引用正文 very ample 定義。 |
| PJ-10 | Projective normality | Algebraically closed k、normal integral closed subscheme X⊂P^r_k；coordinate ring 與 section ring 的比較、sufficiently high Veronese 的 projective normality。引用 normality 工具；不在此發展一般 normalization。 |

## 例子與反例

- S=k[x_0,x_1] → T=k[t]，x_0、x_1 都映到 0：Proj T 非空，但 PJ-2 的定義域為空。
- k[x_0,x_1] 中 I=(x_0)、J=(x_0²,x_0x_1)：不同 ideals、有相同 saturation，定義相同 closed subscheme。
- S 與 S⊕S/S_+ 的 graded modules 經 tilde 後相同，說明 tilde 忘掉 irrelevant torsion，不能期待 recover 每個 degree。
- Rational normal curve 作 Veronese 的可計算例子；P^1×P^1 的 quadric embedding 作 Segre 例子。
- Γ_* 不自動保留 short exact sequences 的 surjectivity：用 P^1 上兩點的 ideal sequence，觀察 degree zero。

## 習題對照

| 來源 | 教材位置 |
| --- | --- |
| [II.2.14](../../src/sec-2-2/exe.typ) | (a)–(c) 在 PJ-1–PJ-3；(d) 統一引用 [VS-2](13-varieties-schemes.md) |
| [II.3.12](../../src/sec-2-3/exe.typ) | PJ-4，並在 PJ-6 回顧 |
| [II.4.9](../../src/sec-2-4/exe.typ) | PJ-8–PJ-9 |
| [II.5.9–II.5.14](../../src/sec-2-5/exe.typ) | PJ-5–PJ-10 |
| II.5.3* | Graded tilde–Γ_* adjunction 的條件化參照；不重複 SC 的一般 adjunction 語言 |

II.5.9 的「忽略充分低次後的 equivalence」先以具體 natural maps 與 high-degree comparison 表述，不另外引入 quotient-category 工具。Relative Proj、blow-ups 暫不展開。

涵蓋界線：II.5.9(a)–(b) 與 (c) 的部分具體比較可由 PJ-5 提供，但 (c) 的完整 equivalence 不列為已安排完成；II.5.3* 與 II.5.14 也須保留其 degree-one generation／Noetherian／base-field 假設，不以題號範圍代替條件核對。
