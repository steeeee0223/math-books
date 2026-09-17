# AL — Algebraic tools for modules

> 設計紀錄：保存選題、分工與條件；現行敘述與證明見 [module-algebra.typ](../../src/sup/module-algebra.typ)，教材分工見 [總覽](README.md)。

定位：短的共用代數教材。只收 SC、QC、SE、RV 真正會用到的工具；代數操作先在此定義，sheafification 在 SC，scheme 上的條件在 QC／SE。

## 內容範圍

| 標記 | 內容 | 條件 |
| --- | --- | --- |
| AL-1 | Finite generation、finite presentation、finite free／finite projective | 區分 generators 與 relations 的有限性；Noetherian ring 上 finite module 是 finitely presented。 |
| AL-2 | Localization 的 exactness、與 tensor／direct sums／colimits 的相容性 | 指定乘法集合及 canonical maps；已有交換代數參照時只連結。 |
| AL-3 | Hom localization | M finitely presented 時，S^{-1}Hom_A(M,N) → Hom_{S^{-1}A}(S^{-1}M,S^{-1}N) 是同構；不把此結論推廣到 arbitrary M。 |
| AL-4 | Tensor–Hom adjunction、dual、evaluation | M finite projective 時的 double-dual 與 M^∨ ⊗ N → Hom(M,N) 同構。 |
| AL-5 | Tensor、symmetric、exterior algebras／powers | Universal properties、base-change compatibility；不把對稱／外冪當作一般 exact functors。 |
| AL-6 | 有限自由 rank 計算與 determinant pairing | Exterior pairing 的 perfectness 以 finite free／finite projective 的條件表述。 |
| AL-7 | Exact sequence 所誘導的 symmetric／exterior filtrations | 以 locally split、finite-projective quotient 的情形為主，不無條件宣稱對所有短正合列成立。 |
| AL-8 | Nakayama 與有限呈示資料的 localization | 為 SE 的 lifting generators、spreading freeness 提供代數終點。 |
| AL-9 | Tensor-invertible modules 的有限秩判準 | 在 Noetherian local ring 上，finite modules M、N 若 M⊗N≅A，則兩者為 rank-one free；為 SE-10 提供純代數工具。 |

## 必須收錄的反例

- **AL-E1：tensor 不保留 monomorphisms。** 乘 2 的 Z → Z，tensor Z/2Z 後不再 injective。
- **AL-E2：localization 不與 infinite products 交換。** 比較 (∏_{n≥0} Z)[1/2] → ∏_{n≥0} Z[1/2]；(2^{-n})_n 是沒有共同有界分母的 witness。
- **AL-E3：Hom localization 的有限性必要。** M = ⊕_{n≥0} Z、N = Z、S = {2^r}；以 Hom(M,N) = ∏ Z 將失敗化約為 AL-E2。
- **AL-E4：double dual 需要假設。** Z-module Z/2Z 的 Z-dual 為零，因此 evaluation 到 double dual 不是同構。

## 使用與分工

SC 建立 corresponding sheaf operations 時只引用 AL 的 universal properties。QC 負責 AL-3 的 sheaf 比較與 quasi-coherence；SE 負責 finite presentation／local freeness 的鄰域結論；RV 不重寫 AL-4–AL-6。

[II.5 exercises](../../src/sec-2-5/exe.typ)：5.1(a)–(c)、5.7–5.8、5.16 的代數部分。這不是完整的 finite projective modules 或 commutative algebra 教科書。
