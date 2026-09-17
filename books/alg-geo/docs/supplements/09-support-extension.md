# SE — Support, extension and local freeness

> 設計紀錄：保存選題、分工與條件；現行敘述與證明見 [support-extension.typ](../../src/sup/support-extension.typ)，教材分工見 [總覽](README.md)。

定位：從已建立的代數與 sheaf 工具得到幾何控制。Finite presentation、duality、tensor／symmetric／exterior operations 不在此重新定義。

## 先備與正文參照

SC 的 exactness、restriction 與 adjunction；AL 的 localization、finite presentation 與 Nakayama；QC 的 affine dictionary。

[II.5, Lemma 5.14 及 Remark 5.14.1](../../src/sec-2-5/part-1.typ) 已處理 sections 乘以 invertible-sheaf section 的冪後延伸，只提供連結，不另立相同命題。

## 內容範圍

| 標記 | 內容 | 條件／邊界 |
| --- | --- | --- |
| SE-1 | Support of a section、support of a sheaf | 區分兩者；section support closed 不代表 arbitrary sheaf support closed。 |
| SE-2 | Support 與 annihilator 的 affine 對照 | Finite A-module M 的 support 是 V(Ann M)；不對 arbitrary M 宣稱相同結論。 |
| SE-3 | Sections with support | Closed Z 的 support subsheaf 及到 j_*(F|U) 的 kernel 描述；一般只寫 left-exact sequence。 |
| SE-4 | Open／closed inclusions 與 extension by zero | Abelian groups／modules 中的 j_!、i_* 及 stalk formulas；明列 0→j_!(F|U)→F→i_*(F|Z)→0，區分 j_! 與 j_*，不推廣到 unital ring sheaves。 |
| SE-5 | Support torsion 的代數對照 | Noetherian affine 情形，Γ_{V(I)} 對應被某個 I^n 消去的元素；補此 support subsheaf 保留 quasi-coherence／coherence 的結論，對應 II.5.6(e)。 |
| SE-6 | Coherent extension | Noetherian X、open U、coherent F on U 的 extension；若嵌入既定 quasi-coherent G|U，要求 extension 是 G 的 coherent subsheaf。 |
| SE-7 | Quasi-coherent sheaves 的 coherent approximation | Noetherian X 上是 coherent subsheaves 的 directed union；extension 不主張 canonical 或 unique。 |
| SE-8 | Stalk freeness 推到鄰域 | F finitely presented 時，free stalk 給 free neighborhood；使用 AL 的有限呈示工具。 |
| SE-9 | Fibre rank、semicontinuity 與 local freeness | Noetherian X、coherent F；rank function upper semicontinuous。Reduced X 加 locally constant fibre rank 的局部自由判準；局部自由的 rank 在 connected X 上常數。 |
| SE-10 | Tensor-invertible 與 rank-one locally free | Noetherian X 上 coherent F invertible iff 存在 coherent G 使 F⊗G≅O_X；inverse 識別為 F 的 dual。純代數工具放 AL，不在 SE 重建 tensor 或 duality。II.5.7(c)。 |

SE-2 另明列單一 section m 的 support=V(Ann(m))，此處不要求整個 M finitely generated；與整個 module 的 support 公式分開，對應 II.5.6(a)。

## 必須收錄的反例

- Spec Z 上 M = ⊕_{p prime} Z/pZ 的 associated sheaf，其 support 是所有閉點、不含 generic point，並不 closed；同時 Ann(M)=0，顯示 SE-2 的 finite hypothesis 不能直接刪除。原先的 tilde Q 例子不成立：其所有 stalks 都是 Q，support 是整個 Spec Z。
- X=Spec(k[ε]/ε²) 上 F=tilde k：fibre rank 恆為 1，但 F 不 locally free，顯示 SE-9 的 reducedness 有作用。
- j:(0,1) → R 與 constant Z sheaf：j_* 在邊界可能有非零 stalk，而 j_! 的邊界 stalk 是零。
- 同一 coherent sheaf 在 open 上可以有不同 extensions；用 P^1 上 O(n) 在標準 A^1 的 restrictions 示範。

## 習題對照

[II.1 exercises](../../src/sec-2-1/exe.typ)：1.14、1.19–1.20；[II.5 exercises](../../src/sec-2-5/exe.typ)：5.6–5.8、5.15。Flasque sheaves 對 support sequence 的強化先列 TODO；不在此發展 cohomology。
