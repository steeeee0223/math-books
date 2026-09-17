# MG — Morphisms, diagonals and graphs

> 設計紀錄：保存選題、分工與條件；現行敘述與證明見 [morphisms.typ](../../src/sup/morphisms.typ)，教材分工見 [總覽](README.md)。

定位：使用正文的 fiber products 推導可重用結果，不另發展 category theory。

## 正文參照：只連結

- [II.3, D10、Theorem 3.3](../../src/sec-2-3/part-1.typ)：fiber product universal property 與存在性。
- [II.4, D1、Proposition 4.1、Corollary 4.2](../../src/sec-2-4/part-1.typ)：diagonal、separatedness 與 affine 情形。
- II.4, Corollaries 4.6、4.8 的 stability statements；既有 [local-props](../../src/sup/local-props.typ) 的 base change／locality profiles。

## 內容範圍

| 標記 | 內容 | 限定與用途 |
| --- | --- | --- |
| MG-1 | Affine calculation 的參照入口 | Spec B ×_{Spec A} Spec C 對應 B ⊗_A C；目前正文只列存在定理，若正式內容仍缺公式，僅補這個計算 lemma，不重寫 universal property。 |
| MG-2 | Fibres 與 residue fields | 由 base change 定義 fibre，計算 affine fibre ring；區分 set-theoretic fibre 與 scheme structure。 |
| MG-3 | Graph 是 diagonal 的 base change | 對 S-morphism X → Y，Y/S separated 推得 graph X → X ×_S Y 是 closed immersion。 |
| MG-4 | Dense-open uniqueness | Reduced X、separated Y/S 下，兩個 S-morphisms 在 dense open 相等便相等。 |
| MG-5 | Affine intersections | X separated over affine S 時，兩個 affine opens 的交集 affine。 |
| MG-6 | Graph factorization 的 property calculus | P 包含 closed immersions 且對 composition、base change 穩定時，推導 products、separated cancellation 與 reduction 相容；引用已有 P 的實例。 |
| MG-7 | Field-valued points 與 residue-field maps | Hom(Spec K,X) 對應點 x 與 κ(x)→K；k-morphisms 保留 k-rational points。配合 XP 的 closed-point 判準，不發展 tangent spaces。II.2.7 的主要位置在此；II.2.15 的 variety-specific 識別與正文 fully faithfulness 引用統一由 [VS](13-varieties-schemes.md) 整理。 |
| MG-8 | Finite、quasi-finite、closed 與 proper 的區別 | Finite morphisms 的 finite fibres、closedness 與 properness；composition／base change 的代數性質與 locality 只引用已有結果。加入 surjective finite-type quasi-finite 但非 finite 的例子。II.3.5、II.4.1。 |
| MG-9 | Closed subschemes 與 scheme-theoretic image 的应用 | II.3.11(a)–(c) 統一引用 [CS](12-closed-subschemes.md) 的入口；維持已安排的 quasi-compact f 的 image ideal ker(O_Y→f_*O_X)、其 quasi-coherence 與 open restriction 相容性。一般 f 的完整 image existence 暫不列為已涵蓋。 |
| MG-10 | Proper subscheme 的 image | 在 II.4.4 的 Noetherian／separated finite-type 假設下，利用 MG-3、MG-9 與正文 properness 性質得到 scheme-theoretic image 的 properness；不只列 graph factorization 作先備。 |

MG-8 的反例選擇 A^1_k ⊔ G_m → A^1_k：第一分量為 identity、第二分量為 open inclusion。這能同時保留 surjectivity、finite type 與 finite fibres，並顯示不 finite。

MG-6 另列 II.3.13 的具體應用索引：closed／quasi-compact open immersions 的 finite type、composition／base change／products，以及在 f quasi-compact、g∘f finite type 時 f finite type 的取消判準。最後一項不以 MG-6 的「g separated」版本偷換，而引用 local-props 的 affine ring-map finite-generation 工具；Noetherian 結論交由 XP-7。

MG-9 的限制是教材內容的一部分：quasi-compact f 的 scheme-theoretic image 可按 kernel 計算並與 open restriction 相容；不能把同一計算無條件套到任意 f。條件對照：[Stacks, Scheme theoretic image](https://stacks.math.columbia.edu/tag/01R5)。

## 例子與反例

- A^1_k ×_k A^1_k 的 points 不等於兩個 point sets 的 ordinary product；選擇不同 primes over 同一對 generic points 示範。
- char(k) ≠ 2、k algebraically closed 時，s=t² 的 family：一般 closed fibre、nonreduced special fibre、generic fibre。寫明 characteristic 條件。
- Doubled origin：非 separated target 導致 dense-open uniqueness 失敗；主要引用既有 local-props 的例子。
- 將兩份 A^2_k 沿 A^2_k\{0} glue：兩個 affine charts 的交集非 affine，補 II.4.3 的反例。Doubled affine line 的交集是 G_m，不能代替這個反例。
- X = Spec(k[ε]/ε²)、Y=A^1_k，t ↦ 0 與 t ↦ ε：底層點映射相同而 scheme morphisms 不同，區分 setwise equality 與 morphism equality。
- 非 reduced source 的 dense-open 反例使用 X=Spec(k[t,ε]/(ε²,tε))，t-coordinate 對應的兩個 A^1-maps由 0、ε 給定；在 dense D(t) 相等。

## 習題對照

[II.3 exercises](../../src/sec-2-3/exe.typ)：3.9–3.10；[II.4 exercises](../../src/sec-2-4/exe.typ)：4.2–4.4、4.8。4.9 的 Segre／projective 部分放 PJ。Valuative criteria 與 Chow's lemma 不在本篇展開。

新增對照：II.2.7 → MG-7，II.2.15 → VS；II.3.5、II.4.1 → MG-8；II.3.11(a)–(c) → CS，(d) 僅先納入 MG-9 的 quasi-compact 版本；II.3.13 → MG-6 與 XP-7。II.3.9(b) 的 Spec k(s) ×_k Spec k(t) 作 MG-1 的 localization 計算例子。II.3.23 的 varieties／schemes product comparison 列在 VS 的後續範圍；MG 僅提供 fiber-product 工具，不標為完整涵蓋。
