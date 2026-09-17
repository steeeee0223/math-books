# SC — Sheaf constructions and exactness

> 設計紀錄：保存選題、分工與條件；現行敘述與證明見 [sheaf-constructions.typ](../../src/sup/sheaf-constructions.typ)，教材分工見 [總覽](README.md)。

定位：所有共用 sheaf constructions 的主要位置。先讀 CAT、SL；modules 部分另需 [II.5 的 O-modules 定義](../../src/sec-2-5/part-1.typ)及 AL 的相關代數工具。

## 值域與適用範圍

| Construction | Abelian groups | Commutative unital rings | O-modules |
| --- | --- | --- | --- |
| Small limits／products | 逐 open 計算 | 逐 open 計算 | 逐 open 在 O(U)-modules 中計算 |
| Small colimits／coproducts | Presheaf colimit 後 sheafify | 在 rings 中取 presheaf colimit 後 sheafify | 在 modules 中取 presheaf colimit 後 sheafify |
| Sheaf Hom | Abelian-group-valued | Set-valued，使用 ring homomorphisms | O-module-valued，使用 O-linear morphisms |
| Kernel／cokernel／exact sequence | Abelian-category 意義 | 不套用 abelian-category 的語言 | Abelian-category 意義 |
| Ideal、quotient ring sheaf | 不適用 | 以 ideal sheaf 作 quotient，必要時 sheafify | 與 module quotient 分別標示 |
| Tensor／symmetric／exterior operations | 需要時視為 Z-modules | Tensor of algebras 有其代數 universal property | 由 AL 的 operations 逐 open 建立後 sheafify |

Rings 的 ring-hom image 是 subring sheaf；kernel 作為 ideal sheaf 處理，不把它當作含同一單位的 subring。Surjective 在本篇指 underlying stalk maps 滿射／sections 局部可提升，不默認等同 ring-sheaf category 的 epimorphism。

## 擬新增命題群

1. **SC-1 — Limits 與 colimits。** 給出上述建構的 universal properties。Limits 的 restriction maps、colimits 的 canonical maps 必須明列。引用正文 sheafification，不再重述其定義。
2. **SC-2 — Stalk comparison。** Stalks 與 filtered colimits 及 finite limits 的交換；一般 colimits 可由局部代表元與 universal properties 處理。標明此處只涉及上表的具體代數範疇；finite limits 不升格為 arbitrary limits。
3. **SC-3 — Direct sum of abelian-group sheaves。** 有限 direct sum 是 biproduct；無限 direct sum 是 presheaf direct sum 的 sheafification，sections 局部只有有限多個非零分量。這一命題的標題與敘述明標 abelian groups；O-modules 使用同一底層建構並另加 scalar action，不重證。
4. **SC-4 — Exactness calculus。** 將正文 kernel／image／cokernel 定義集中連結；新增 stalkwise exactness、surjectivity 的 local lifting criterion、first isomorphism theorem 與 short exact sequence 的 quotient 描述。僅限 abelian groups／modules。
5. **SC-5 — Sheaf Hom。** U ↦ Hom(F|U,G|U) 的 sheaf property、global sections 與 morphisms 的識別、restriction compatibility。一般 stalk Hom 比較不聲稱是同構；有限呈示情形見 AL、QC。
6. **SC-6 — Direct／inverse image 與 adjunction。** 引用正文定義，新增 f^{-1} ⊣ f_*、unit／counit、composition compatibility。Abelian groups 上 f^{-1} exact、f_* left exact；ringed spaces 上明確區分 f^{-1} 與 f^*。
7. **SC-7 — Module tensor 與 pullback。** Module tensor sheaf、tensor–Hom adjunction、f^* ⊣ f_*、pullback 與 tensor／symmetric／exterior operations 相容。f^* 一般 right exact；flatness 才提供 exactness。若正文已有建構，只設參照入口。
8. **SC-8 — Sections 與 filtered colimits。** Noetherian topological space 上的交換命題，明列每個 open quasi-compact 如何進入假設；一般空間不無條件交換。
9. **SC-9 — Constant 與 skyscraper sheaves。** Constant presheaf 的 sheafification 與 locally constant sections 的識別；點包含 i_P:{P}→X 的 direct image、其在 closure({P}) 上的 stalks，以及由該閉包上 constant sheaf pushforward 得到的識別。以 abelian groups 為主，引用 SL 的 sheafification 工具。特別區分 P closed 與非 closed 的情形，供 SC-E1 與 SE 的 support 例子引用。
10. **SC-10 — Finite locally free projection formula。** 對 ringed spaces 的 morphism f:X→Y、O_X-module F 與 finite locally free O_Y-module E，列出 canonical map f_*F ⊗ E → f_*(F ⊗ f^*E) 為同構。此版本不需要 scheme、quasi-coherence 或 properness；有限自由代數與 duality 引用 AL，QC 不另證一遍。

## 必須收錄的反例

### SC-E1：stalks 不與 infinite products 交換

X = N ∪ {∞}，各自然數點 isolated，∞ 的鄰域包含某個 tail。令 F_n 是在 n 的 skyscraper abelian-group sheaf，係數 Z。

- 每個 (F_n)_∞ = 0。
- 比較映射 (∏_n F_n)_∞ → ∏_n (F_n)_∞ 的目標為零。
- 全域 section (1,1,…) 的 germ 在 ∞ 非零，作為比較映射不 injective 的具體 witness。

### SC-E2：同一例子給 inverse-limit 反例

令 G_m = ∏_{n≤m} F_n，以忘掉最後一個分量作 transition maps。比較 (lim_m G_m)_∞ → lim_m (G_m)_∞；前者含 SC-E1 的非零 germ，後者為零。

### SC-E3：sheaf epimorphism 不保證 sections 滿射

引用 II.1.21(c) 的 P^1 與兩點例子，標記全域截面映射 k → k × k 是 diagonal；不重抄原習題證明。

### SC-E4：ring epimorphism 不等於 underlying surjection

單點空間上的 Z → Q 是 unital rings 的 epimorphism，但不是集合上的滿射。這是 SC-4 不套用 rings 的原因之一。

### SC-E5：inverse image 與 module pullback 的 exactness 不同

在單點 ringed spaces 上取 Z → Z/2Z；pullback 將 Z 上的乘 2 單射送成零映射。這裡用 AL 的 tensor 例子，避免再證一次。

## 習題對照與正文索引

[II.1 正文](../../src/sec-2-1/part-1.typ)：D5–D7、Proposition-Definition 1.2 僅引用。

[II.1 exercises](../../src/sec-2-1/exe.typ)：1.2–1.8 → SC-4、SC-6；1.9 → SC-3；1.10–1.12 → SC-1、SC-2、SC-8；1.15 → SC-5；1.18 → SC-6。II.1.21(c) 作 SC-E3 的例子入口。

[II.5 exercises](../../src/sec-2-5/exe.typ)：5.1(c) → SC-7；5.16 的 sheaf operations 與 pullback 相容性 → SC-7，有限自由計算由 AL 提供。

補充對照：II.1.1、1.17 → SC-9；II.5.1(a)–(b) 的 sheaf duality 由 AL-4 配合 SL 的 gluing 得到，II.5.1(d) → SC-10。II.1.16 的 flasque 性質仍留待後續，不能因已有 skyscraper construction 就標為涵蓋。
