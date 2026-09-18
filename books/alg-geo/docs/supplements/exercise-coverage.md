# 第二章習題與補充教材對照

以現行各節的 `exe.typ` 與 `src/sup/*.typ` 為核對來源。II.1–II.5 逐題列出，另含 II.2.A、II.5.3* 兩道補充題；II.6–II.8 只列補充教材已涉及的項目。這是教材內容索引，不是證明或形式驗證完成清單。

## 標示方式

- **收錄**：現行教材已有對應敘述或推導；此標記不判定書面證明或 Lean 驗證是否完整。
- **引用**：主要內容已在正文或 local-props，補充教材只建立應用／查找入口。
- **部分**：只處理部分小題、提供先備，或目前版本的假設較窄；缺少部分列在同一行。
- **後續**：尚未納入補充教材，見 [TODO](TODO.md)。

教材代號與檔案見 [總覽](README.md)；每題的主要位置如下，跨篇時由 construction 所在篇作主要引用，避免重複內容。

## II.1 — Sheaves

來源：[II.1 exercises](../../src/sec-2-1/exe.typ)。

| 題號 | 狀態 | 位置與範圍 |
| --- | --- | --- |
| II.1.1 | 收錄 | SC-10：constant presheaf 的 sheafification。 |
| II.1.2 | 收錄 | SC-2、SC-4：stalks、kernel／image、injectivity／surjectivity／exactness。 |
| II.1.3 | 收錄 | SC-4 的 local lifting；SC-14 的 sections 非滿射例子。 |
| II.1.4 | 收錄 | SL-5、SC-2／SC-4：sheafification 保留 monomorphisms、image subsheaf。 |
| II.1.5 | 收錄 | SC-4 配合正文 II.1.1；只在 abelian groups／modules 使用 mono+epi 判準。 |
| II.1.6 | 收錄 | SC-4：subsheaf quotient 與 short exact sequences。 |
| II.1.7 | 收錄 | SC-4：first isomorphism theorem。 |
| II.1.8 | 收錄 | SC-6：sections left exact；SC-14 提供非 right-exact 例子。 |
| II.1.9 | 收錄 | SC-3：abelian-group finite biproduct。 |
| II.1.10 | 收錄 | SC-1：sheaf colimit construction；CAT 只供 universal-property 語言。 |
| II.1.11 | 收錄 | SC-9：Noetherian space 上 sections 與 directed colimits。 |
| II.1.12 | 收錄 | SC-1：inverse limits；SC-13 補 stalk 不交換的反例。 |
| II.1.13 | 後續 | Espace étalé；SL 的 sheafification 不等於已涵蓋此幾何模型。 |
| II.1.14 | 收錄 | SE-1：section support 與 sheaf support 的差別。 |
| II.1.15 | 收錄 | SC-5：sheaf Hom；SL-3 提供 morphism gluing。 |
| II.1.16 | 後續 | (a)–(e) 的 flasque 理論，保留完整題群。 |
| II.1.17 | 收錄 | SC-10：skyscraper、非閉點的 stalks、closure 上的 constant sheaf。 |
| II.1.18 | 收錄 | SC-6：adjunction、unit／counit；CAT 只供語言。 |
| II.1.19 | 收錄 | SE-5–SE-6：(a)–(c) 的 extension by zero 與 open-closed exact sequence。 |
| II.1.20 | 部分 | SE-3–SE-4 包含 (a)、(b) 的 left-exact sequence，SE-7 提供 affine support torsion；flasque 時的 surjectivity 留待後續。 |
| II.1.21 | 部分 | (a)–(b) 由 CS-6 引用 ideal／quotient 結果，VS 提供語境識別；(c) 為 SC-14；(d)–(e) 的 rational functions／principal parts 留待後續。 |
| II.1.22 | 收錄 | SL-4：gluing sheaves 及 compatible uniqueness。 |

## II.2 — Schemes

來源：[II.2 exercises](../../src/sec-2-2/exe.typ)。

| 題號 | 狀態 | 位置與範圍 |
| --- | --- | --- |
| II.2.1 | 收錄 | XL-1：distinguished open 的 scheme identification；正文 localization 公式只引用。 |
| II.2.2 | 收錄 | XL-1：open subschemes。 |
| II.2.3 | 收錄／引用 | (a) 的 reduced criterion 引用正文；(b)–(c) 在 XP-9。 |
| II.2.4 | 收錄 | XL-2：morphisms into Spec 與 global sections 的自然對應。 |
| II.2.5 | 收錄 | XL-2：Spec Z 的描述與 terminal property；CAT-4 提供範疇語言。 |
| II.2.6 | 收錄 | XL-2：empty scheme 與 initial property；CAT-4 提供範疇語言。 |
| II.2.7 | 收錄 | MG-10：field-valued points；不需另開 residue-field 專題。 |
| II.2.8 | 收錄 | [DF-1](../../src/sup/differentials-tangent-spaces.typ)：固定 k-rational point 的 dual-number morphisms、derivations 與 tangent vectors 的自然對應。 |
| II.2.9 | 收錄 | XP-1：generic points。 |
| II.2.10 | 後續 | Spec R[x] 的完整點集、拓撲與 residue-field 計算。 |
| II.2.11 | 後續 | Finite-field polynomial spectrum 與 residue-field 計數。 |
| II.2.12 | 收錄 | XL-4：gluing schemes、disjoint union。 |
| II.2.13 | 收錄 | XP-10 及其 counterexamples。 |
| II.2.14 | 收錄／引用 | (a)–(c) 在 PJ-1–PJ-4；(d) 在 VS-2 引用正文 Proj charts 與 II.2.6 建立識別。 |
| II.2.15 | 收錄／引用 | VS-1／VS-3 為主要入口；(a)–(b) 引用 MG-10 的一般結果與 closed-point 判準，(c) 引用正文 II.2.6。 |
| II.2.16 | 收錄 | XL-6：global principal opens、清分母與 qcqs 假設。 |
| II.2.17 | 收錄／引用 | (a) 在 XL-5；(b) 在 XL-7 連到 local-props 的 affineness 工具。 |
| II.2.18 | 收錄／引用 | (a) 為 XL principal-open 索引；(b) 在 XL-8、(c)–(d) 在 CS-1；dominance 的條件與反例在 XP-6。 |
| II.2.19 | 收錄 | XP-8：clopen／idempotent／product decomposition。 |
| II.2.A | 引用 | 六個小題分別索引到正文 spectrum 性質、XL principal opens 與 XP；不複製命題。 |

## II.3 — Properties

來源：[II.3 exercises](../../src/sec-2-3/exe.typ)。LP 指既有 [local-props.typ](../../src/sup/local-props.typ)。

| 題號 | 狀態 | 位置與範圍 |
| --- | --- | --- |
| II.3.1 | 引用 | LP 的 finite-type affine communication。 |
| II.3.2 | 引用 | LP 的 quasi-compact target criterion。 |
| II.3.3 | 引用 | LP 加 finite-subcover／affine criteria，列 finite type 與 locally finite type+quasi-compact 的應用。 |
| II.3.4 | 引用 | LP 的 whole-inverse-image finite criterion。 |
| II.3.5 | 收錄 | MG-11：(a) finite fibres／closedness，(b) surjective quasi-finite 非 finite 的例子。 |
| II.3.6 | 收錄 | XP-5：function field 與 generic local ring。 |
| II.3.7 | 部分 | XP-6 提供 dominance／field inclusion；RM-5 已證明 integral separated finite-type k-schemes 的 field extension／整個 inverse image finite 判準，不宣稱涵蓋一般 integral schemes。 |
| II.3.8 | 部分 | BU-10–BU-11 已計算 cusp、node 的 normalization；一般 normalization 的建構與性質仍待補，XP、XL 提供先備。 |
| II.3.9 | 收錄 | MG-1–MG-2：(a) product points，(b) k(s)⊗_k k(t) 的 spectrum。 |
| II.3.10 | 收錄 | MG-3–MG-4：fiber topology 與 closed／generic fiber 計算，標明 characteristic。 |
| II.3.11 | 部分 | (a)–(c) 由 CS-1–CS-4 統一引用 LP、正文與 XP-9；(d) MG-12 先處理 quasi-compact f，任意 f 的版本留待後續。 |
| II.3.12 | 收錄 | PJ-5：homogeneous quotient 與 ideal truncation。 |
| II.3.13 | 收錄／引用 | MG-9 的 finite-type 應用索引與 LP；最後的 Noetherian 結論在 XP-13。取消判準不得偷加 separated 假設。 |
| II.3.14 | 收錄 | XP-7：closed-point density 及 DVR 反例。 |
| II.3.15 | 後續 | Geometric properties 與 field extension；不由一般 locality 自動推出。 |
| II.3.16 | 收錄 | XP-10：Noetherian induction 工具。 |
| II.3.17 | 部分 | XP-2–XP-4、XP-7 處理 (a)–(d)；(e) 的 t(X) 比較留待後續。 |
| II.3.18 | 後續 | XP 只連結 (b) 的 generic-point 動機，不宣稱完成 constructibility 題群。 |
| II.3.19 | 後續 | Chevalley；MG／XP 的工具不足以直接視為涵蓋。 |
| II.3.20 | 後續 | Dimension formula 題群。 |
| II.3.21 | 後續 | Dimension formula 的 DVR 反例。 |
| II.3.22 | 後續 | Dimension of fibres。 |
| II.3.23 | 部分 | VS 將此題列為後續；MG 與正文 II.2.6 只供先備，完整 product 比較未加入核心。 |

## II.4 — Separated and proper morphisms

來源：[II.4 exercises](../../src/sec-2-4/exe.typ)。

| 題號 | 狀態 | 位置與範圍 |
| --- | --- | --- |
| II.4.1 | 收錄 | MG-11：finite implies proper，引用正文 proper 定義與 finite-map 工具。 |
| II.4.2 | 收錄 | MG-6–MG-7：dense-open uniqueness 與兩類反例；LP-63 提供 schematically dense 版本。 |
| II.4.3 | 收錄 | MG-8：affine intersections，另加 nonseparated 的非 affine overlap 例子。 |
| II.4.4 | 收錄 | MG-13：proper subscheme image；MG-5、MG-12 提供 graph 與 image。 |
| II.4.5 | 後續 | Valuations 的 centers；generic-point 教材只提供先備。 |
| II.4.6 | 後續 | Proper affine variety morphism 的 finiteness；MG-11 不涵蓋此逆向結果。 |
| II.4.7 | 後續 | Real forms／field descent，不與 open-cover gluing 混用。 |
| II.4.8 | 收錄 | MG-9：property calculus。 |
| II.4.9 | 收錄 | PJ-10–PJ-11，並引用 MG-9 的 property calculus。 |
| II.4.10 | 後續 | Chow's lemma。 |
| II.4.11 | 後續 | DVR dominance 與 valuative criteria。 |
| II.4.12 | 後續 | Curves／surfaces 上 valuation examples。 |

## II.5 — Sheaves of modules

來源：[II.5 exercises](../../src/sec-2-5/exe.typ)。

| 題號 | 狀態 | 位置與範圍 |
| --- | --- | --- |
| II.5.1 | 收錄 | (a)–(b)、(d) SC-11 的 duality 與 finite locally free projection formula；(c) SC-7 的 tensor–Hom adjunction。 |
| II.5.2 | 收錄 | QC-9：DVR 的兩點模型與 quasi-coherence 判準。 |
| II.5.3 | 收錄 | QC-1 的 tilde–Γ adjunction；不與 SC-8 的 f^*–f_* 混同。 |
| II.5.4 | 收錄 | QC-7：local presentation。 |
| II.5.5 | 收錄／引用 | (a) QC-13；(b) finite-map 判準；(c) QC-5／QC-6 的 finite pushforward 應用。 |
| II.5.6 | 收錄 | (a)–(c) SE-1／SE-2；(d)–(e) SE-7，明列 support subsheaf 的 QCoh／Coh 保留性。 |
| II.5.7 | 收錄 | (a)–(b) SE-10；(c) AL-11+SE-12 的 tensor-invertibility 判準。 |
| II.5.8 | 收錄 | SE-11 與 nonreduced counterexample。 |
| II.5.9 | 部分 | PJ-6 的 (a)–(b) 與具體 high-degree comparisons；(c) 完整 equivalence 未收錄。 |
| II.5.10 | 收錄 | PJ-7–PJ-8：saturation 與 ideal sheaves，保持 polynomial／Noetherian 假設。 |
| II.5.11 | 收錄 | PJ-10：Segre algebra、product identification 與 O(1) comparison。 |
| II.5.12 | 收錄 | PJ-11：兩個 very-ampleness 結論，保持相對 base 條件。 |
| II.5.13 | 收錄 | PJ-9：Veronese 與 twisting comparison。 |
| II.5.14 | 收錄 | PJ-12：projective normality；connected normal→integral 使用 XP 及其 Noetherian／非空條件。 |
| II.5.15 | 收錄 | SE-8–SE-9：coherent extension／approximation。 |
| II.5.16 | 收錄 | AL-6–AL-9：代數 operations、rank／pairing／filtrations；SC-7–SC-8：sheafification 與 pullback。 |
| II.5.17 | 收錄／引用 | (a) 引用 LP；(b)–(d) RV-1–RV-4。 |
| II.5.18 | 收錄 | RV-6–RV-8，保留 V(E) 的 dual convention。 |
| II.5.3* | 收錄 | PJ-6 的 graded adjunction，以正文 degree-one generation 假設為範圍。 |

## 涵蓋界限

對 II.3.11(d)，quasi-compact 版本的 kernel／open-restriction 條件另參照 [Stacks, Scheme theoretic image](https://stacks.math.columbia.edu/tag/01R5)。表中的「部分」保留較強假設或只涵蓋小題的界限，不表示原題的所有情形都已有證明。

## II.6–II.8 — 已涉及的習題

來源：[II.6](../../src/sec-2-6/exe.typ)、[II.7](../../src/sec-2-7/exe.typ)、[II.8](../../src/sec-2-8/exe.typ)。下表只列已涉及的項目，其餘題目不因相關教材存在而視為完成。形式驗證缺口見 [驗證狀態](verification-status.md)。

| 題號 | 狀態 | 實際位置與仍缺範圍 |
| --- | --- | --- |
| II.6.1 | 部分 | DV-16 計算 P¹×P¹ 的 Pic／Cl；一般 X×Pⁿ 未證明。 |
| II.6.5 | 部分 | DV-15 計算 affine quadric surface 的 Cl=Z/2；DV-16 處理 projective quadric surface。高維 quadric 與 Klein theorem 未納入。 |
| II.7.5 | 部分 | PM-4 使用 very ample 與 globally generated tensor 的建構，證明 very ample differences；不宣稱涵蓋所有五項。 |
| II.7.10 | 部分 | PJ2-6–PJ2-7 處理 P(E)、twisting、quotient section 與 transitions；任意 projective-space bundle 的 converse classification 未證明。 |
| II.7.11 | 部分 | BU-2 與 PJ2 的 Veronese／twisting 提供先備；一般 center-support 強化未證明，未標成整題解答。 |
| II.7.13 | 收錄 | LP-57 完整寫出 nodal gluing、Pic(C×A¹)／Pic(C×Gₘ)、overlap action 及 degree obstruction；其 Picard 分類尚未完整形式驗證。 |
| II.8.1 | 部分 | DF-3 的 residue term 與 finite-separable closed-point 比較；LP2 補 smooth locus 的判準。任意點的所有 rank assertions 未視為已完成。 |
| II.8.4 | 部分 | DF-13–DF-14 提供 determinant adjunction 與 smooth hypersurface formula；不納入 projective-normality、Bertini construction 或 genus formulas。 |
| II.8.5 | 部分 | BU-8 是 exceptional geometry 先備；blowup 的 global Picard 與 canonical formulas 仍是本題要求，未在補充教材證明。 |
| II.8.6 | 收錄 | LP2-2–LP2-3 與 DF-1 給 affine lifting／derivation framework；純代數定理明確留由讀者證明，不以此宣稱已逐行形式驗證原題。 |
