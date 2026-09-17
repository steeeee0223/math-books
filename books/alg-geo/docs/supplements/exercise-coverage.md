# II.1–II.5 習題涵蓋檢查

以 repository 中五節的 `exe.typ` 為核對來源，共 94 道編號習題，另有 II.2.A、II.5.3* 兩道補充題。這是教材內容分工的索引，不是證明完成清單，也不是原書逐字校勘。

## 標示方式

- **安排**：已有指定教材位置；此標記不判定書面證明或 Lean 驗證是否完整。
- **引用**：主要內容已在正文或 local-props，補充教材只建立應用／查找入口。
- **部分**：只處理部分小題、提供先備，或目前版本的假設較窄；缺少部分列在同一行。
- **後續**：仍放 TODO，不為提高覆蓋率而擴大核心教材。

教材代號與檔案見 [總覽](README.md)；每題的主要位置如下，跨篇時由 construction 所在篇作主要引用，避免重複內容。

## II.1 — Sheaves

來源：[II.1 exercises](../../src/sec-2-1/exe.typ)。

| 題號 | 狀態 | 位置與範圍 |
| --- | --- | --- |
| II.1.1 | 安排 | SC-9：constant presheaf 的 sheafification；新增明確對照。 |
| II.1.2 | 安排 | SC-2、SC-4：stalks、kernel／image、injectivity／surjectivity／exactness。 |
| II.1.3 | 安排 | SC-4 的 local lifting；SC-E3 的 sections 非滿射例子。 |
| II.1.4 | 安排 | SL-6、SC-2／SC-4：sheafification 保留 monomorphisms、image subsheaf。 |
| II.1.5 | 安排 | SC-4 配合正文 II.1.1；只在 abelian groups／modules 使用 mono+epi 判準。 |
| II.1.6 | 安排 | SC-4：subsheaf quotient 與 short exact sequences。 |
| II.1.7 | 安排 | SC-4：first isomorphism theorem。 |
| II.1.8 | 安排 | SC-6：sections left exact；SC-E3 提供非 right-exact 例子。 |
| II.1.9 | 安排 | SC-3：abelian-group finite biproduct。 |
| II.1.10 | 安排 | SC-1：sheaf colimit construction；CAT 只供 universal-property 語言。 |
| II.1.11 | 安排 | SC-8：Noetherian space 上 sections 與 directed colimits。 |
| II.1.12 | 安排 | SC-1：inverse limits；SC-E2 補 stalk 不交換的反例。 |
| II.1.13 | 後續 | Espace étalé；SL 的 sheafification 不等於已涵蓋此幾何模型。 |
| II.1.14 | 安排 | SE-1：section support 與 sheaf support 的差別。 |
| II.1.15 | 安排 | SC-5：sheaf Hom；SL-3 提供 morphism gluing。 |
| II.1.16 | 後續 | (a)–(e) 的 flasque 理論，保留完整題群。 |
| II.1.17 | 安排 | SC-9：skyscraper、非閉點的 stalks、closure 上的 constant sheaf。 |
| II.1.18 | 安排 | SC-6：adjunction、unit／counit；CAT 只供語言。 |
| II.1.19 | 安排 | SE-4：(a)–(c) 的 extension by zero 與 exact sequence。 |
| II.1.20 | 部分 | SE-3、SE-5 包含 (a)、(b) 的 left-exact sequence；flasque 時的 surjectivity 留待後續。 |
| II.1.21 | 部分 | (a)–(b) 由 CS-4 引用 ideal／quotient 結果，VS 提供語境識別；(c) 為 SC-E3；(d)–(e) 的 rational functions／principal parts 留待後續。 |
| II.1.22 | 安排 | SL-4：gluing sheaves 及 compatible uniqueness。 |

## II.2 — Schemes

來源：[II.2 exercises](../../src/sec-2-2/exe.typ)。

| 題號 | 狀態 | 位置與範圍 |
| --- | --- | --- |
| II.2.1 | 安排 | XL-1：distinguished open 的 scheme identification；正文 localization 公式只引用。 |
| II.2.2 | 安排 | XL-1：open subschemes。 |
| II.2.3 | 安排／引用 | (a) 的 reduced criterion 引用正文；(b)–(c) 在 XP-3。 |
| II.2.4 | 安排 | XL-2：morphisms into Spec 與 global sections 的自然對應。 |
| II.2.5 | 安排 | XL／CAT：Spec Z 的描述與 terminal property。 |
| II.2.6 | 安排 | XL／CAT：empty scheme 與 initial property。 |
| II.2.7 | 安排 | MG-7：field-valued points；不需另開 residue-field 專題。 |
| II.2.8 | 後續 | Tangent space 與 dual numbers；MG 的 nilpotent 反例只提供動機。 |
| II.2.9 | 安排 | XP-1a：generic points。 |
| II.2.10 | 後續 | Spec R[x] 的完整點集、拓撲與 residue-field 計算。 |
| II.2.11 | 後續 | Finite-field polynomial spectrum 與 residue-field 計數。 |
| II.2.12 | 安排 | XL-4：gluing schemes、disjoint union。 |
| II.2.13 | 安排 | XP-4 及其 counterexamples。 |
| II.2.14 | 安排／引用 | (a)–(c) 在 PJ-1–PJ-3；(d) 在 VS-2 引用正文 Proj charts 與 II.2.6 建立識別。 |
| II.2.15 | 安排／引用 | VS-1／VS-3 為主要入口；(a)–(b) 引用 MG-7 的一般結果與 closed-point 判準，(c) 引用正文 II.2.6。 |
| II.2.16 | 安排 | XL-6：global principal opens、清分母與 qcqs 假設。 |
| II.2.17 | 安排／引用 | (a) 在 XL-5；(b) 在 XL-7 連到 local-props 的 affineness 工具。 |
| II.2.18 | 安排／引用 | (a) 為 XL principal-open 索引；(b) 在 XL-8、(c)–(d) 在 CS-1；dominance 的條件與反例在 XP-1e。 |
| II.2.19 | 安排 | XP-2：clopen／idempotent／product decomposition。 |
| II.2.A | 引用 | 六個小題分別索引到正文 spectrum 性質、XL principal opens 與 XP；不複製命題。 |

## II.3 — Properties

來源：[II.3 exercises](../../src/sec-2-3/exe.typ)。LP 指既有 [local-props.typ](../../src/sup/local-props.typ)。

| 題號 | 狀態 | 位置與範圍 |
| --- | --- | --- |
| II.3.1 | 引用 | LP 的 finite-type affine communication。 |
| II.3.2 | 引用 | LP 的 quasi-compact target criterion。 |
| II.3.3 | 引用 | LP 加 finite-subcover／affine criteria，列 finite type 與 locally finite type+quasi-compact 的應用。 |
| II.3.4 | 引用 | LP 的 whole-inverse-image finite criterion。 |
| II.3.5 | 安排 | MG-8：(a) finite fibres／closedness，(b) surjective quasi-finite 非 finite 的例子。 |
| II.3.6 | 安排 | XP-1d：function field 與 generic local ring。 |
| II.3.7 | 部分 | XP-1e 提供 dominance／field inclusion；finite extension 與 dense-open finiteness 留待後續。 |
| II.3.8 | 後續 | XP／XL 只提供 normality、generic points、gluing 先備；normalization 本身未安排。 |
| II.3.9 | 安排 | MG-1、例子：(a) product points，(b) k(s)⊗_k k(t) 的 spectrum。 |
| II.3.10 | 安排 | MG-2：fibre topology 與 closed／generic fibre 計算，標明 characteristic。 |
| II.3.11 | 部分 | (a)–(c) 由 CS-1–CS-3 統一引用 LP、正文與 XP-3；(d) MG-9 先處理 quasi-compact f，任意 f 的版本留待後續。 |
| II.3.12 | 安排 | PJ-4：homogeneous quotient 與 ideal truncation。 |
| II.3.13 | 安排／引用 | MG-6 的 finite-type 應用索引與 LP；最後的 Noetherian 結論在 XP-7。取消判準不得偷加 separated 假設。 |
| II.3.14 | 安排 | XP-1f：closed-point density 及 DVR 反例。 |
| II.3.15 | 後續 | Geometric properties 與 field extension；不由一般 locality 自動推出。 |
| II.3.16 | 安排 | XP-4：Noetherian induction 工具。 |
| II.3.17 | 部分 | XP-1b、XP-1c、XP-1f 處理 (a)–(d)；(e) 的 t(X) 比較留待後續。 |
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
| II.4.1 | 安排 | MG-8：finite implies proper，引用正文 proper 定義與 finite-map 工具。 |
| II.4.2 | 安排 | MG-4：dense-open uniqueness 與兩類反例。 |
| II.4.3 | 安排 | MG-5：affine intersections，另加 nonseparated 的非 affine overlap 例子。 |
| II.4.4 | 安排 | MG-10：proper subscheme image；MG-3／MG-9 提供 graph 與 image，不再只標先備。 |
| II.4.5 | 後續 | Valuations 的 centers；generic-point 教材只提供先備。 |
| II.4.6 | 後續 | Proper affine variety morphism 的 finiteness；MG-8 不涵蓋此逆向結果。 |
| II.4.7 | 後續 | Real forms／field descent，不與 open-cover gluing 混用。 |
| II.4.8 | 安排 | MG-6：property calculus。 |
| II.4.9 | 安排 | PJ-8–PJ-9，並引用 MG-6 的 property calculus。 |
| II.4.10 | 後續 | Chow's lemma。 |
| II.4.11 | 後續 | DVR dominance 與 valuative criteria。 |
| II.4.12 | 後續 | Curves／surfaces 上 valuation examples。 |

## II.5 — Sheaves of modules

來源：[II.5 exercises](../../src/sec-2-5/exe.typ)。

| 題號 | 狀態 | 位置與範圍 |
| --- | --- | --- |
| II.5.1 | 安排 | (a)–(b) AL-4+SL；(c) SC-7；(d) SC-10 的 finite locally free projection formula。 |
| II.5.2 | 安排 | QC-M1：DVR 的兩點模型與 quasi-coherence 判準。 |
| II.5.3 | 安排 | QC 的 tilde–Γ adjunction；不與 SC 的 f^*–f_* 混同。 |
| II.5.4 | 安排 | QC-7：local presentation。 |
| II.5.5 | 安排／引用 | (a) QC-E4；(b) finite-map 判準；(c) QC-5／QC-6 的 finite pushforward 應用。 |
| II.5.6 | 安排 | (a)–(c) SE-1／SE-2；(d)–(e) SE-5，明列 support subsheaf 的 QCoh／Coh 保留性。 |
| II.5.7 | 安排 | (a)–(b) SE-8；(c) AL-9+SE-10 的 tensor-invertibility 判準。 |
| II.5.8 | 安排 | SE-9 與 nonreduced counterexample。 |
| II.5.9 | 部分 | PJ-5 的 (a)–(b) 與具體 high-degree comparisons；(c) 完整 equivalence 未安排。 |
| II.5.10 | 安排 | PJ-6，保持 polynomial／Noetherian 假設。 |
| II.5.11 | 安排 | PJ-8：Segre algebra、product identification 與 O(1) comparison。 |
| II.5.12 | 安排 | PJ-9：兩個 very-ampleness 結論，保持相對 base 條件。 |
| II.5.13 | 安排 | PJ-7：Veronese 與 twisting comparison。 |
| II.5.14 | 安排 | PJ-10：projective normality；connected normal→integral 使用 XP 及其 Noetherian／非空條件。 |
| II.5.15 | 安排 | SE-6–SE-7：coherent extension／approximation。 |
| II.5.16 | 安排 | AL-5–AL-7：代數 operations、rank／pairing／filtrations；SC-7：sheafification 與 pullback。 |
| II.5.17 | 安排／引用 | (a) 引用 LP；(b)–(d) RV-1–RV-4。 |
| II.5.18 | 安排 | RV-6–RV-7，保留 V(E) 的 dual convention。 |
| II.5.3* | 安排 | PJ 的 graded adjunction 參照，以正文 degree-one generation 假設為範圍。 |

## 涵蓋界限

對 II.3.11(d)，quasi-compact 版本的 kernel／open-restriction 條件另參照 [Stacks, Scheme theoretic image](https://stacks.math.columbia.edu/tag/01R5)。綱要中的「部分」標示刻意保留，避免用較強假設的版本宣稱涵蓋原题的所有情形。
