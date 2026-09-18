# 代數幾何補充教材

本目錄維護現行教材的索引、習題分工與未完成工作。數學敘述、證明、例子及閱讀路徑以 [正式教材入口](../../src/sup/sup.typ) 為準，已由 [主書](../../src/main.typ) 納入。

- [習題對照](exercise-coverage.md)：逐題列出教材位置、適用條件與尚缺範圍。
- [後續範圍](TODO.md)：尚未納入的內容及編輯範圍。
- [形式驗證狀態](verification-status.md)：Lean companions 的覆蓋範圍、缺口與檢查方式。

已落實的逐篇設計稿不再另行維護。選材與設計沿革可查 Git 歷史；現行編號與來源註記直接查閱各篇 Typst。

## 教材索引

下表依 `sup.typ` 的收錄次序排列。編號涵蓋定義、結果、例子與 remarks，不代表全部都是已完整驗證的定理。

| 代號與編號 | 正式教材 | 主要內容 |
| --- | --- | --- |
| CAT-1–CAT-10 | [Categorical language](../../src/sup/categorical-language.typ) | Natural transformations、universal properties、limits、colimits、adjunctions。 |
| SL-1–SL-5 | [Sheaf locality and gluing](../../src/sup/sheaf-locality.typ) | Open covers、bases、stalks 與 sheaf gluing。 |
| SC-1–SC-16 | [Sheaf constructions and exactness](../../src/sup/sheaf-constructions.typ) | Sheaf operations、exactness、adjunctions 及不交換的反例。 |
| AL-1–AL-15 | [Algebraic tools for modules](../../src/sup/module-algebra.typ) | Finite presentation、localization、tensor、duality、symmetric 與 exterior powers。 |
| XL-1–XL-8 | [Scheme locality and gluing](../../src/sup/scheme-locality.typ) | Morphisms into affine schemes、scheme gluing、principal opens 與 affineness criterion。 |
| LP-1–LP-65 | [A Locality Calculus for Morphisms](../../src/sup/local-props.typ) | Ring-local conditions、affine communication、morphism locality、projectivity、dominance 與 dense opens。 |
| XP-1–XP-21 | [Topology and intrinsic properties of schemes](../../src/sup/scheme-properties.typ) | Generic points、reduction、normality、Noetherianity 與反例。 |
| MG-1–MG-13 | [Morphisms, diagonals and graphs](../../src/sup/morphisms.typ) | Fiber products、graphs、finite maps 與 quasi-compact scheme-theoretic images。 |
| QC-1–QC-14 | [Quasi-coherent and coherent operations](../../src/sup/quasi-coherent.typ) | Affine dictionary、Hom、pushforward 與有限性條件。 |
| SE-1–SE-16 | [Support, extension and local freeness](../../src/sup/support-extension.typ) | Support、extension by zero、coherent extension、fiber rank 與 local freeness。 |
| RV-1–RV-9 | [Relative Spec and vector bundles](../../src/sup/relative-spec.typ) | Relative Spec、modules、base change 與 vector bundles。 |
| PJ-1–PJ-13 | [Proj and graded modules](../../src/sup/proj.typ) | Graded maps、high-degree comparison、saturation、Veronese、Segre 與 projective normality。 |
| CS-1–CS-6 | [Closed subschemes and ideal sheaves](../../src/sup/closed-subschemes.typ) | Affine quotients、ideal pullback、reduced structures 與 classical vanishing ideals。 |
| VS-1–VS-3 | [Varieties and schemes](../../src/sup/varieties-schemes.typ) | Classical points、Spec／Proj 識別與 regular maps。 |
| AL2-1–AL2-13 | [Associated points and regular sequences](../../src/sup/module-algebra-2.typ) | Associated primes、embedded points、total quotients、depth、conormal algebra 與 Koszul complex。 |
| DV-1–DV-16 | [Divisors and line bundles](../../src/sup/divisors-line-bundles.typ) | Local equations、rational sections、Cartier classes、degree 與具體計算。 |
| PJ2-1–PJ2-10 | [Relative Proj and projectivization](../../src/sup/proj-2.typ) | Quotient description、relations、base change、twists、weighted gradings 與 fibers。 |
| PM-1–PM-9 | [Projective morphisms and positivity](../../src/sup/projective-morphisms.typ) | Global embeddings、relative positivity、finite maps、ruled surfaces 與有限投影。 |
| RM-1–RM-10 | [Rational maps of schemes](../../src/sup/rational-maps.typ) | Representatives、composition、function fields、graph closure 與 extension。 |
| BU-1–BU-13 | [Blowups and birational constructions](../../src/sup/blowups.typ) | Rees algebra、saturated charts、transforms、regular centers 與 base points。 |
| DF-1–DF-15 | [Differentials and Tangent Geometry](../../src/sup/differentials-tangent-spaces.typ) | Tangent vectors、residue fields、Jacobian、conormal、normal 與 canonical bundles。 |
| LP2-1–LP2-12 | [Further Locality Criteria](../../src/sup/local-props-2.typ) | Smooth／étale／unramified、Cartier／regular immersion 與固定 line bundle 的 relative ampleness。 |
| VS2-1–VS2-10 | [Calculations on varieties](../../src/sup/varieties-schemes-2.typ) | Divisors、weighted Proj、pencils、singularities 與退化 conic family 的綜合案例。 |

收錄次序與編號可從 repository root 核對：

```sh
rg '^#include ' books/alg-geo/src/sup/sup.typ
rg 'number: "(CAT|SL|SC|AL|XL|LP|XP|MG|QC|SE|RV|PJ|CS|VS|AL2|DV|PJ2|PM|RM|BU|DF|LP2|VS2)-' books/alg-geo/src/sup/*.typ
```

## 閱讀與內容分工

[教材 roadmap](../../src/sup/sup.typ) 依 II.1–II.8 列出分段閱讀路徑；各篇開頭補充先備與回讀時機。實體收錄次序不等於閱讀依賴，不要求先讀完一整篇才能使用其中一段。

| 共用內容 | 主要位置與分工 |
| --- | --- |
| 一般 sheaf operations 與純代數工具 | SC 維護 sheaf constructions；AL 維護 module algebra；AL2 維護 associated primes 與 regular sequences。 |
| Affineness 的 unit-ideal criterion | XL-7 保存 II.2.17(b) 的證明；LP-13 引用它，LP-46 再套用 LP-13。 |
| Affine closed-immersion dictionary | CS-1 維護 quotient dictionary；LP-33 處理 locality，MG、QC、PJ 引用它。 |
| Projectivity 的 locality 與反例 | LP-54–LP-58；取得全域 embedding 的定理在 PM。 |
| Dominance、dense-open restriction 與 Hartogs | LP-59–LP-64；RM 維護 rational-map constructions，DV 使用 meromorphic extension。 |
| 新的 locality criteria | LP2；relative Proj、Rees algebra 與 Ω 的 base-change 比較分別留在 PJ2、BU、DF。 |
| 共用案例 | DV、PJ2、PM、RM、BU、DF 維護各自計算；VS2 串接它們，並維護 VS2-10 的完整 conic family。 |

LP 的 ring-level base change 只需 tensor product，scheme-level base change 才需 II.3 的 fiber products。LP-27 的 integral source gluing 另用「integral iff affine and universally closed」，LP-23 再引用它。Flat 與 faithfully flat 案例也需要相應的 module criteria，不能將整篇 LP 都視為只有 II.2 的先備。

## 編輯與引用慣例

- 每個 construction 或證明維護一個主要位置；正文已有結果改用引用，習題入口與補充教材維護雙向連結。
- 文件使用中文；正式教材使用英文並沿用 [defs.typ](../../src/defs.typ) 的記號。證明編輯依 [ag-proof](../../../../.agents/skills/ag-proof/SKILL.md)。
- 依數學主題組織段落；在結果旁標明來源、hypotheses、canonical maps 與約化步驟。不可只用題號或抽象同構取代適用條件。
- Projective 沿用 Hartshorne 的有限 projective-space embedding 慣例；`P(E)=Proj Sym E` 採 invertible quotient 慣例；`V(E)=Spec Sym E` 的 sections 對應 `E^∨`。
- II.6–II.8 的補充限用第二章、其先備與已建立的工具；範圍之外的專題見 [TODO](TODO.md)。
- `Check!` 表示正文明確交由讀者證明的純代數或拓撲步驟；形式化缺口另記於 companion 與 [驗證狀態](verification-status.md)。

區塊編號使用 `number: "RV-2"`，標題只放 `title: "Universal property"`。連結目標放在區塊之前：

```typst
#metadata(none) <sup-rv-2>
```

引用使用 `#book-link(<sup-rv-2>)[RV-2]`。獨立預覽缺少目標時只顯示文字，因此仍須核對每個目標存在且唯一。
