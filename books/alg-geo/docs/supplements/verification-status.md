# 補充教材的形式驗證狀態

本檔依現行 [Lean companions](../../src/sup/lean/) 的宣告與缺口註記整理，核對日期為 2026-09-18。教材位置見 [總覽](README.md)，尚未納入的教材內容見 [TODO](TODO.md)。

Companion 通過 Lean 只驗證檔案中實際陳述的定理。它不自動驗證整篇教材，也不補上未編碼的 sheaf comparison、scheme gluing 或終端代數斷言。以下是覆蓋索引，不是本次重新執行所有 Lean 檔案的結果。

## II.1–II.5 與 LP 基礎

| Companion | 現有內容與尚待完成的比較 |
| --- | --- |
| [CAT](../../src/sup/lean/categorical-language.lean) | Universal properties、localization、filtered colimits 與 adjunction 的範疇接口；涵蓋範圍以各宣告的型別與假設為準。 |
| [SL](../../src/sup/lean/sheaf-locality.lean) | Local equality、basis extension 與 compatible families；SL-4 另用 [II.1.15–1.22 companion](../../src/sup/lean/ii-1-exercise-15-22.lean)，其中仍有 fixed-base gluing 的接口缺口。 |
| [SC](../../src/sup/lean/sheaf-constructions.lean) | Limits、stalks 與 module-sheaf adjunction；tensor 的 stalk formula、symmetric／exterior sheaf comparisons 尚未組成完整全域同構，反例的具體空間也未全部建構。 |
| [AL](../../src/sup/lean/module-algebra.lean) | Finiteness、localization、duality 與 power operations 的代數接口；graded decomposition／filtration 到 graded sheaf 的組裝尚未編碼。 |
| [XL](../../src/sup/lean/scheme-locality.lean) | Scheme-morphism gluing 與 exact localization；XL-1、XL-2、XL-4–XL-7 另由 [II.2 companion](../../src/sup/lean/ii-2-exe.lean) 與 [LP](../../src/sup/lean/local-props.lean) 提供對應。 |
| [LP 基礎](../../src/sup/lean/local-props.lean) | Ring locality、affine／stalk comparisons、target locality 與 base change；integral／finite source gluing、faithfully-flat gluing 與具體反例尚未完整形式化。LP-54–LP-64 見下表。 |
| [XP](../../src/sup/lean/scheme-properties.lean) | Generic points、dominance、idempotents、compactness 與 Noetherianity；normal scheme 的全域組裝與具體反例尚缺。Reduction 另見 II.2 companion。 |
| [MG](../../src/sup/lean/morphisms.lean) | 實際 scheme fiber products、graphs、quasi-compact image kernel；完整反例 schemes 與 global reduced-morphism construction 尚未組裝。 |
| [QC](../../src/sup/lean/quasi-coherent.lean) | Affine comparison、colimits、Hom 與有限 Čech equalizer；qcqs pushforward 的全域 sheaf 比較與 coherence 比較尚待組裝。 |
| [SE](../../src/sup/lean/support-extension.lean) | Support、stalk exactness、finite denominators 與 fiber-rank algebra；extension by zero、coherent enlargement gluing、rank loci 與 local-freeness equivalence 尚未全域組裝。 |
| [RV](../../src/sup/lean/relative-spec.lean) | Relative scheme gluing、affine universal properties 與 symmetric algebra；quasi-coherent algebra functor、保留 algebra action 的 module equivalence 與 vector-bundle gluing 尚缺。 |
| [PJ](../../src/sup/lean/proj.lean) | Homogeneous charts、localization、saturation 的代數步驟；radical-domain map、high-degree comparison、graded adjunction／reconstruction／Čech exactness，以及 Veronese、Segre、twists、normality 尚缺完整比較。 |
| [CS](../../src/sup/lean/closed-subschemes.lean) | Closed-subscheme dictionary、scheme pullbacks 與 tensor quotient；pullback ideal 的 sheaf-module image 比較及 classical variety functor 尚缺。 |
| [VS](../../src/sup/lean/varieties-schemes.lean) | Nullstellensatz、closed points、Proj charts 與 gluing uniqueness；尚未定義 classical variety category 與 Hartshorne 的 t functor，full faithfulness 尚未端到端形式化。 |

SC、QC、SE 的部分結果另由 [II.1.1–1.12](../../src/sup/lean/ii-1-exercise-1-12.lean)、[II.1.18](../../src/sup/lean/ii-1-exercise-18.lean) 與 [II.5](../../src/sup/lean/ii-5-exe.lean) 的 exercise companions 提供。核對時須一起閱讀，不能只按同名檔案判斷覆蓋。

## II.6–II.8 與 LP 擴充

下表保留尚未完成的關鍵約化；直接套用 mathlib 定理時，仍須核對其定義與 Hartshorne 的假設是否一致。

| Companion | 已編碼的內容 | 尚缺的重要步驟 |
| --- | --- | --- |
| [DV](../../src/sup/lean/divisors-line-bundles.lean) | Unit-valued transitions／cocycle、fractional frames、Cartier multiplication、semilocal rank-one triviality、DV-10 實際商模 exact sequence 與 product-length formula、scalar-extension inputs。 | Cartier sheaf 與 meromorphic global equivalence、associated-point extension、homogeneous prime avoidance、curve degree 組裝、P¹／P¹×P¹ sections、cone class group。 |
| [AL2](../../src/sup/lean/module-algebra-2.lean) | Hartshorne annihilator 與 associated-prime definition 比較、finiteness／localization／zero divisors、total quotient injection、semilocal frames、regular pair 的實際 Koszul maps 與 exactness。 | Embedded ring normal forms、general associated-graded isomorphism、任意長度 Koszul、depth／CM／Serre、regular local quotient 與 cone／cusp normality；這些終端代數命題仍未全部驗證。 |
| [BU](../../src/sup/lean/blowups.lean) | Localization saturation、prime saturation、flat tensor 的 ideal-power injection、solved polynomial chart quotients、cusp／node／cone substitutions。 | Relative Rees Proj、全域 universal property、graph closure、regular-center charts regularity、exceptional line bundles 與 normal bundle 的組裝。 |
| [DF](../../src/sup/lean/differentials-tangent-spaces.lean) | Kähler localization／base change、quotient conormal exactness、dual-number／derivation maps、normalization relation 與 torsion annihilation、Euler coordinate kernel、local differential identity。 | Torsion kernel 的完備分類、residue cotangent sequence 的所有比較、scheme-level tangent／normal gluing、determinant adjunction 與 projective canonical transitions。 |
| [LP2](../../src/sup/lean/local-props-2.lean) | Scheme smooth／étale／unramified locality、composition／base change、diagonal criterion、flat regular-sequence interfaces。 | Hartshorne geometrically regular 與所用 smooth definition 的比較、Cartier／regular immersion 的完整 sheaf bridge、固定 bundle ampleness 與 local-base spreading。 |
| [PJ2](../../src/sup/lean/proj-2.lean) | Relations factorization、scheme pullback universal property、graded charts、cone quotient、proper vertex ideal，以及 odd-module presentation 的 k² residue quotient 與非循環性。 | Quotient-valued relative Proj functor、sheaf／twist comparisons、odd-module presentation 與 O(1) 的識別、vertex localization、normal bundle 的全域識別。 |
| [PM](../../src/sup/lean/projective-morphisms.lean) | Finite-list exponent bound、加入座標保持 surjectivity、closed-immersion composition、monic-at-infinity argument、ruled polynomial-chart surjectivity、finite injective algebra 的 spectrum surjectivity。 | 相對 ample 的全域 embedding theorem、line-bundle generation／twisting、very ample differences、homogeneous normalization 與 degree-zero finite generation、ruled embeddings 與有限投影的 scheme 組裝。 |
| [RM](../../src/sup/lean/rational-maps.lean) | 實際 dense-open rational maps、maximal representative（absolute separated target）、composition、generic-map equivalence／spreading、proper graph projection、valuative inputs。 | Relative maximal representative 的組裝、field-embedding equivalence 全部步驟、generically finite 的整個 inverse-image argument、reduced graph closure、DVR／Hartogs global extension、pencil maximality。 |
| [VS2](../../src/sup/lean/varieties-schemes-2.lean) | Conic ring k[x,y][t]/(t−xy) 的實際 quotient equivalence、t↦xy 的 injective structure map 與 flatness、relative Jacobian entries、chart／transform identities。 | Projective conic 的三張 charts 組裝、scheme-level smooth locus、polarization degree；其餘案例仍依各主題 companion 的已列缺口。 |
| [LP extensions](../../src/sup/lean/local-props-extensions.lean) | Dominance target locality／composition／restriction、nil-kernel criterion／flat tensor kernel／nil-ideal extension；reduced target 的 scheme-level flat base change；nodal Picard coordinates 的 degree-zero obstruction。 | Nonreduced target 的有限 affine-cover 組裝、associated-point sheaf criterion、normal height-one intersection／Hartogs、nodal conductor 與 Picard 分類、singular-fiber degree 的有限長度比較、projective counterexample schemes。 |

後續工作按各 companion 的缺口補足教材實際使用的約化；不能用無關的代數等式取代全域命題，也不能把 `Check!` 的讀者作業計為已完成的 Lean 證明。

## 檢查方式

從 repository root 執行，將 `<name>` 換成受影響檔案的名稱：

```sh
typst compile books/alg-geo/src/main.typ /tmp/math-books-alg-geo.pdf
typst compile --root books/alg-geo/src books/alg-geo/src/sup/<name>.typ /tmp/<name>.pdf
lake env lean books/alg-geo/src/sup/lean/<name>.lean
git diff --check
```

證明變更依 [ag-proof](../../../../.agents/skills/ag-proof/SKILL.md) 核對對應 companion；交叉引用另查 `book-link` 目標是否存在且唯一。記錄檢查結果時列明執行日期、檔案與仍缺的證明，不能將歷史 build、PDF 頁數或一次編譯成功當作目前驗證完成的依據。
