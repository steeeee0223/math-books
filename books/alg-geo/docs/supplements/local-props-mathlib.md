# LP 的 mathlib 來源與驗證對照

本文件記錄 [LP 教材](../../src/sup/local-props.typ) 使用的 mathlib 介面、固定版本來源，以及現行 Lean companions 的驗證範圍。本文是來源索引，不是教材正文，也不以同名 mathlib 定義取代 Hartshorne 的定義。

## 版本與驗證檔案

- 來源稽核使用固定 mathlib commit [`e281a66114fe17935e6ea7917a01b714d0c1e493`](https://github.com/leanprover-community/mathlib4/commit/e281a66114fe17935e6ea7917a01b714d0c1e493)。下方原始碼連結固定到此版本，避免行號隨新版變動。
- 目前本地 mathlib checkout 是 [`520045ab14e26149ee970e2e617ca04b09bde5d6`](https://github.com/leanprover-community/mathlib4/commit/520045ab14e26149ee970e2e617ca04b09bde5d6)。2026-09-29 已用此版本檢查兩份 companions。
- [LP 基礎 companion](../../src/sup/lean/local-props.lean) 檢查 ring locality、affine comparisons、stalk criteria、target locality，以及 base change 的可用介面。
- [LP extensions companion](../../src/sup/lean/local-props-extensions.lean) 檢查 dominance、flat base change 的代數約化，以及 projectivity 反例使用的 degree obstruction。
- [形式驗證狀態](verification-status.md) 列出未完成的 scheme assembly 與 comparison lemmas。

Companion 通過只代表其中實際陳述的 Lean 定理成立。教材中的 integral／finite source gluing、faithfully-flat gluing，以及具體反例 schemes 尚未全部形式化。

## Locality 條件

所有環同態均保單位。零環與空 scheme 均允許。`P` 對 ring-map isomorphism 不變。S 與 T 採 scheme morphism 的 source／target 方向。

| 教材條件 | mathlib 介面 |
| --- | --- |
| T | `RingHom.LocalizationAwayPreserves` |
| S | `RingHom.StableUnderCompositionWithLocalizationAwayTarget` |
| GS | `RingHom.OfLocalizationSpanTarget`，有限版本等價 |
| GT | `RingHom.OfLocalizationSpan`，有限版本等價 |
| PL | `RingHom.StableUnderCompositionWithLocalizationAwaySource` |
| BC | `RingHom.IsStableUnderBaseChange` |

教材依下列層次使用這些條件：

- LP-7–LP-8：固定 affine target 的 affine communication 等價於 S + GS。
- LP-12：S + GS 使 all-affine-pairs property 對 source Zariski local。此處的 fixed-target cover induction 是教材證明。mathlib 的 `HasRingHomProperty` 同時包裝 source 與 target locality，因此假設比 LP-12 強。
- LP-14：T + S + GS + GT 使 all-affine-pairs property 可由一組 affine atlas 檢查，並對 source 與 target Zariski local。
- LP-13：whole-inverse-image／`affineAnd` 路線只需 T + GT。加入 BC 後得到 scheme-level base-change stability。
- LP-4：GS + PL 推出 GT。有限型、有限表示與 flatness 的 locality instances 使用此組裝方式。
- BC 是獨立的 transport condition，不是 gluing condition。

## 固定版本原始碼索引

以下連結固定到來源稽核 commit。匿名 instance 不另造名稱。

| 教材用途 | 原始碼宣告 | 教材中的用法 |
| --- | --- | --- |
| Affine-open induction | [`exists_basicOpen_le_affine_inter`](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/AlgebraicGeometry/AffineScheme.lean#L763)<br>[`of_affine_open_cover`](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/AlgebraicGeometry/AffineScheme.lean#L1033) | LP-7–LP-8 的 simultaneous distinguished neighborhoods 與 fixed-target communication。 |
| Ring-local fields | [`RingHom.PropertyIsLocal`](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/RingTheory/LocalProperties/Basic.lean#L183)<br>[`RingHom.OfLocalizationSpanTarget.ofLocalizationSpan`](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/RingTheory/LocalProperties/Basic.lean#L371) | T、S、GS、GT 的介面與 GS + PL ⇒ GT；不包含 BC。 |
| All affine pairs | [`sourceAffineLocally_isLocal`](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/AlgebraicGeometry/Morphisms/RingHomProperties.lean#L157)<br>[`of_source_openCover`](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/AlgebraicGeometry/Morphisms/RingHomProperties.lean#L322)<br>[`isLocal_ringHomProperty_of_isZariskiLocalAtSource_of_isZariskiLocalAtTarget`](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/AlgebraicGeometry/Morphisms/RingHomProperties.lean#L402) | LP-12 與 LP-14 的 scheme-level comparison。現有介面把 source 與 target locality 一起包裝。 |
| Target-local framework | [`IsLocal`](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/AlgebraicGeometry/Morphisms/Basic.lean#L407)<br>[`of_iSup_eq_top`](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/AlgebraicGeometry/Morphisms/Basic.lean#L535) | Distinguished target tests 升級到任意 open covers。 |
| Affine whole inverse image | [`affineAnd_isLocal`](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/AlgebraicGeometry/Morphisms/AffineAnd.lean#L65)<br>[`affineAnd_isStableUnderBaseChange`](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/AlgebraicGeometry/Morphisms/AffineAnd.lean#L109) | LP-13 的 T + GT 路線；先 gluing affineness，再 gluing ring property。 |
| Finite type algebra | [`Algebra.FiniteType.of_span_eq_top_target`](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/RingTheory/Finiteness/FiniteTypeLocal.lean#L82) | LP-17 的 GS。生成子包含局部生成子的分子、covering elements，以及 unit-ideal expression 的係數。 |
| Finite presentation algebra | [`of_span_eq_top_target_aux`](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/RingTheory/Finiteness/FinitePresentationLocal.lean#L40)<br>[`of_span_eq_top_target`](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/RingTheory/Finiteness/FinitePresentationLocal.lean#L61) | LP-20 的 GS。先加入一條 unit-ideal relation，再 gluing kernel 的有限生成性。 |
| Finite type fields | [`finiteType_isLocal`](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/RingTheory/RingHom/FiniteType.lean#L88) | LP-17 的 BC、T、S、GS、GT。 |
| Finite presentation fields | [`finitePresentation_isLocal`](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/RingTheory/RingHom/FinitePresentation.lean#L69) | LP-20 的 BC、T、S、GS、GT。 |
| Flat fields | [`ofLocalizationSpanTarget`](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/RingTheory/RingHom/Flat.lean#L75)<br>[`propertyIsLocal`](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/RingTheory/RingHom/Flat.lean#L85)<br>[`ofLocalizationPrime`](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/RingTheory/RingHom/Flat.lean#L95) | LP-32–LP-33 的 ring locality 與 stalk criterion。 |
| Finite ring maps | [`finite_isStableUnderBaseChange`](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/RingTheory/RingHom/Finite.lean#L47)<br>[`RingHom.finite_ofLocalizationSpan`](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/RingTheory/RingHom/Finite.lean#L86) | LP-23–LP-24 的 BC、T、GT。 |
| Integral ring maps | [`isIntegral_isStableUnderBaseChange`](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/RingTheory/RingHom/Integral.lean#L35)<br>[`isIntegral_ofLocalizationSpan`](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/RingTheory/RingHom/Integral.lean#L44) | LP-26–LP-27 的 BC、T、GT。 |
| Surjective ring maps | [`surjective_isStableUnderBaseChange`](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/RingTheory/RingHom/Surjective.lean#L48)<br>[`surjective_ofLocalizationSpan`](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/RingTheory/RingHom/Surjective.lean#L69) | LP-29–LP-30 的 BC、T、GT。 |
| Faithfully flat ring maps | [`iff_flat_and_comap_surjective`](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/RingTheory/RingHom/FaithfullyFlat.lean#L41)<br>[`isStableUnderBaseChange`](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/RingTheory/RingHom/FaithfullyFlat.lean#L75) | LP-35–LP-36 的 affine comparison 與 BC。此檔未把 GS／GT 封裝成 `PropertyIsLocal`。 |
| Locally finite type | [`HasRingHomProperty`](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/AlgebraicGeometry/Morphisms/FiniteType.lean#L50) | LP-18 的 affine-pair property。 |
| Locally finite presentation | [`HasRingHomProperty`](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/AlgebraicGeometry/Morphisms/FinitePresentation.lean#L52) | LP-21 的 affine-pair property。 |
| Flat morphisms | [`HasRingHomProperty`](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/AlgebraicGeometry/Morphisms/Flat.lean#L51)<br>[`iff_flat_stalkMap`](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/AlgebraicGeometry/Morphisms/Flat.lean#L104)<br>[`flat_and_surjective_iff_faithfullyFlat_of_isAffine`](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/AlgebraicGeometry/Morphisms/Flat.lean#L168) | LP-33 與 LP-36 的 affine／stalk comparisons。 |
| Finite morphisms | [`HasAffineProperty`](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/AlgebraicGeometry/Morphisms/Finite.lean#L48) | LP-24 的 `affineAnd` criterion。實際宣告是 `IsFinite` namespace 下的匿名 instance。 |
| Integral morphisms | [`hasAffineProperty`](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/AlgebraicGeometry/Morphisms/Integral.lean#L45)<br>[`iff_universallyClosed_and_isAffineHom`](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/AlgebraicGeometry/Morphisms/Integral.lean#L135) | LP-26–LP-27 的 target locality；integral ⇔ affine + universally closed。 |
| Closed immersions | [`IsClosedImmersion`](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean#L45)<br>[`IsClosedImmersion.isZariskiLocalAtTarget`](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean#L352)<br>[`IsClosedImmersion.hasAffineProperty`](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean#L358) | LP-30 的 target locality 與 affine quotient criterion。 |
| Quasi-compact morphisms | [`HasAffineProperty`](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/AlgebraicGeometry/Morphisms/QuasiCompact.lean#L117) | LP-41 的 whole-inverse-image criterion。 |
| Affine morphisms | [`isAffine_of_isAffineOpen_basicOpen`](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/AlgebraicGeometry/Morphisms/Affine.lean#L108)<br>[`HasAffineProperty`](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/AlgebraicGeometry/Morphisms/Affine.lean#L146) | LP-43 的 target locality。此處 gluing whole inverse images，不是 gluing 任意 affine source cover。 |
| Separated morphisms | [`isSeparated_eq_diagonal_isClosedImmersion`](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/AlgebraicGeometry/Morphisms/Separated.lean#L52)<br>[`IsZariskiLocalAtTarget`](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/AlgebraicGeometry/Morphisms/Separated.lean#L84) | LP-45 的 diagonal argument 與 target locality。Source gluing 仍需檢查 mixed products。 |
| Universally closed morphisms | [`universallyClosed_isZariskiLocalAtTarget`](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/AlgebraicGeometry/Morphisms/UniversallyClosed.lean#L101) | LP-47 的 target locality。 |
| Surjective scheme maps | [`surjective_isZariskiLocalAtTarget`](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/AlgebraicGeometry/Morphisms/UnderlyingMap.lean#L94) | LP-36 使用的 scheme-level surjectivity。 |

## 教材補充證明與反例

下列論證屬於教材，不宣稱 mathlib 有同名且假設完全相同的定理：

- LP-26 的 integral GS：有限 distinguished source cover 上的 maps 都 integral，因此 affine 且 universally closed。任意 base change 後，closed subset 的 image 是有限個 closed images 的聯集。整個 affine map 因而 universally closed，再由 affine + universally closed 回到 integral。
- LP-23 的 finite GS：合併 integral GS、finite-type GS，以及 integral + finite type ⇔ finite。
- LP-35 的 faithfully-flat GS／GT：使用 flat + surjective on spectra。非空有限 source cover 給 GS；任意有限 target cover給 GT。若 GS 允許零環的空 cover，LP-39 的 `k → 0` 反例說明 unrestricted GS 失敗。
- LP-37–LP-39 集中 ring-property failures。LP-48–LP-49 集中 geometric-property failures。Lean companions 尚未組裝所有具體反例 schemes。

Integral GS 的 characterization 依賴 T／GT 建立的 affine comparison，不依賴待證的 GS，因此沒有循環。

## Hartshorne 定義的接合點

教材保留 Hartshorne-style scheme 與 ring-map conventions。有限型與 finite 的「存在 affine atlas」和「每個 affine pair／target」之間使用 LP 的 locality results，不以同名 mathlib 定義直接代換。

Flatness 的 affine／stalk comparison 使用 `Flat.iff_flat_stalkMap`。Closed immersion 的 structure-sheaf map 是 stalkwise surjective，不能替換為任意 open 上的 sections surjective。Integral morphism、finite presentation 與 locality 字母是教材的組織方式，不宣稱全部出自 Hartshorne II.3。

## 檢查方式

從 repository root 執行：

```sh
typst compile --root . books/alg-geo/src/main.typ /tmp/math-books-alg-geo.pdf
lake env lean books/alg-geo/src/sup/lean/local-props.lean
lake env lean books/alg-geo/src/sup/lean/local-props-extensions.lean
git diff --check
```
