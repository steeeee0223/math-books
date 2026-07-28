# local-props 的 mathlib 證明來源

教材：[local-props.typ](local-props.typ)。查閱日期：2026-09-07。
固定 mathlib commit：[e281a66114fe17935e6ea7917a01b714d0c1e493](https://github.com/leanprover-community/mathlib4/commit/e281a66114fe17935e6ea7917a01b714d0c1e493)。

這次改寫從此版本原始碼的定義、證明本體與依賴抽取數學論證；不是建立 Lean 專案，也沒有宣稱教材文字已由 Lean kernel 驗證。教材保留原有兩份 summary tables 及全部原有反例；僅修正 faithfully flat 的 GS 一格，以符合 mathlib 允許空 cover 的定義，沒有加入 sec-2-3 的 include。

## 抽象與必要條件

所有環同態均保單位，允許零環與空 scheme；P 對 ring-map isomorphism 不變。S/T 指幾何方向。

| 教材 | mathlib |
| --- | --- |
| T | RingHom.LocalizationAwayPreserves |
| S | RingHom.StableUnderCompositionWithLocalizationAwayTarget |
| GS | RingHom.OfLocalizationSpanTarget（有限版本等價） |
| GT | RingHom.OfLocalizationSpan（有限版本等價） |
| PL | RingHom.StableUnderCompositionWithLocalizationAwaySource |
| BC | RingHom.IsStableUnderBaseChange |

- 固定 affine target 的 universal affine communication **等價於 S + GS**。充分性取自 affine-open induction；必要性是教材補充：單一 affine cover 得 S，distinguished cover 得 GS。
- P 能延伸成在 spectra 上等於 P、且雙邊 Zariski local 的 scheme 性質，**等價於 T + S + GS + GT**。mathlib 有從雙邊 locality 回推 PropertyIsLocal 的定理。這不宣稱四個欄位彼此邏輯獨立。
- affineAnd 路線用 iso invariance + T + GT 得 target locality，不需要 S、GS。閉浸入的實際檔案採先幾何後環判準的順序，教材另行交代。
- GS + PL ⇒ GT 是 mathlib 的組裝引理；有限型、有限表示、flat 的 PropertyIsLocal instance 都利用它。PL 不應作為所有 locality 證明的額外欄位。
- BC 另證。教材新增「P(A → B) := B reduced」的反例：雙邊 local，但沿 k → k[ε]/(ε²) 的 base change 破壞 reducedness。

## 原始碼索引

以下連結固定 commit 與原始碼行號。instance 的名稱以原始碼實際呈現為準；匿名 instance 不臆造名稱。

| 教材用途 | 原始碼宣告 | 使用方式 |
| --- | --- | --- |
| Affine-open induction | [exists_basicOpen_le_affine_inter](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/AlgebraicGeometry/AffineScheme.lean#L763)<br>[of_affine_open_cover](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/AlgebraicGeometry/AffineScheme.lean#L1033) | 兩個 affine open 中同時 distinguished 的鄰域；restriction + finite distinguished gluing 的歸納。 |
| Ring-local fields | [RingHom.PropertyIsLocal](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/RingTheory/LocalProperties/Basic.lean#L183)<br>[RingHom.OfLocalizationSpanTarget.ofLocalizationSpan](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/RingTheory/LocalProperties/Basic.lean#L371) | T、GS、GT、S 四個欄位；GS + PL ⇒ GT；不包含 BC。 |
| All affine pairs | [sourceAffineLocally_isLocal](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/AlgebraicGeometry/Morphisms/RingHomProperties.lean#L157)<br>[of_source_openCover](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/AlgebraicGeometry/Morphisms/RingHomProperties.lean#L322)<br>[isLocal_ringHomProperty_of_isZariskiLocalAtSource_of_isZariskiLocalAtTarget](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/AlgebraicGeometry/Morphisms/RingHomProperties.lean#L402) | target 階段使用 T + GT；fixed-target source 階段使用 S + GS；最後一項證明雙邊 locality 的必要條件。 |
| Target-local framework | [class IsLocal](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/AlgebraicGeometry/Morphisms/Basic.lean#L407)<br>[of_iSup_eq_top](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/AlgebraicGeometry/Morphisms/Basic.lean#L535) | AffineTargetMorphismProperty.IsLocal 與 HasAffineProperty；distinguished target tests 升級到任意 open covers。 |
| Affine whole inverse image | [affineAnd_isLocal](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/AlgebraicGeometry/Morphisms/AffineAnd.lean#L65)<br>[affineAnd_isStableUnderBaseChange](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/AlgebraicGeometry/Morphisms/AffineAnd.lean#L109) | iso invariance + T + GT；先黏合 affineness，再黏合 ring property；BC 另證。 |
| Finite type algebra | [Algebra.FiniteType.of_span_eq_top_target](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/RingTheory/Finiteness/FiniteTypeLocal.lean#L82) | 生成子包括局部生成子的分子、covering elements、unit-ideal expression 的係數。 |
| Finite presentation algebra | [of_span_eq_top_target_aux](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/RingTheory/Finiteness/FinitePresentationLocal.lean#L40)<br>[of_span_eq_top_target (](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/RingTheory/Finiteness/FinitePresentationLocal.lean#L61) | 先加一條 unit-ideal relation 到多項式代數，再黏合 kernel 的有限生成性。 |
| Finite type fields | [finiteType_isLocal](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/RingTheory/RingHom/FiniteType.lean#L88) | BC ⇒ T；composition + principal localization ⇒ S、PL；GS + PL ⇒ GT。 |
| Finite presentation fields | [finitePresentation_isLocal](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/RingTheory/RingHom/FinitePresentation.lean#L69) | 和 finite type 相同的四欄位組裝方法，GS 使用 finite presentation algebra lemma。 |
| Flat fields | [ofLocalizationSpanTarget](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/RingTheory/RingHom/Flat.lean#L75)<br>[propertyIsLocal](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/RingTheory/RingHom/Flat.lean#L85)<br>[ofLocalizationPrime](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/RingTheory/RingHom/Flat.lean#L95) | GS 用 Module.flat_of_isLocalized_span；用 composition/localization 建立 S、PL；stalk 判準另證。 |
| Finite ring maps | [finite_isStableUnderBaseChange](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/RingTheory/RingHom/Finite.lean#L47)<br>[RingHom.finite_ofLocalizationSpan](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/RingTheory/RingHom/Finite.lean#L86) | BC、T、GT；GT 清除分母後黏合 module generators。 |
| Integral ring maps | [isIntegral_isStableUnderBaseChange](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/RingTheory/RingHom/Integral.lean#L35)<br>[isIntegral_ofLocalizationSpan](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/RingTheory/RingHom/Integral.lean#L44) | BC、T、GT；GT 在 integral closure 子模內黏合 membership。 |
| Surjective ring maps | [surjective_isStableUnderBaseChange](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/RingTheory/RingHom/Surjective.lean#L48)<br>[surjective_ofLocalizationSpan](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/RingTheory/RingHom/Surjective.lean#L69) | BC 用 pure tensors；GT 在 image 子模內清分母並黏合。 |
| Faithfully flat ring maps | [iff_flat_and_comap_surjective](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/RingTheory/RingHom/FaithfullyFlat.lean#L41)<br>[isStableUnderBaseChange](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/RingTheory/RingHom/FaithfullyFlat.lean#L75) | flat + surjective on Spec 的等價式與 BC；此檔未把 GS/GT 封裝成 PropertyIsLocal。 |
| Locally finite type | [: HasRingHomProperty](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/AlgebraicGeometry/Morphisms/FiniteType.lean#L50) | 用 finiteType_isLocal 建立 HasRingHomProperty。 |
| Locally finite presentation | [: HasRingHomProperty](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/AlgebraicGeometry/Morphisms/FinitePresentation.lean#L52) | 用 finitePresentation_isLocal 建立 HasRingHomProperty。 |
| Flat morphisms | [: HasRingHomProperty](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/AlgebraicGeometry/Morphisms/Flat.lean#L51)<br>[iff_flat_stalkMap](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/AlgebraicGeometry/Morphisms/Flat.lean#L104)<br>[flat_and_surjective_iff_faithfullyFlat_of_isAffine](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/AlgebraicGeometry/Morphisms/Flat.lean#L168) | 雙邊 locality；stalk 定義比較；faithfully flat 的 affine 比較。 |
| Finite morphisms | [: HasAffineProperty](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/AlgebraicGeometry/Morphisms/Finite.lean#L48) | 實際為 IsFinite namespace 下的匿名 instance，使用 affineAnd/T/GT。 |
| Integral morphisms | [hasAffineProperty](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/AlgebraicGeometry/Morphisms/Integral.lean#L45)<br>[iff_universallyClosed_and_isAffineHom](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/AlgebraicGeometry/Morphisms/Integral.lean#L135) | T/GT 的 affineAnd 路線；integral ⇔ affine + universally closed。 |
| Closed immersions | [class IsClosedImmersion](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean#L45)<br>[IsClosedImmersion.isZariskiLocalAtTarget](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean#L352)<br>[IsClosedImmersion.hasAffineProperty](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean#L358) | 先證明 closed embedding + stalk surjectivity 的 target locality，再得到 affine ring-map criterion。 |
| Quasi-compact morphisms | [: HasAffineProperty](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/AlgebraicGeometry/Morphisms/QuasiCompact.lean#L117) | affine target 上整個 source 的 CompactSpace（不要求 Hausdorff）；finite unions 與 basic opens。 |
| Affine morphisms | [isAffine_of_isAffineOpen_basicOpen (](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/AlgebraicGeometry/Morphisms/Affine.lean#L108)<br>[: HasAffineProperty](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/AlgebraicGeometry/Morphisms/Affine.lean#L146) | global functions 的 unit-ideal basic-open cover 黏合到 Spec Γ；非任意 affine source cover。 |
| Separated morphisms | [isSeparated_eq_diagonal_isClosedImmersion](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/AlgebraicGeometry/Morphisms/Separated.lean#L52)<br>[: IsZariskiLocalAtTarget](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/AlgebraicGeometry/Morphisms/Separated.lean#L84) | closed immersion 的 diagonal construction；source gluing 要注意 mixed products。 |
| Universally closed morphisms | [universallyClosed_isZariskiLocalAtTarget](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/AlgebraicGeometry/Morphisms/UniversallyClosed.lean#L101) | universally(topologically IsClosedMap)；對每次 base change 使用 closed-map target gluing。 |
| Surjective scheme maps | [surjective_isZariskiLocalAtTarget](https://github.com/leanprover-community/mathlib4/blob/e281a66114fe17935e6ea7917a01b714d0c1e493/Mathlib/AlgebraicGeometry/Morphisms/UnderlyingMap.lean#L94) | 對底層映射的滿射性作 target gluing。 |

## 從 mathlib 結果推導的補充

以下論證已寫入教材，但不宣稱在 mathlib 中存在對應同名、同假設的獨立定理。

- **Integral 的 GS**：有限 distinguished source cover 的每個 map integral，故 universally closed。任意 base change 後，closed subset 的 image 是有限個 closed images 的聯集，因此整個 affine map universally closed。用 IsIntegralHom.iff_universallyClosed_and_isAffineHom 回到 integral。該 characterization 的建構依賴 T/GT，不依賴待證的 GS，沒有循環。
- **Finite 的 GS**：由 integral GS 和 finite-type GS，再用 integral + finite type ⇔ finite。
- **Faithfully flat 的 GS/GT**：由 flat + surjective on Spec 的等價式得到非空 finite-cover GS，以及不限空/非空 cover 的 GT。mathlib 的 GS 允許空 cover，因此 unrestricted GS 實際為 **no**：取 k → 0，以零環的空 distinguished cover 為反例。這是原表格唯一修正，旁註非空-cover 約定下的 yes。
- **Fixed-target 必要性與 reduced-source BC 反例**：由來源框架作出的教材推論。
- **反例**：保留原教材的具體例子並補充論證；未聲稱這些具體構造都已在 mathlib 形式化。

## Hartshorne 定義的接合點

保留 Hartshorne-style scheme 與 ring-map conventions。有限型/finite 的「存在 affine atlas」與「每個 affine pair/target」之間使用上述 locality 結果；不是用同名定義直接代換。Flat 的 affine/stalk 比較使用 Flat.iff_flat_stalkMap。Closed immersion 的 surjective sheaf map 是 stalkwise surjective，不能替換為任意 open 上 sections 滿射。Integral morphism、finite presentation 與 locality 字母是教材延伸內容，不假稱全都出自 Hartshorne II.3。

本索引記錄與 mathlib 的定義接合，並不聲稱完成 Hartshorne 原書逐頁、逐字的文獻校勘。

## 檢查

- 單獨編譯教材：`typst compile --root . books/alg-geo/src/sec-2-3/local-props.typ /private/tmp/local-props-mathlib.pdf`。
- 對照 git HEAD：兩份表格只有 faithfully flat / GS 由 yes 改為 no；保留全部 8 個反例，另加 2 個反例（BC 與空-cover GS）。
- sec-2-3.typ 維持原有 include。
