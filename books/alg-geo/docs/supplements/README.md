# II.1–II.5 補充教材

正式教材位於 [src/sup](../../src/sup/sup.typ)，已納入主書，包含 13 篇主題教材與 LP locality calculus。本目錄保存教材分工、習題對照與後續範圍；數學敘述和證明以 Typst 檔案為準。

## 教材入口

| 編號 | 教材 | 核心問題 |
| --- | --- | --- |
| CAT | [Categorical language](../../src/sup/categorical-language.typ) · [設計綱要](01-categorical-language.md) | Universal properties 與 adjunction 如何組織建構？ |
| SL | [Sheaf locality and gluing](../../src/sup/sheaf-locality.typ) · [設計綱要](02-sheaf-locality.md) | 哪些資料可在 open cover、basis 或 stalks 上檢查？ |
| SC | [Sheaf constructions and exactness](../../src/sup/sheaf-constructions.typ) · [設計綱要](03-sheaf-constructions.md) | 各值域範疇如何共用建構，哪些操作不能交換？ |
| AL | [Algebraic tools for modules](../../src/sup/module-algebra.typ) · [設計綱要](04-module-algebra.md) | 有限呈示、localization、tensor 與 duality 的共用代數工具。 |
| XL | [Scheme locality and gluing](../../src/sup/scheme-locality.typ) · [設計綱要](05-scheme-locality.md) | 如何明確地做 affine reduction 與 gluing？ |
| LP | [A Locality Calculus for Morphisms](../../src/sup/local-props.typ) | Ring-local conditions、affine communication 與 morphism locality。 |
| XP | [Topology and intrinsic properties](../../src/sup/scheme-properties.typ) · [設計綱要](06-scheme-properties.md) | 哪些性質可局部檢查，哪些需要全域條件？ |
| MG | [Morphisms, diagonals and graphs](../../src/sup/morphisms.typ) · [設計綱要](07-morphisms.md) | 如何用既有 fiber products 推導幾何性質？ |
| QC | [Quasi-coherent and coherent operations](../../src/sup/quasi-coherent.typ) · [設計綱要](08-quasi-coherent.md) | 一般 sheaf 操作何時留在 QCoh／Coh 中？ |
| SE | [Support, extension and local freeness](../../src/sup/support-extension.typ) · [設計綱要](09-support-extension.md) | 如何控制 support、延伸資料、把 stalk 性質推到鄰域？ |
| RV | [Relative Spec and vector bundles](../../src/sup/relative-spec.typ) · [設計綱要](10-relative-spec.md) | 如何從 quasi-coherent algebras／locally free sheaves 建立幾何物件？ |
| PJ | [Proj and graded modules](../../src/sup/proj.typ) · [設計綱要](11-proj.md) | 如何集中各節分散的 Proj 性質並分階段閱讀？ |
| CS | [Closed subschemes and ideal sheaves](../../src/sup/closed-subschemes.typ) · [設計綱要](12-closed-subschemes.md) | Ideal、affine quotient 與 closed subscheme 如何對應？ |
| VS | [Varieties and schemes](../../src/sup/varieties-schemes.typ) · [設計綱要](13-varieties-schemes.md) | Classical points、regular maps 與 Spec／Proj 如何識別？ |

## 閱讀次序與分工

完整的樹狀 roadmap 位於 [正式教材入口](../../src/sup/sup.typ)。節點只列標題，分支呈現主要閱讀路徑；圖外的先備對照表列出跨分支依賴。同一教材依內容分成初讀與回讀節點。

1. **II.3 前建立 locality 核心。** II.1 → SL，搭配 CAT 讀 SC 的 groups／rings；II.2 與 SL → XL-1–7 → LP-1–15。LP 使用 II.2.13 的 affine quasi-compactness（XP-4 第一項）及 II.2.16–17 的 principal-open 工具。II.2.5 與 XL 也可接 PJ-1–3。
2. **II.3–II.4 配合性質分階段回讀。** XP 的 intrinsic properties 與 LP 的 finite-type、finite、quasi-compact、affine 案例配合 II.3。II.3.3 的 fiber products → MG-1–2、7 及 LP 的 scheme-level BC。II.4 的 diagonal → XP-5 與 LP-50–57；LP-56 還使用 II.4.9。VS 使用 Chapter I、II.2.5–2.6、XL、XP-1，並以 II.4.10 說明 classical comparison 的範圍。
3. **II.5 補齊 modules 與 ideal-sheaf 依賴。** Module definitions 與 AL → SC 的 module statements；II.5.1–5.8、SC、AL → QC → SE。RV 另需 XL、LP 的 affine criterion、MG-1、AL-5 與 SC-7，SE 不是必要先備。II.5.2 與 AL-2 補讀 XL-8。
4. **Closed-subscheme 與 projective 分支。** II.5.9–5.10、II.3 的 closed immersions、SC、MG-1、XP-3 → CS，CS-4 另需 VS。CS-1 供 LP-33 的完整 affine criterion，以及 MG、PJ 的後續證明引用。II.5.11–5.20、QC、AL、CS、XL、LP、MG → PJ-4–10；PJ-10 另用 XP-6 與 II.5.19。

LP 的 ring-level BC 只需要 tensor product，scheme-level BC 才需要 fiber products。LP-27 的 integral GS 使用額外的「integral iff affine and universally closed」定理，LP-23 的 finite GS 再引用它；不能把這兩段標成只依賴 II.2。Flat 與 faithfully flat 案例另需相應的 module-theoretic criteria。

一般 sheaf constructions 集中於 SC，純代數工具集中於 AL。Affineness 的 unit-ideal criterion 證明集中於 XL 的 II.2.17(b)，LP-13 引用它，LP-47 再套用 LP-13。Affine closed-immersion dictionary 集中於 CS-1，LP-33 處理 locality。Disjoint points 與 doubled-origin line 的共用反例在 XP，punctured-plane 的非 affine 計算在 MG-5。這是閱讀依賴，不要求實體章節採相同順序。

## 編輯與引用慣例

- 正文已有結果以連結引用，避免維護重複版本；每個 construction 指定一個主要位置。
- 明列值域範疇、空間假設、有限性條件及比較映射方向；不能只寫兩邊抽象同構。
- 規劃紀錄使用中文；正式教材使用英文並沿用正文記號。
- 不擴充 equalizers/coequalizers、Yoneda、Kan extensions、一般 descent 或 quotient categories；未納入的專題見 [TODO](TODO.md)。
- 習題與補充教材的證明維護雙向連結，避免重複證明。
- 區塊編號使用 `number: "RV-2"`，標題只放 `title: "Universal property"`。自訂 `example`、`remark` 也支援 `number`，預設為 `none`，不自動編號。
- 連結目標使用區塊前的 `#metadata(none) <sup-rv-2>`；引用使用 `#book-link(<sup-rv-2>)[RV-2]`。主書內可點擊，獨立預覽缺少目標時顯示文字。這可避免直接連結 theorion 編號區塊與目前書籍主題的相容性問題。

自訂區塊與 `book-link` 定義見 [defs.typ](../../src/defs.typ)。新增引用時仍須檢查目標存在且唯一；獨立預覽的文字 fallback 不會替作者檢出錯誤標籤。

## 習題分工與後續範圍

[習題涵蓋表](exercise-coverage.md)記錄 94 道編號習題及兩道補充題的內容分工，不是逐題證明完成或形式驗證清單。各篇設計綱要保存選題理由與邊界；未納入的專題與形式化工作集中於 [TODO](TODO.md)。
