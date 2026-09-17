# QC — Quasi-coherent and coherent operations

> 設計紀錄：保存選題、分工與條件；現行敘述與證明見 [quasi-coherent.typ](../../src/sup/quasi-coherent.typ)，教材分工見 [總覽](README.md)。

定位：只寫 SC／AL 的 operations 與 affine correspondence 之間新增的相容性、有限性條件、失敗例子；不重新建構 functors。

## 正文索引：不重述內容

| 查找主題 | 正文位置 |
| --- | --- |
| Tilde 的 stalks、principal-open sections、global sections | II.5.1 |
| Exactness、fully faithfulness、tensor、direct sum、affine pushforward／pullback | II.5.2 |
| 清分母、affine locality、affine equivalence | II.5.3–II.5.5 |
| Affine sections exactness、kernels／cokernels／images／extensions | II.5.6–II.5.7 |
| Pullback／pushforward 保留 QCoh／Coh 的既有版本 | II.5.8 |
| Ideal sheaves 與 closed subschemes | II.5.9–II.5.10 |

以上均連到 [II.5 正文](../../src/sec-2-5/part-1.typ)。一般 tensor、Hom、adjunction、limits／colimits 的入口連到 SC；純代數 localization 連到 AL。

## 內容範圍

1. **QC-1 — Canonical comparison 的使用規則。** 先指定 morphism，再用正文 principal-open 公式與 SL 檢查同構；不只比較兩邊 stalk 的 abstract isomorphism classes。
2. **QC-2 — Colimits。** QCoh 的任意 small colimit 可在 O-modules 中計算且仍 quasi-coherent。Tilde 與 module colimits 的 canonical comparison；不把同樣結論套到 arbitrary products／inverse limits。
3. **QC-3 — Hom comparison。** Affine 上 M finitely presented、N arbitrary 時，tilde(Hom_A(M,N)) → sheaf Hom(tilde M,tilde N) 是同構。Scheme 上 F finitely presented、G quasi-coherent 時，sheaf Hom(F,G) quasi-coherent。引用 AL-3，不重證代數 Hom localization。
4. **QC-4 — Finite locally free 的較強交換公式。** F finite locally free 時，以 duality 得到 pullback 與 sheaf Hom(F,G) 的相容性；不宣稱僅 finitely presented 即足以對任意 base change 成立。
5. **QC-5 — Pushforward 的 qcqs 版本。** f quasi-compact、quasi-separated 時保留 quasi-coherence，作正文 II.5.8(c) 的明確延伸；affine／finite morphisms 的更強結論引用正文及相關 exercises。
6. **QC-6 — Coherence 的有限性表。** Noetherian schemes 上，既有 finite-operation 結果只索引；finite direct sums 與 infinite direct sums 分開。Coherence 第一版維持 Hartshorne 的 Noetherian 使用情境。
7. **QC-7 — Local presentations。** Quasi-coherence 與局部為 free O-modules 間映射的 cokernel 之間的判準；Noetherian 情形的 coherent 版本要求兩個 free modules 都 finite rank。只使用 SC 的 cokernel 與 AL 的 presentation 定義。
8. **QC-8 — Closed subschemes 的引用入口。** Ideal／quotient 與 II.1.21(a)–(b) 的應用統一引用 [CS-1、CS-4](12-closed-subschemes.md)，classical／scheme 識別引用 [VS](13-varieties-schemes.md)。QC 不再獨立安排相同內容。

QC-5／QC-6 另明列 II.5.5(b)–(c) 的應用：closed immersion 是 finite；Noetherian schemes 間的 finite morphism pushforward 保留 coherence。第一項引用 finite ring-map 判準，第二項以 affine pushforward 與 restriction of scalars 的 finite-generation 計算銜接。SC-10 已提供 II.5.1(d) 的 projection formula，這裡只引用。

## 計算模型

**QC-M1 — DVR 的兩點模型。** R 為 DVR、K 為 fraction field 時，以 R-module M、K-vector space L 及 M⊗_R K → L 描述 Spec R 上的 O-module；quasi-coherence 對應該映射為同構。此模型用來區分一般 O-module 與 quasi-coherent O-module，不另建 sheaf functors。

## 必須收錄的反例

- **QC-E1：ambient product 不必 quasi-coherent。** X=Spec Z，F=∏_n O_X 在全部 O-modules 中取 product。Γ(X,F)=∏ Z，但 D(2) 上的比較是 AL-E2，不是同構；因此不能把 ambient product 當作 tilde(∏ Z)。
- **QC-E2：infinite sum 不保留 coherence。** Spec k 上 ⊕_n k 非有限維。
- **QC-E3：Hom 的 base-change comparison 會失敗。** A=Z、B=Z/2Z、M=Z/2Z、N=Z；B ⊗ Hom_A(M,N) → Hom_B(B⊗M,B⊗N) 不是同構，且 M 已 finitely presented。
- **QC-E4：pushforward 不必保留 coherence。** A^1_k → Spec k 的 O pushforward 對應 k[t]，不是有限維 k-vector space。
- **QC-E5：global sections 與 tensor 不無條件交換。** P^1_k 上 O(-1)、O(1) 的 global sections tensor 比較到 Γ(O) 不是同構。只引用正文的 twisting／sections 計算。

## 習題對照

[II.5 exercises](../../src/sec-2-5/exe.typ)：5.2 → QC-M1；5.4 → QC-7；5.5 → QC-5／QC-6／QC-E4。5.3 的 tilde–Γ adjunction 若保留為獨立命題，只補此 adjunction，與 SC 的 f^*–f_* adjunction 區分；5.16 的 QCoh 保留性由 SC、AL 的建構連到本篇。相關證明由正式教材中的引用查找。

外部條件對照：[Stacks, Functoriality for quasi-coherent modules](https://stacks.math.columbia.edu/tag/01LA)。
