# 後續範圍

以下題群尚未納入核心教材範圍。

- [ ] Flasque sheaves、sections 的非正合性與 cohomology 的準備：II.1.16、1.20(b) 的 flasque 強化、1.21(d)–(e)。II.1.21(a)–(c) 已由 CS／SC 安排。
- [ ] Espace étalé 與 sheaves 的幾何模型：II.1.13。
- [ ] Tangent vectors 與具體 residue-field 計算：II.2.8、2.10–2.11。II.2.7、2.15 已分別由 MG-7、VS 及正文引用安排，不再整題列為後續。
- [ ] Generically finite maps、normalization：II.3.7 的主要結論、II.3.8。II.3.6 與 dominance／function-field inclusion 已在 XP。
- [ ] Geometric reducedness／irreducibility 與 field extensions：II.3.15。
- [ ] Constructibility、Chevalley、dimension 與 fibre dimension：II.3.18–3.23。
- [ ] II.3.17(e) 的 t(X) 比較；II.3.23 的 varieties product comparison 與上項分開追蹤，VS 暫不新增 product 比較，MG 只提供先備。
- [ ] II.3.11(d) 的任意 morphism 之 scheme-theoretic image：MG 先安排 quasi-compact 版本，不能將 kernel 的 quasi-coherence 與 open restriction 相容性無條件套用。
- [ ] II.5.9(c) 的完整 equivalence formulation：PJ 先保留具體 high-degree comparisons，不新增 quotient-category 工具。
- [ ] Valuation rings、valuative criteria 與 properness：II.4.5–4.6、4.11–4.12。
- [ ] Real forms 與 field descent：II.4.7；不混入 open-cover gluing。
- [ ] Chow's lemma：II.4.10。
- [ ] Relative Proj 與 blow-ups：作為 Proj、relative Spec 之後的專題另行評估。

- [ ] CS 的進階內容：ideal sums／intersections 與 scheme-theoretic unions／intersections；核心教材只涵蓋 CS-1–CS-4。既有 MG-9 的 quasi-compact image 內容保持原位。
- [ ] VS 的一般 open／closed subvariety correspondence 完整整理；核心版僅保留 CS-4 所需的識別，II.3.23 的 product 比較依前項追蹤。


擴充或進一步整併時，逐小題核對內容與假設並維護雙向引用，保留尚有獨立內容的習題證明。

## 形式化工作

Lean companions 的局部結果不等於教材命題已端到端形式化。後續核對以 [companion 原始碼](../../src/sup/lean/)的宣告與缺口註記為準。

- [ ] CAT、SL、SC、AL、XL：完成範疇、sheaf 與 scheme 層的全域組裝，核對各 companion 的覆蓋界限。
- [ ] XP、MG：global idempotents、components、reduced factorization 與具體反例 scheme 的完整形式化。
- [ ] QC、SE：qcqs pushforward、Hom/pullback、support、extension 與 local freeness 的全域 sheaf 比較。
- [ ] RV：relative Spec functor、universal property、module equivalence 與 vector-bundle gluing。
- [ ] PJ：radical-domain graded maps、high-degree localization、graded adjunction／reconstruction／Čech exactness，以及 saturation、Veronese、Segre、twists 與 normality 的完整比較；包含尚未完成的代數步驟。
- [ ] CS、VS：ideal sheaf 與 base change 的全域比較，以及 classical variety category、associated scheme functor 與 full faithfulness。
