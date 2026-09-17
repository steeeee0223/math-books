# XP — Topology and intrinsic properties of schemes

> 設計紀錄：保存選題、分工與條件；現行敘述與證明見 [scheme-properties.typ](../../src/sup/scheme-properties.typ)，教材分工見 [總覽](README.md)。

定位：對 scheme 本身的性質建立條件表與反例索引。Morphism properties 繼續使用既有 local-props。

## 正文參照：只連結

[II.3 正文](../../src/sec-2-3/part-1.typ)：connected、irreducible、reduced、integral、locally Noetherian／Noetherian 的定義與 Propositions 3.1–3.2。只建立索引，不複製這些命題。

## 內容範圍

| 標記 | 內容 | 必須顯示的條件 |
| --- | --- | --- |
| XP-1 | Specialization、generization、generic points、irreducible components | 分成下列 XP-1a–XP-1f；以 prime ideals、local rings 與 open restrictions 串起相關題群。 |
| XP-2 | Connectedness、clopen decompositions 與 idempotents | Spec A 的 decomposition 與 A 的 product decomposition；全域 idempotents 與 clopen subsets 的對應。 |
| XP-3 | Reduction 的建構與 universal property | 引用正文 reduced 定義；補 X_red 與 reduced-source morphisms 的 factorization。 |
| XP-4 | Quasi-compactness、Noetherian topological spaces | 每個 affine quasi-compact；space Noetherian iff 每個 open quasi-compact；locally Noetherian scheme 加 quasi-compact 得 Noetherian；另列 II.3.16 的 Noetherian induction。 |
| XP-5 | Quasi-separatedness 的 affine-overlap criterion | Scheme 的任兩 affine opens 交集 quasi-compact；區分 separated 與 quasi-separated。 |
| XP-6 | Normality 的 affine／stalk criterion | 定義所有 local rings integrally closed domains；可在 open cover 上檢查。Normal 不包含 connected／irreducible 假設；normalization 暫列 TODO。 |
| XP-7 | Finite type 與 Noetherian 的銜接 | Finite-type scheme over a Noetherian scheme 是 Noetherian；Hilbert basis theorem 的代數部分只引用，將 local finite type 與 quasi-compactness 的角色分開。II.3.13 的最後一項。 |

## Generic points 題群

本題群先整理可直接引用的性質，再安排計算與反例。

| 標記 | 擬收錄內容 | 條件與相關習題 |
| --- | --- | --- |
| XP-1a | 非空 irreducible closed subset 的 generic point 存在且唯一；在 Spec A 上，V(p) 的 generic point 是 p | 任意 scheme，無須 Noetherian；II.2.9。 |
| XP-1b | Specialization／generization 與 prime inclusion；T_0 性質、closed points、irreducible components 的 generic points | 明定 y 是 x 的 specialization iff y∈closure({x})；affine 上對應 p_x⊆p_y。Components 對應 minimal primes；II.3.17(b)、(d) 的 scheme 部分。 |
| XP-1c | 非空 open 包含 irreducible scheme 的 generic point，且仍有同一 generic point；components 在 open restriction 下的對應 | 對任意 scheme，U 的 components 是 X 中與 U 相交的 components 和 U 的交集；不預設 components 有限。II.3.17(c)，並補 open-restriction 版本。 |
| XP-1d | Integral scheme 的 generic local ring 是 function field；非空 affine opens 的 fraction fields 與它自然識別 | K(X)=O_{X,η}=κ(η)；任意非空 open U 的 Γ(U,O_X) 自然嵌入 K(X)。II.3.6；非 integral 情形不沿用 field 結論。 |
| XP-1e | Dominant morphism 對 generic points 的作用與 function-field inclusion | Integral X、Y 下，f dominant iff f(η_X)=η_Y，並誘導 K(Y)→K(X)。作 II.3.7 的先備，不在此處理 generically finite 的 finite-extension／dense-open finiteness 結論。 |
| XP-1f | Noetherian schemes 的底層空間與 Zariski spaces；generic points 與 closed points 的角色比較 | II.3.17(a)–(d) 作整合；II.3.14 的 finite-type-over-a-field closed-point density 作對照。不把 Noetherian 或 closed-point density 當作 generic-point 存在性的必要條件。 |

XP-1e 另加入 affine 判準：A→B 誘導的 map dominant iff ker(A→B) 包含於 A 的 nilradical；A reduced 時才可將此條件換成 injectivity。這補上 II.2.18(b) 的 dominance 部分，並以 A→A_red 作為「dominant 不必對應 injective ring map」的反例。

### 計算與反例

- **兩個 components 的 generic points。** X=Spec(k[x,y]/(xy))：辨認 (x)、(y)，計算其 closures，並比較 D(x)、D(y) 上留下哪些 components。連到 XP-1b–XP-1c。
- **Generic local ring 不必是 field。** X=Spec(k[ε]/ε²) 只有一個點，它同時是 generic point 與 closed point，但其 local ring 不是 field。連到 XP-1d 的 reducedness／integrality 條件。
- **所有 closed points 可以 dense，卻不含 generic point。** A^1_k（k algebraically closed）的 closed points 作例子；避免把「dense subset」與「包含 generic point」直接視為等價。
- **Closed points 不一定 dense。** 非 field 的 DVR spectrum 只有 generic point 與一個 closed point，後者不是 dense。對照 II.3.14 的 finite-type 假設。
- **Generic-point 計算不只追蹤底層點。** A^1_k→A^1_k，s↦t²，計算 generic-point 上的 k(s)→k(t)；完整 generic fibre 的 scheme 計算仍引用 MG，不重複建構。

### 與後續專題的分界

II.3.18(b)「irreducible Zariski space 中，constructible subset dense iff 包含 generic point，且此時包含非空 open」列作後續連結；須先建立 constructibility，因此核心範圍不將其完整搬入 XP。II.3.17(e) 的 t(X)／soberification 比較同樣留作延伸。II.3.8、3.19、3.22 只引用本篇 generic-point 工具，normalization、Chevalley 與 dimension of fibres 仍為非優先專題。

## Locality 對照表的欄位

每個性質列出：是否保留於 open restriction、是否可由 arbitrary open cover 檢查、是否可由 stalks 檢查、affine algebra criterion，以及所需的額外全域条件。

- Reduced、normal、locally Noetherian 分別列出條件，不把三者的 stalk criteria 混為一談。
- Quasi-compactness 由有限個 quasi-compact opens 的 cover 得到，不能用 arbitrary cover 推回。
- Irreducibility／connectedness 不由「每個 cover member 有該性質」無條件推出；另列 overlap／連通覆蓋條件。
- Integral 引用正文 reduced + irreducible 的刻畫，所有 domain 敘述只在非空 opens 上使用。

## 必須收錄的反例

- 無限多個 Spec k 的 disjoint union：locally Noetherian，但不 quasi-compact／Noetherian。
- Spec(k ⊕ V)，V 是無限維 k-vector space、V²=0：底層空間只有一點，但 ring 不 Noetherian。
- A = ∏_{n≥0} F_2：各 local rings 是 fields，但 A 不 Noetherian，不能以所有 stalks Noetherian 取代 locally Noetherian。
- 兩份 Spec k 的 disjoint union：有 integral affine cover，但全域不 connected／irreducible。
- Spec(k[x,y]/(xy)) 去掉原點：connected scheme 的 open subset 可以 disconnected。
- Spec(k × k)：normal scheme 不必 integral。

## 習題對照

| 來源 | 本篇位置與涵蓋範圍 |
| --- | --- |
| [II.2.9](../../src/sec-2-2/exe.typ) | XP-1a：generic points 的存在與唯一性。 |
| [II.3.6](../../src/sec-2-3/exe.typ) | XP-1d：generic local ring、function field 與 affine fraction fields。 |
| II.3.7 | XP-1e 僅提供 dominance／function-field inclusion 的先備；主要結論留待後續專題。 |
| II.3.14 | XP-1f 與 closed-point density 的例子／反例。 |
| II.3.17(a)–(d) | XP-1b、XP-1c、XP-1f；scheme 情形可不依賴 Noetherian 的結論另標適用範圍。 |
| II.3.18(b) | 後續 constructibility 專題的交叉引用，不列為核心範圍已涵蓋。 |
| II.2.3、2.13、2.19；II.3.16 | 分別對應 XP-3、XP-4、XP-2 與 Noetherian induction。 |
| II.2.18(b)；II.3.13 最後一項 | 分別對應 XP-1e 的 affine dominance criterion 與 XP-7。 |

題號依 [II.2 exercises](../../src/sec-2-2/exe.typ) 與 [II.3 exercises](../../src/sec-2-3/exe.typ) 的現有內容核對；原題與證明均保持原位。完整 normalization、dimension、constructibility 留在 TODO。
