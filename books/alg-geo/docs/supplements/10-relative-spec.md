# RV — Relative Spec and vector bundles

> 設計紀錄：保存選題、分工與條件；現行敘述與證明見 [relative-spec.typ](../../src/sup/relative-spec.typ)，教材分工見 [總覽](README.md)。

定位：獨立的幾何建構教材。先備 XL、QC、AL；局部 gluing 只引用 SL／XL，symmetric algebra 只引用 AL／SC。

## 內容範圍

| 標記 | 內容 | 範圍 |
| --- | --- | --- |
| RV-1 | Relative Spec of a quasi-coherent O_Y-algebra A | 在 affine opens 上建立 Spec Γ(U,A)，以 restriction／localization 的 canonical identifications glue。 |
| RV-2 | Relative Spec universal property | Hom_Y(T,Spec_Y A) 與 Hom_{O_Y-alg}(A,g_*O_T) 的自然對應，g:T→Y。 |
| RV-3 | Affine morphisms 與 quasi-coherent algebras 的反變對應 | Affine locality、quasi-compactness、separatedness 引用既有 local-props；只新增相對 Spec 的識別。 |
| RV-4 | Modules on an affine morphism | QCoh(X) 與 quasi-coherent f_*O_X-modules 的對應；解釋此處 target 不是單純 QCoh(Y)。 |
| RV-5 | Base change of relative Spec | Base change 對應 quasi-coherent algebra 的 pullback；不重建 pullback functor。 |
| RV-6 | Vector bundles 與 transition functions | Finite locally free sheaf 對應幾何 vector bundle；cocycle 與換 basis 的相容性。 |
| RV-7 | Sections 與 dual convention | 明確採 V(E)=Spec_X Sym(E)，其 sections sheaf 是 E^∨；若要 sections 為 E，使用 V(E^∨)。 |

## 例子與界線

- A=O_Y[t_1,…,t_n] 給 relative affine n-space。
- A=O_Y/I 給 closed subscheme，引用正文 ideal-sheaf correspondence。
- Finite locally free E 在 trivializing cover 上給 polynomial algebras；transition matrices 的 dual 方向需列出。
- Non-locally-free coherent module（例如 Spec(k[t]) 上 tilde(k[t]/(t))）的 relative Spec of Sym 仍存在，但不能直接稱為固定 rank vector bundle。

## 習題對照

[II.5 exercises](../../src/sec-2-5/exe.typ)：5.17–5.18。5.1 的 duality 與 5.16 的 symmetric-algebra construction 由 AL／SC 提供，本篇只引用。

Relative Proj 不在核心範圍加入；本篇也不延伸到 general descent 或 moduli of bundles。
