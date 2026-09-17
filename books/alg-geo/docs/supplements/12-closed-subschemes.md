# CS — Closed subschemes and ideal sheaves

> 設計紀錄：保存選題、分工與條件；現行敘述與證明見 [closed-subschemes.typ](../../src/sup/closed-subschemes.typ)，教材分工見 [總覽](README.md)。

定位：集中 closed subscheme 與 ideal sheaf 的基本對應，作為 MG、QC、PJ 共同引用的入口。範圍限於最高優先級的核心內容。

## 正文參照：只連結

- [II.3, D7–D8](../../src/sec-2-3/part-1.typ)：closed subscheme、closed immersion 的定義。
- [II.5.9–II.5.10](../../src/sec-2-5/part-1.typ)：ideal sheaves 與 closed subschemes 的既有對應；不重新敘述或證明。
- [local-props](../../src/sup/local-props.typ)：LP-33 引用 CS-1 的 affine criterion，再處理 target locality 與 base-change stability。

## 核心內容

| 標記 | 擬收錄內容 | 條件與分工 |
| --- | --- | --- |
| CS-1 | Affine quotient 與 ideal sheaf 的對照入口 | 在 X=Spec A 上，集中說明 I⊆A、其 associated ideal sheaf、Spec(A/I)→X 的識別，並由 II.5.9–5.10 證明 A→B surjective iff 對應 map 為 closed immersion。LP-33 引用這個判準，不重證 quotient dictionary。 |
| CS-2 | Ideal sheaf 的 restriction 與 closed subscheme 的 base change | 對 i:Z→X 及 g:X'→X，base-changed subscheme 的 ideal 是 g^*I→O_{X'} 的 image，亦記作 I O_{X'}。一般不能把 g^*I 直接當作 O_{X'} 的 subsheaf；open restriction 是此比較的特例。Base-change stability 本身只引用。 |
| CS-3 | Reduced induced structure 與不同的 closed structures | 固定 closed subset Z⊆X，整理其 reduced induced closed subscheme；在 affine chart 上使用 radical ideal。精確記錄 ideal inclusion 與 closed-subscheme inclusion 的反向關係，連到 XP-3；X_red 的一般建構與 universal property 仍由 XP 提供。 |
| CS-4 | Classical vanishing ideal 與 quotient 的應用 | 以 II.1.21(a)–(b) 為應用，識別 vanishing ideal sheaf 與 O_X/I_Y≅i_*O_Y；引用正文 correspondence、SC 的 ring quotient 及 VS 的 variety／scheme 識別，不另證一般理論。 |

## 核心例子與反例

- A^1_k 中 (t) 與 (t²) 定義相同底層閉集合，但給出不同 closed subschemes；辨認其 reduced induced structure。
- A=k[t]、I=(t)、B=A/(t)：base change 後 I⊗_A B→B 是零映射，說明 CS-2 必須取 image，不能默認 pullback 保留 ideal inclusion。

## 習題對照

| 來源 | 位置與涵蓋範圍 |
| --- | --- |
| [II.1.21(a)–(b)](../../src/sec-2-1/exe.typ) | CS-4；(c) 的 sections 非滿射例子仍在 SC。 |
| [II.2.18(c)–(d)](../../src/sec-2-2/exe.typ) | CS-1；(a)–(b) 仍在 XL／XP。 |
| [II.3.11(a)–(c)](../../src/sec-2-3/exe.typ) | CS-2、CS-1、CS-3，正文與 local-props 已有的結果只引用。 |
| [II.5.5(b)](../../src/sec-2-5/exe.typ) | 作 CS-1 的引用應用；finite pushforward 的 coherence 仍由 QC 處理。 |

## 範圍界線

- PJ 的 homogeneous ideals、truncation、saturation 引用本篇一般對應，不搬入 CS。
- MG-9 已安排的 quasi-compact scheme-theoretic image 維持原位；本次不將 image 理論加入新篇核心。任意 morphism 的 image 仍在 TODO。
- Scheme-theoretic unions／intersections 與 ideal sums／intersections 暫列 TODO，不在核心範圍新增；general intersection theory、embedded components 亦不展開。

先備：II.3 的 closed immersions、SC 的 ideal／quotient、II.5 的 tilde 與 ideal-sheaf correspondence。閱讀 II.2 時可先使用 CS-1 的 affine 參照，其餘內容待相應正文讀完。
