# CAT — Categorical language

> 設計紀錄：保存選題、分工與條件；現行敘述與證明見 [categorical-language.typ](../../src/sup/categorical-language.typ)，教材分工見 [總覽](README.md)。

定位：僅提供後續教材會使用的共用語言；不發展獨立的範疇論課程。先備為 categories、functors、morphisms 的基本概念。

## 內容範圍

| 標記 | 內容 | 範圍與條件 |
| --- | --- | --- |
| CAT-1 | Natural transformations、自然同構、commutative diagrams | 以與限制映射相容的映射族為動機；不使用 Yoneda。 |
| CAT-2 | Universal property 與唯一到唯一同構 | 唯一性必須相對於指定的結構映射；不是聲稱物件沒有其他 automorphisms。 |
| CAT-3 | Initial／terminal objects、products／coproducts | 分清 Hom 的方向，涵蓋空指標族。 |
| CAT-4 | Limits／colimits：diagrams、compatible cones／cocones、誘導映射 | 只處理 small diagrams；存在性需在所用範疇中另行確認。 |
| CAT-5 | Directed systems、inverse systems、filtered colimits | 區分一般 colimit 與 filtered colimit；以 directed posets 作主要計算模型。 |
| CAT-6 | Adjunction 的自然 Hom bijection、unit／counit、triangle identities | 左伴隨保留存在的 colimits；右伴隨保留存在的 limits。 |

## 例子與比較

- Sets 中 product 與 disjoint union 的不同 universal properties。
- Abelian groups 的有限 direct sum 同時是 product 與 coproduct；無限情形需區分。
- Commutative unital rings 中 product 與 coproduct 的差異；後者的二元例子是 tensor product over Z。
- Localization 的 universal property：明列需變成 units 的乘法集合。
- Sheafification、inverse image／direct image 只作連結到 SC 的例子，不在此建構。

## 不在此重複

- Sheafification 的正文敘述：引用 [II.1, Proposition-Definition 1.2](../../src/sec-2-1/part-1.typ)。
- Fiber product 的具體定義：引用 [II.3, D10](../../src/sec-2-3/part-1.typ)。本文只說明它是 limit 的一個例子。
- f^{-1}、f_* 的定義：引用 II.1, D7。f^* 與 f^{-1} 的差異由 SC 說明。
- 不加入 equalizers/coequalizers、Yoneda、Kan extensions、general representability。

## 習題對照

本篇提供 II.1.9–1.12、1.18、II.2.4–2.6 的語言；具體結果分別由 SC、XL 承擔，不在此聲稱完成這些習題。
