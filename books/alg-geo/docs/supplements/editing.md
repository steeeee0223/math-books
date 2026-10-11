# 編輯補充教材

修改 `src/sup/*.typ` 時，依本頁處理建構、敘述、引用與檢查。教材分工見 [總覽](README.md)，證明規則見 [ag-proof](../../../../.agents/skills/ag-proof/SKILL.md)。

## 確定內容位置與依賴

1. 搜尋正文與補充教材，確認是否已有相同結果。
2. 若已有結果，引用其主要位置，並列明本次使用的假設。
3. 若新增結果，依數學主題選擇位置，並標明來源習題。
4. 將定義與先備結果排在首次使用之前。篇內證明只使用已介紹的概念與已建立的結果。
5. 拆開各自獨立的命題。Constant sheaves 與 skyscraper sheaves 分別編號，affine-target morphisms 與 initial、terminal objects 也分別編號。

## 寫出建構與既有定義

1. 若正文已有定義，引用該處，直接列出本篇要用的性質。SC-1 引用 II.1, D5\~D7，不再重述 subsheaf、quotient、kernel、image、cokernel 與 exactness 的定義。
2. 若在本篇定義 sheaf，先說明定義的對象，並用斜體標出名稱。採用 `Define the _… sheaf_ … to be the sheafification of the presheaf …` 的句型，接著寫 open set 的對應與 restriction maps。
3. 若該 presheaf 已是 sheaf，接著寫明 `This presheaf is already a sheaf.`，無須另加證明。需要讀者自行核對時可加 `Check!`。
4. 將 stalk formulas、universal properties 與其他性質列在建構之後。
5. 若某項比較不成立，列出反例或足以使比較成立的條件。

沿用 Hartshorne 的 sheaf 記號。`ops.im u` 表示 image sheaf。若證明需要命名 image presheaf，使用 `(ops.im u)^-`。Kernel 與 cokernel 也採相同區別。

在 exactness calculus 中，依序列出 subsheaf 與 quotient、kernel 與 image 及 cokernel、morphism criteria、exact sequences。若 exactness 已在正文定義，引用該定義，再列 canonical short exact sequence。

區分 direct limit 與 inverse limit。Direct limit 使用 `ops.colim` 與 colimit universal property，inverse limit 使用 `lim` 與 limit universal property。Stalks 與任意 colimits、finite limits 交換。Noetherian 空間上的 sectionwise direct-limit presheaf 已是 sheaf 的結論，須有 filtered diagram 的假設。

## 區分建構與性質

1. 將動機與用途寫在 formal block 之前或之外。
2. 對有多項性質的主題，使用簡短斜體標籤，例如 `_Kernel, image & cokernel._`。建構標籤後仍須說明定義的對象，不能只列名稱或寫 `Put` 加公式。
3. 若 parent item 只用來分組，寫一段短摘要，例如 `Adjunction of direct and inverse image.`，並將數學斷言移入 subitems。
4. 將性質列在第二層，不再增加層級。Stalk formulas 先用文字說明對象，例如 `The stalk of the direct image sheaf is …`，避免只列公式。
5. 若一段內容不需要分組，直接寫成同一 item。不要為一句補充說明另設 subitem，也不要為每個 item 強加標籤。
6. 若列出多個等價條件，先寫 `The following conditions are equivalent:`，再用 bullet list 分列條件，如 SC-1 的 injectivity 與 surjectivity criteria。
7. 對反例，先列空間、sheaves 與 morphisms，再分列性質與失敗的比較。只有一句結論時，保留單一敘述。

## 核對 Typst 記號

1. 沿用 [symbols package](../../../../packages/steee-book/symbols/0.1.0/lib.typ) 匯入的記號。新增記號前，依 ag-proof 提出用途與寫法。
2. 在 formal statements 中，以文字表達量詞，不使用 `forall`、`exists` 或 `exists.not`。
3. 用文字表達「if and only if」，或在 display math 中使用對齊的 `arrow.l.r.double`。不要使用 `arrow.l.r`。
4. 若要印出 quotient slash，使用 `\/`。保留 `/` 給分數。
5. 核對內容記號後的括號。獨立寫 section 時使用 `shf.f\(U)`，在函數參數內可使用 `shf.f (U)`。
6. 編譯後檢查 quotient、括號、下標與長公式，不只檢查原始碼。

對齊的等價式可寫為：

```typst
$
	s=t & arrow.l.r.double s|_(U_i)=t|_(U_i) " for every " i \
	    & arrow.l.r.double s_x=t_x " for every " x in U.
$
```

## 核對編號與引用

1. 用 `#supplement-numbering("RV")` 設定篇章代號。讓區塊依出現次序編號。
2. 在區塊使用 `key` 設定引用目標，並以 `title` 設定標題。
3. 用 `#supplement-link(<sup-rv-2>)[RV-2]` 引用補充結果，用 `#book-link` 引用正文。
4. 若調整區塊順序，同步更新正文、習題入口、Lean comments 與本目錄中的編號。
5. 核對每個引用目標存在且唯一。獨立預覽可能只顯示引用文字，不能據此判定目標有效。

現行區塊寫法如下：

```typst
#proposition(key: "sup-rv-2", title: "Universal property")[
	// Statement body.
]
```

從 repository root 列出收錄次序、篇章代號與區塊：

```sh
rg '^#include ' books/alg-geo/src/sup/sup.typ
rg '^#supplement-numbering|^#(definition|lemma|proposition|theorem|corollary|example|remark)\(key:' books/alg-geo/src/sup/*.typ
```

## 檢查變更

1. 依 statement 的順序與分組安排 proof。先證明本組使用的結果，再處理後續性質；不引用同篇尚未建立的結果。
2. 若改動證明，更新對應 Lean companion，並依 ag-proof 核對約化與終端斷言。
3. 編譯主書。若需要查看單篇排版，再編譯該篇。
4. 對每個受影響的 companion 執行 Lean 檢查。
5. 核對引用、篇內依賴與 diff。
6. 若變更內容位置、涵蓋範圍或驗證缺口，同步更新 [習題對照](exercise-coverage.md) 與 [形式驗證狀態](verification-status.md)。
7. 記錄檢查日期、檔案、結果與尚缺的證明。區分完整命題的驗證與部分約化的驗證。

從 repository root 執行以下指令，將 `<name>` 換成受影響的檔名：

```sh
typst compile --root . --package-path packages books/alg-geo/src/main.typ /tmp/math-books-alg-geo.pdf
typst compile --root . --package-path packages books/alg-geo/src/sup/<name>.typ /tmp/<name>.pdf
lake env lean books/alg-geo/src/sup/lean/<name>.lean
git diff --check
```
