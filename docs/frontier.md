# Frontier 層：缺陷修復與十二個主題的有限可判定實做

日期：2026-11-13。工具鏈：`moon 0.1.20261104 (2026-11-04)` /
`moonc v0.10.20+65efd5b93 (2026-11-05)`（當日最新穩定版，官方
`curl -fsSL https://cli.moonbitlang.com/install/unix.sh | bash` 安裝）。

---

## 1. 新版語法核查（2026-11-05 v0.10.19 / v0.10.20）

官方更新重點：`derive(...)` 後綴改為前置 `#derive(...)` 屬性；
`Int/UInt` 改名 `Int32/UInt32`（舊名仍為別名）；`extenum` 改為
`pub extenum E` + `extenum E += {...}`；新增位元組正則 `reb"..."`、
頂層 `declare let`、`#foo(@pkg.id)` 屬性形式；`Json/ToJson` 移入
`moonbitlang/core/json`。本倉庫此前已全數使用 `#derive` 與
`Int32`，且不使用 `extenum`、regex 字面量與 `to_json`，
故 `moon fmt --check`、`moon check --target wasm/native
--deny-warn` 在新工具鏈下直接零修改通過；僅更新文件與
`bench` 中寫死的工具鏈字串。新增程式碼（`kernel_wbtest`、
`frontier/`）全數以新語法撰寫（`#derive`、`Int32`、頂層輔助
函數而非相互遞迴的局部函數）。

---

## 2. 缺陷：「縮端點誤保留 `parts.base`」

### 2.1 這是什麼問題

`DVGlue` 的合成演算法在合成方向的兩個端點 `j = 0, 1` 處，需要
知道該端點的 Glue 結構 `(system, face, line, base, level)`。當
端點型別本身已經定義性塌縮（generic 點是 Glue、端點是普通型別）
時，`glue_at(line, d)` 只能回報一個假的 parts：`branches = []`、
**`base = line(d)`（即塌縮後的端點型別本身）**。重構端點結構的
`glue_endpoint_parts`（`kernel/kan_ast.mbt`）把 generic Glue 的
分支按端點特化保留下來，卻在舊碼中**無條件寫
`base: parts.base`**：

- 當特化後的定義域面為 **⊤（FTop）** 時，Glue 在該端點定義性
  等於它的*分部型別*（partial type，例如 `ua` 線在 `j = 1` 的
  `dst`），不是它的*底型別*（base `A`）。此時 `parts.base` 是
  分部型別，把它當底型別會使後續在底型別上的
  `comp`/`coe`/校正（correction）hcomp 全部在錯誤型別上進行
  —— 非自同態等價的傳輸會算錯或卡住。
- 當定義域面為 **⊥** 時，Glue 塌縮到底型別，`parts.base`
  本來就等於底型別，保留它無誤。

等價呈現版本 `glue_equiv_endpoint_parts`
（`kernel/equiv_glue.mbt`）此前已按此修復（`FTop` 時取
`generic.base`），但路徑呈現的 `DVGlue` 版遺留了同一缺陷，
且 `comp_glue_value` 的底線 `a_line` 是用
`glue_at(line, j).base` 讀的，在塌縮端點同樣誤讀。

### 2.2 修復（`kernel/kan_ast.mbt`，含迴歸測試）

1. `glue_endpoint_parts`：重構 parts 的 `base` 改為
   「特化定義域面為 ⊤ 時取 `generic.base`（generic Glue 的真
   底型別），否則保留 `parts.base`」，與
   `glue_equiv_endpoint_parts` 完全對稱。
2. `comp_glue_value`：`a_line` 改經
   `glue_endpoint_parts(line, j, dlevel).base` 讀取，使合成全程
   的底分量都在真底型別線上合成（與
   `comp_glue_equiv_value` 的端點感知 `a_line` 一致）。
3. 新增 `kernel/kernel_wbtest.mbt` 迴歸測試：構造 generic 點為
   `Glue [(j = 1) ↦ Nat] Bool`、端點已塌縮的線（及其鏡像）。
   修復前斷言 `glue_endpoint_parts(line, 1, 0).base` 是底型別
   `Bool` 失敗（實得塌縮分部型別 `Nat`），修復後通過；並驗證
   中立元沿此線雙向 `coe` 後在目標型別上可轉換、
   `check_dep_all()`（含計算性單價）仍通過。全倉庫另以
   `grep` 排查其餘 `parts.base` 使用點（`DNUnglueEquiv` 的型別
   本就是底型別、其餘為真 Glue 的欄位讀取），確認無其他
   同型缺陷殘留。

---

## 3. 十二個主題的實做（新套件 `frontier/`）

`frontier/` 位於依賴 DAG 頂層，依賴 `core`／`cubical`／
`derived`／`face_bdd`／`finite`。所有命題都在有限模型中
**窮舉驗證**，`verify_frontier_suite() -> FrontierReport`
逐項匯報，`frontier/frontier_wbtest.mbt` 有 13 個測試。

| 主題 | 檔案 | 模型與驗證要點 |
|---|---|---|
| 德摩根立方體代數 | `cubical_ops.mbt` | 對一階維度項窮舉驗證有界分配格＋對合律、德摩根律、吸收律、三元結合／分配律；非布爾見證 `i∧¬i ≠ 0`；連結端點律 `(i∧j)[j:=0]=0` 等；與面格 `Cof` 蘊含的一致性（extent 語義對照）由 `@face_bdd.dim_eq_demorgan` 交叉核對 |
| 小立方體算子 | `cubical_ops.mbt` | 子立方體碼 `{0,1,*}^n`（`n ≤ 3`）上的面限制 `∂ᵢ^ε`、退化 `sᵢ`、反轉 `¬ᵢ`、連結 `Γ^∧/Γ^∨`（Kleene 三值合併相鄰座標）；窮舉面–面、退化–面移位、反轉–面、連結端點／冪等諸恆等式 |
| 可判定性與合流性 | `cubical_ops.mbt` | 維度項重寫系統（否定下推、常數／冪等／吸收、`/∧` 對 `∨` 分配）＋自寫規範 DNF（子句排序去重、包含吸收；`i∧¬i` 子句保留，因非布爾）；與 `@face_bdd` 判等 oracle 在全部一階項上一致；深度二項的每一對一步歸約都可接合（joinable）、確定性歸約有界步內終止於不可約項 |
| 路徑類型局部可補性 | `path_local.mbt` | 自帶有限預層模型 `MiniTy` 按 `@cubical.path_ty` 同算法過濾高維立方體得路徑型別並交叉核對基數；階段式子集是否為子對象／局部可補（自身與補集皆限制穩定）是有限可判定問題：窮舉判定，常值型別恰有 4 個可補子對象、路徑預層恰有 2 個（空／全），且「僅在 generic 階段出現」的子集被判定為不可補 |
| 形變函子與模塔 | `derived_geo.mbt` | `A₂` 奇點在 Artin 截斷 `F_p[t]/(t^{n+1})` 上的展開函子 `x³ + u(t)x + v(t)`；一階參數 `(u₁,v₁)` 張成 Milnor 代數（以 `@derived.milnor_number` 核對 `μ = τ = 2`）；截斷塔 `Def_{n+1} → Def_n` 滿射、每纖維恰 `p²` 個提升（小素數窮舉編碼計數）、零擴張給出無障礙提升、`|Def_n| = p^{2n}` |
| 衍生纖維積 | `derived_geo.mbt` | 鏈映射以位元組欄位給出並先驗證鏈映射條件；移位衍生纖維積 `S_n = A_{n-1} ⊕ B_{n-1} ⊕ C_n`、`d(a,b,c) = (da, db, f(a)+g(b)+dc)` 建為 `@core.ChainComplex` 並驗證 `d² = 0`；恆等映射例 Betti `[0,1]`（對角拉回），零映射例 `[1,2]`——多出普通纖維積看不見的 Tor 類；圓複形沿點包含的拉回為點 |
| 聯絡與曲率及水平分佈 | `derived_geo.mbt` | 環面格圖 `Z₃×Z₃`、纖維 `Fin m` 的離散聯絡（邊上給纖維置換，反向邊用逆置換）；水平分佈 = 傳輸圖像邊，驗證其對基邊×源纖維點的投影雙射且與豎直邊不交、往返傳輸為恆等；曲率 = 每個小方格的 holonomy：平坦聯絡與規範平凡聯絡（頂點位勢差）全為恆等，磁性聯絡在 `(0,0)` 格給出對換 `[1,0]`（路徑相依的非零曲率） |
| 泛覆疊空間 | `derived_geo.mbt` | 覆疊 `Z → C₆`、`k ↦ k mod 6`：窗口內每點星形投影雙射；長度 6 的全部 64 條步行唯一提升、提升的投影還原原步行、甲板（deck）平移 `6k` 保持投影；閉步行提升端點為 `6 × 繞數`，繞一圈繞數為 1 |
| 高維群胚模型 | `derived_geo.mbt` | 由覆疊提升決定的基本群胚：圓的態射以覆疊正規形 `(src, tgt, lift)` 表示，複合／單位／逆窮舉驗證群胚律；二胞腔存在性 ⇔ 提升端點相等（可判定），繞一圈的環路與恆等之間無二胞腔；環面 `Z₃²` 以 `Z²` 提升位移 `(dx,dy)` 判定：方格換位子 `RULD` 位移 `(0,0)` 有二胞腔（方格填充），`RRR` 位移 `(3,0)` 無 |
| 弱歐米茄群胚 | `logic_nbe.mbt` | 骨架範疇群截斷模型：1-胞腔為群 `Z/m`，2-胞腔為標籤 `Z/m`，結合子由進位 3-上閉鏈 `α(x,y,z) = x·⌊(y+z)/m⌋ mod m` 給出——正規化（單位嚴格）、五邊形（3-上閉鏈條件）對 `m = 2, 3` 全部四元組窮舉，且 `α(1,1,1) = 1 ≠ 0`（真弱性）；3-胞腔為五邊形等式的唯一恆等見證，其上各維皆瘦（thin），是弱 ω-群胚的有限截斷 |
| 伴隨邏輯 | `logic_nbe.mbt` | 有限冪集格上的三組伴隨窮舉：Heyting `a∧b ≤ c ⇔ b ≤ (a⇒c)`；映射 `φ` 的量詞三元組 `∃_φ ⊣ φ⁻¹ ⊣ ∀_φ`；由序關係誘導的 Galois 連接（含單位／餘單位）；伴隨存在性以窮舉搜尋判定——保並的映射由 `g(b) = ⋃{a ∣ f(a) ≤ b}` 公式得到右伴隨，不保並的「頂點偵測器」則搜尋確認無任何單調右伴隨 |
| 符號動態執行與 NbE 整合 | `logic_nbe.mbt` | 對 `@finite.Term` 程式按符號布爾變量逐一分裂具體化（符號執行樹，葉節點記錄以 `Face` 表示的路徑條件），葉上以 `@finite.eval` 動態執行；路徑條件兩兩不交且覆蓋整個立方體（`face_holds` 窮舉核對）；整合命題：每一葉的符號執行結果**逐字等於**該葉閉具體化項的 NbE 範式 `@finite.nf`，且開項 NbE 範式單值（`nbe_single_valued`）；恆等程式的兩條軌跡可區分（路徑敏感）、β-歸約投影程式兩條軌跡同為 `false` |

---

## 4. 驗證方式

```bash
export PATH="$HOME/.moon/bin:$PATH"   # moon 0.1.20261104 / moonc v0.10.20
moon fmt --check                      # 無差異
moon check --target wasm --deny-warn  # 0 錯 0 警
moon check --target native --deny-warn
moon test --target wasm               # 59/59
moon test --target native             # 59/59
moon run --target native bench        # 含 frontier suite: all ok = true
```

測試總數由 44 增至 59：`kernel` 新增 2 個端點缺陷迴歸測試，
`frontier` 新增 13 個主題測試，其餘 44 個原測試不變且全數通過。

## 5. 限制（誠實邊界）

- 所有「定理」都是有限模型內的窮舉驗證（維度項深度 ≤ 2、
  立方體維度 ≤ 3、群胚骨架 `m ≤ 3`、覆疊步行長度 ≤ 6 等），
  與本倉庫一貫風格相同；一般情形的證明以註釋中的數學論證
  給出，程式是其有限截斷的可執行見證。
- 弱 ω-群胚採骨架範疇群的 3-截斷：3-胞腔以上皆瘦，這是該
  骨架模型的標準形態；非骨架的完全弱 ω-結構不在有限模型內。
- 符號執行所語言片段（`@finite`）無布爾消除子，故符號執行樹
  以變量具體化分裂實現路徑敏感性；與 NbE 的一致性是在此
  片段上驗證的逐字相等，而非對任意高階程式的符號語義。
