# moonmath — 編譯期導出數學（MoonBit）

[![CI](https://github.com/vv0101v01/alge3/actions/workflows/ci.yml/badge.svg)](https://github.com/vv0101v01/alge3/actions/workflows/ci.yml)
[![License: Apache-2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE)

Repository: <https://github.com/vv0101v01/alge3>

以 MoonBit 由零實作的有限、可驗證高階數學引擎：

- **core**：GF(2) 位元向量與位並行線性代數（rank、Boolean 矩陣乘）、鏈複形、持久同調、有限體 `F_p`。
- **homotopy**：單純複形與三角剖分（S¹、S²、T²、RP²、Möbius）、內角填充（擬範疇）、么半群神經／棒複形、span/correspondence 合成。
- **algebra**：自由 Monad 與 substitution、Eilenberg–Moore fold、常數摺疊、A∞（Stasheff）、E∞（surjection operad 可縮性）、VOA（Heisenberg 模式、Wick DP、特徵標、rank variety）。
- **derived**：加權齊次奇點的 Milnor／Tjurina 數與 Hilbert 函數（ADE）、箭圖表示的 Ext⁰/Ext¹。
- **cubical**：把單價公理變成立方體演算法——區間的 De Morgan 代數、面格、Glue 類型、comp/hcomp/transp、$\mathsf{ua}$ 與 uaβ 計算（有限立方體模型，專文 `docs/cubical.md`）。
- **frontier**：十二個主題的有限可判定模型——德摩根立方體代數與小立方體算子、重寫可判定性與合流性、路徑類型局部可補性、形變函子與模塔、衍生纖維積、聯絡與曲率及水平分佈、泛覆疊空間、高維群胚模型、弱歐米茄群胚、伴隨邏輯、符號動態執行與 NbE 整合（專文 `docs/frontier.md`）。
- **bench**：可執行基準；**docs/paper.md**：定理、定義、算式與複雜度分析。

## 工具鏈

```text
moon 0.1.20261104 / moonc v0.10.20+65efd5b93 (2026-11-04)
```

安裝：`curl -fsSL https://cli.moonbitlang.com/install/unix.sh | bash`，然後 `export PATH="$HOME/.moon/bin:$PATH"`。

## 快速開始

```bash
git clone https://github.com/vv0101v01/alge3.git
cd alge3
export PATH="$HOME/.moon/bin:$PATH"
moon test --target wasm        # 59/59
moon test --target native      # 59/59
moon run --target native bench # 數學摘要 + 基準
```

或者一鍵跑齊（會自動安裝工具鏈）：

```bash
./scripts/check.sh
```

## 基準（native，5 次平均）

| 項目 | 位並行／DP | 純量／樸素 | 加速 |
|---|---|---|---|
| GF(2) rank 512×512 | 23.8–24.3 ms | 1.03–1.10 s | **43–45×** |
| Boolean matmul 256³ | 3.1–4.0 ms | 315–393 ms | **98–102×** |
| Wick 16 點 | 12.5 ms | 517–592 ms | **41–47×** |
| BZ/2 至度 8 | 4.6 ms | — | — |
| E(4) 至度 3 | 194–244 ms | — | — |
| Milnor E₈ | 0.22–0.27 ms | — | — |
| uaβ 窮舉 Fin 6（720 等價） | 6.9 ms | — | — |
| $\mathcal U$ 中 comp ×50 | 2.8 ms | — | — |
| 面格蘊含 n=6 ×200 | 60 ms | — | — |

## 數學結果（節選）

- `S²: V=4 E=6 F=4 χ=2 β=[1,0,1]`
- `T²: V=9 E=27 F=18 χ=0 β=[1,2,1]`
- `RP²: V=6 E=15 F=10 χ=1 β=[1,1,1]`（F₂ 係數；RP² 不可定向）
- `Möbius: V=6 E=15 F=9 χ=0 β=[1,1,0]`
- `BZ/2` 的 F₂ 同調：每個度數維度 1（週期性）
- `BZ/3`：`[1,0,0,0,0]`（3 在 F₂ 可逆）
- Surjection operad `E(4)`：`[1,0,0,0]`（可縮）
- A∞ 三例全部通過 `m₁²=0`、Leibniz、Stasheff m₃
- Heisenberg 特徵標係數：`1,1,2,3,5,7,11,15,22`
- ADE：A₁=1、A₂=2、A₄=4、D₄=4、E₆=6、E₇=7、E₈=8（μ=τ）
- Kronecker (1,1)：Ext⁰=1、Ext¹=1
- `transport (ua e) = e`（uaβ）：Fin 3、Fin 4 全部等價窮舉成立；`idtoeqv` 與 `ua` 兩邊來回程成立
- 沿 `ua(not)` 搬運布爾運算：AND → OR、OR → AND、XOR → XNOR（De Morgan 由 comp 計出）

## 文件

- 完整論文：`docs/paper.md`（HTML 版 `docs/paper.html`：單檔、公式內嵌成 SVG、無任何外部請求，離線可讀）。
- 基準原始輸出與說明：`RESULTS.md`。
- 方法論、定理、複雜度分析：論文 §1–§7；實作驗證 §8；限制 §9；立方體單價 §10。
- 立方體單價專文：`docs/cubical.md` / `docs/cubical.html`（定義、Glue/comp/ua 公式、有限單價定理及證明、複雜度）。

## 專案結構

```text
core/       GF(2) 位元向量、位並行線性代數、鏈複形、持久同調、F_p
homotopy/   單形複形、內角填充、神經／棒複形、correspondence
algebra/    自由 Monad、A∞、E∞（surjection operad）、VOA
derived/    Milnor／Tjurina、Hilbert 函數、箭圖 Ext
cubical/    區間/面格、CubeTy、Glue、comp、ua（立方體單價）
kernel/     依賴 NbE、Kan 運算、Glue/等價與計算性單價
frontier/   形變/衍生纖維積/聯絡曲率/覆疊/群胚/伴隨/NbE 整合（見 docs/frontier.md）
bench/      可執行基準（moonbitlang/core/bench）
docs/       paper.md / paper.html、cubical.md / cubical.html
scripts/    check.sh
```

執行 `moon test` 時每個 package 的 `*_wbtest.mbt` 即為對應定理的可執行版本（44 個測試）。

## 2026 MoonBit 語法注意

- `trait`/`impl` 方法要 `fn`；泛型寫 `fn[T] f`。
- `Int` = `Int32`；`UInt64` 用 `UL`。
- `moon.pkg` DSL；`using @pkg { type T, value }`；`using` 塊不接受 `fn`。
- 範圍 `for i in (a + 1)..<n` 要括號。
- 熱路徑已標 `#inline`；測試以 `moon test --target wasm` 執行。

---

## 更新紀錄（2026-11-13 流水式追加，保留全部舊文）

### 階段一：根目錄 14 份模組歸位與依賴清理

原根目錄 14 份獨立 `.mbt` 檔案已完成符號衝突排查、移除／本地替代外部依賴（`@gcd`、`@swar`、`@sym`、`@topos` 等），並歸位至 12 個無環套件階層中：

- **符號衝突與套件拆分**：14 份檔案彼此與檔名零碰撞；對直接併入舊套件時會發生的 6 處符號碰撞（`int_pow`、`glue_at`、`partial_empty`、`Iso`/`ua`、`Term`、`PolyTerm`），透過設立獨立套件 `cube/`、`face_bdd/`、`finite/`、`kernel/`、`autonomy/`、`structures/`，以及將無碰撞模組併入 `algebra/`（`symalg.mbt`、`qpoly.mbt`、`qmat.mbt`）與 `homotopy/`（`cubical_algorithms.mbt`、`circle_hit.mbt`）徹底消弭。
- **新增／擴充套件目錄**：
  - `algebra/`：新增 `symalg.mbt`、`qpoly.mbt`、`qmat.mbt`（純 `BigInt` 有理多項式與精確矩陣演算法）
  - `cube/`：`cube.mbt`、`complex.mbt`
  - `face_bdd/`：`face_bdd.mbt`（維度、面公式、自由 De Morgan DNF、ROBDD）
  - `finite/`：`nbe.mbt`、`nbe_eta.mbt`、`pathp_glue.mbt`、`wiring.mbt`
  - `kernel/`：`nbe_dep.mbt`、`kan_ast.mbt`、`kan_dep.mbt`、`specs_levels.mbt`、`inductive_hit.mbt`、`equiv_glue.mbt`、`dcube.mbt`
  - `homotopy/`：新增 `cubical_algorithms.mbt`、`circle_hit.mbt`
  - `autonomy/`：`poset_sieve.mbt`、`affine_bide_morgan_cubical.mbt`
  - `structures/`：`glue_hae_universe_classifier.mbt`

### 階段二：補齊計算性單值性（Computational Univalence）、全代碼健檢與統計報告

- **計算性單值性完整補齊（`kernel/` + `homotopy/` + `structures/`）**：
  - 修正 `kernel/equiv_glue.mbt` 中 `glue_equiv_endpoint_parts` 於 `FTop` 塌縮端點誤保留 `parts.base` 之缺陷，確保非自同態等價 $A \simeq B$ 之 `coe (ua e) 0 1` 正確計算。
  - 將 `ua_type_at` 升級為雙端 CCHM 形式 `Glue dst [(i=0, src, e), (i=1, dst, idEquiv dst)]`。
  - 補齊並公開完整單值性構造與等式見證：語法與推理項 `DTerm::DPathToEquiv`（含 `eval_path_to_equiv_term`、`infer_path_to_equiv`、`dterm_conv_plausible`、`dterm_children`、`glue_collapse`），以及語義構造 `path_to_equiv_value`、`ua_beta_path_value`、`ua_beta_inv_path_value`、`ua_id_path_value`、`ua_eta_path_value`（含 `sq_cchm` 與中立類型 $B$ 情況下於 $\mathcal U$ 之 `hcomp` 橋接 `sq_bridge`）、`path_to_equiv_ua_beta_path_value` 與一等單值性等價 `univalence_equiv_value : Equiv (Equiv A B) (Path U A B)`。
  - 將 `homotopy/circle_hit.mbt` 重複的 `path_to_equiv_value`、`ua_beta_path_value` 委派至 `@kernel`，並擴充 `@kernel.check_computational_univalence`（由 `check_dep_all` 自動執行，覆蓋閉合與開放中立上下文 $A, B : \mathcal U$）與 `@structures.verify_glue_hae_and_universe_classifier_suite`。
- **全代碼健檢、除錯、去重、減債與清死碼**：
  - 為 `algebra/monad.mbt` `Term` 補齊 `pub extend Term with Debug / Eq`，消除全部 `[0079]` 警告。
  - 去重與刪除死碼：移除 `algebra/voa.mbt` 重複 `pow_int_local`（共用 `pow_int`）、`face_bdd/face_bdd.mbt` 重複 `sort_lit_conj`/`bdd_face_eq`（改用 `sort_ints`/`face_eq_mod`）、`kernel/kan_dep.mbt` 重複 `dv_is_bool`（改用 `dv_is_bool_dep`）、`cubical/univalence_wbtest.mbt` 重複 `some_or2`/`iso_exn2`（改用 `some_or`/`iso_exn`）；清除 13 處空 `///|` 文檔塊；移除 `cubical/comp.mbt`、`cubical/cubety.mbt`、`homotopy/cubical_algorithms.mbt`、`kernel/kan_ast.mbt` 共 7 處無效 `ignore(...)` 與死變數 `off_big`／`pt`。
- **全數通過狀態**：`moon fmt --check`、`moon check --target wasm/native`（0 錯 0 警）、`moon test --target wasm/native`（44/44）、`moon run --target native bench` 及全部 12 套件 `check_*`/`verify_*` 執行期定理套件皆通過；已產出緊湊欄寬 `.xlsx` 統計報告（`alge3_stats_report.xlsx`）。

### 階段三：最新穩定版工具鏈、端點 `parts.base` 缺陷修復、frontier 十二主題實做

- **工具鏈升級**：安裝最新穩定版 `moon 0.1.20261104 / moonc v0.10.20+65efd5b93 (2026-11-04)`；核查 2026-11 新語法（`#derive` 前置屬性、`Int32/UInt32`、`extenum` 新式、`reb"..."`、`declare let`、`Json` 遷移）後確認本倉庫已相容，`moon fmt --check`、`moon check --deny-warn`（wasm/native）零修改通過，僅更新工具鏈字串（`bench` 與本文件）。
- **缺陷修復（縮端點誤保留 `parts.base`）**：`kernel/kan_ast.mbt` 的 `DVGlue` 版 `glue_endpoint_parts` 在重構已塌縮端點的 Glue 結構時無條件保留 `parts.base`——當特化定義域面為 `FTop` 時該值是塌縮後的分部型別而非 Glue 的底型別（`DVGlueEquiv` 版此前已修、`DVGlue` 版遺留）。已改為面為 ⊤ 時取 `generic.base`、否則保留 `parts.base`，並將 `comp_glue_value` 的底線 `a_line` 改經端點感知的 `glue_endpoint_parts` 讀取；新增 `kernel/kernel_wbtest.mbt` 兩項迴歸測試（修復前失敗、修復後通過）。詳見 `docs/frontier.md` §2。
- **新套件 `frontier/`（DAG 頂層，依賴 core/cubical/derived/face_bdd/finite）**：以有限窮舉模型實做並驗證——德摩根立方體代數、小立方體算子（面／退化／反轉／連結）、維度項重寫之可判定性與合流性、路徑類型局部可補性（`MiniTy` 預層判定）、形變函子與模塔（`A₂` 展開、`μ=τ=2`、截斷塔纖維 `p²`）、衍生纖維積（移位複形、Tor 修正 Betti）、聯絡與曲率及水平分佈（環面格聯絡、磁性格 holonomy 為對換）、泛覆疊空間（`Z → C₆` 唯一提升與繞數）、高維群胚模型（覆疊提升決定的 `S¹`／`T²` 基本群胚）、弱歐米茄群胚（骨架範疇群攜帶進位 3-上閉鏈結合子，五邊形窮舉）、伴隨邏輯（Heyting／量詞三元組／Galois 連接及伴隨存在性判定）、符號動態執行與 NbE 整合（路徑條件分割、每葉軌跡等於 NbE 範式）。`verify_frontier_suite()` 逐項匯報全數通過。
- **全數通過狀態（更新）**：`moon test --target wasm/native` 由 44/44 增至 **59/59**（kernel +2、frontier +13），`moon run --target native bench` 新增 frontier 匯報（`frontier suite all ok: true`、衍生拉回 Betti `[0, 1]`、磁性格 holonomy `[1, 0]`、可補子對象計數 `4`）。

### 階段四：大立方體到 3 維——A∞ 頂邊界、循環同調、單值等價影子

- **新模組 `frontier/hypercube3d.mbt`（+ `frontier/hypercube_wbtest.mbt` 8 項測試）**：把高維「睇唔見」問題做成可驗證的降維管線——大小立方體胞腔複形（面編碼、實心 Betti `[1,0,…]`、頂邊界 Betti 即 $S^{n-1}$、小立方細分的內部面相消）；單對象 A∞ 模型中 $m_1$（胞腔邊界）作用於頂胞腔給出頂邊界 $z_n$（$\partial z_n=0$，A∞ 證書建至 n=3、組合複形驗至 n=5）；循環同調由座標循環輪換 $\rho$ 的 $(1-\rho, N)$ 循環雙複形計算（$z_n$ 為 $\rho$-不變循環循環，低度數 Betti：n=3 為 `[1,0,1,0]`、n=5 為 `[1,0,0,0]`）；纖維積分 $\pi_!$（面存活 ⟺ 遺忘部分為整條纖維 $I^{n-3}$，鏈映射逐面驗）嚴格給出 $\pi_!(z_n)=z_3$（6 個面）；影子面／頂點類型與 $I^3$ 對應類型間的顯式等價經 `ua` 變成有限宇宙路徑，transport 計算回等價本身（uaβ 與往返皆驗）。頂點纖維大小恆為 $2^{n-3}$。
- **互動可視化 `docs/hypercube3d.html`**：單檔零依賴畫面，可調 n=3..7、旋轉高維投影線框、開關頂邊界影子 $\partial I^3$、2×2×2 小立方細分與纖維高亮；專文 `docs/hypercube3d.md` 說明管線與誠實邊界（等價是纖維積分／商集與循環截斷後的影子類型之間，相機僅為顯示）。
- **附帶修復**：`core/bitset.mbt` 的 `Bits::xor_inplace` 在兩操作數字長不同（維度跨 64 位邊界）時會讀越界，改為短操作數零擴展；立方體複形的 $d^2=0$ 改以精確位長自有檢查逐列驗證。
- **全數通過狀態（更新）**：`moon test --target wasm/native` 增至 **67/67**（frontier 13→21），`moon run --target native bench` 新增 hypercube 匯報（`hypercube3d pipeline ok: true`、$I^5$ 實心 Betti `[1,0,0,0,0,0]`、頂邊界 Betti `[1,0,0,0,1]`、循環 Betti `[1,0,0,0]`、投影後頂邊界面數 `6`、全檢查約 111 ms）。

### 階段五：穩定光譜蝶形 FFT 與九個幾何／範疇有限模型（nexus）

- **新模組 `frontier/nexus_fft.mbt` + `frontier/nexus_geo.mbt`（+ `nexus_wbtest.mbt` 11 項）**：把十個短語落實為精確有限模型——穩定光譜束聯快葉 FFT（有限域 NTT $p=998244353$：蝶形／遞歸葉／樸素 DFT 三方互驗、位移定理、Parseval、卷積）；同倫環空間模切雙射（繞數 ↔ 覆疊提升甲板端點、$w\bmod 4\mapsto 6w\bmod 24$）；愛因斯坦 boost 範疇（$\mathbb F_{13}$ 上 12 個洛倫茲態射、速度加法、Minkowski 區間不變）；格與構重構（Birkhoff：$B_3$ 與約數格 $D(12)$ 由 join-不可約元重構）；超方體全對偶／黎曼／超分次／對蹠折（$n=4$ 面對偶反轉包含、$n=5$ 加權圖距離 = 加權曼哈頓、奇偶分次、32 頂點折 16 對）；穩定自旋算子（$Cl(2)$ 12 轉子、保範、雙覆蓋核 $\{\pm1\}$）；葉子遞歸樹同態幾何（四點條件、剪枝 1-Lipschitz、fold 同態）；全映射收斂（256 個 $\mathrm{Fin}\,4$ 映射 $f^{16}=f^4$、冪等 41、雙射 24、逆像纖維劃分）；向量束範疇特徵（$C_4$ 線束以單值分類、同構類 4）；結同調行列式（unknot 1、三葉 3、八字 5）與循環蝶形 FFT。解讀方式逐節寫明於 `docs/nexus.md`。
- **互動可視化 `docs/nexus_fft.html`**：蝶形合并逐步動畫（葉子位元反轉 → 逐級縫合 → 頻譜），附來回／Parseval／位移定理即時誤差與 MoonBit 實算對照表。
- **全數通過狀態（更新）**：`moon test --target wasm/native` 增至 **78/78**（frontier 21→32），`bench` 新增 nexus 匯報（`spectral nexus all ok: true`、蝶形運算 32、線束同構類 4、三葉行列式 3、全檢查約 361 ms）。
