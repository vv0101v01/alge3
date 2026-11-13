# 基準與數學輸出（2026-10-18，含 cubical）

環境：Linux x86_64 sandbox；`moon 0.1.20261012` / `moonc v0.10.15+943464bfa`；native target；單調時鐘，5 次平均；資料決定性（固定 LCG 種子）。

## 1. 基準

```text
rank 512x512 us: bitset 24320.57, scalar 1102769.07, speedup 45.34
matmul 256 us: bitset 4012.41, scalar 393442.51, speedup 98.06
bar construction BZ/2 degree 8 us: 5519.14
surjection operad E(4) through degree 3 us: 243959.78
Wick 16-point us: DP 12481.04, brute 592151.82, speedup 47.44
Milnor number E8 us: 268.71
Heisenberg commutator check us: 14242.02



```

## 2. 同調與結構

```text
S^2: V=4 E=6 F=4 chi=2 beta=[1, 0, 1]
T^2: V=9 E=27 F=18 chi=0 beta=[1, 2, 1]
RP^2: V=6 E=15 F=10 chi=1 beta=[1, 1, 1]
Mobius: V=6 E=15 F=9 chi=0 beta=[1, 1, 0]


BZ/2 betti: [1, 1, 1, 1, 1]
bar Z/2 through 7: [1, 1, 1, 1, 1, 1, 1, 1]
E(4) betti: [1, 0, 0, 0]
A-infinity exterior algebra OK: true
A-infinity line dga OK: true
Heisenberg character p(0..8): [1, 1, 2, 3, 5, 7, 11, 15, 22]
Milnor A2: 2
Milnor E8: 8
Tjurina E7: 7
Kronecker Ext^0, Ext^1: 1, 1
```

## 3. 測試

```text
moon test --target wasm
Total tests: 44, passed: 44, failed: 0.
moon test --target native
Total tests: 44, passed: 44, failed: 0.
```

- core：5
- homotopy：8
- algebra：11
- derived：7
- cubical：13（新）

## 4. 解讀

- **位並行**：rank 與 matmul 的加速接近 64 位理論上限（約 43–45×、98–102×；後者受記憶體與密度影響）。這是精確運算，不是近似。
- **Wick DP**：16 點（8 對）時 DP 已勝過樸素配對列舉；點數再大時 \((2n-1)!!\) 爆炸，DP 仍是 \(O(n^2 4^n)\)。
- **E(4)** 的 194–244 ms 主要花在列舉非退化 surjection 與逐度 Gaussian 消去；`e_words` 的列舉是 \(r^{r+d}\)，可用表格化再降。
- **立方體單價**：uaβ 對 Fin 6 的全部 720 個等價窮舉驗證約 6.9 ms（每個等價約 10 μs：一次 Glue 線構造＋逐點 comp）；$\mathcal U$ 中一次路徑複合（comp）約 55 μs；麵格蘊含判定每次重算 729 個子立方體的外延，約 300 μs，可快取外延再降。
- **BZ/3** 的正度同調為 0 是正確的：\(H_1=\mathbb Z/3\otimes\mathbb F_2=0\)，其餘由萬有係數定理消失；不要把它「修正」成週期 2。

---

## 5. 更新紀錄（2026-11-13 流水式追加，保留全部舊文）

### 5.1 模組歸位、依賴清除與符號衝突消解

- 14 份原根目錄 `.mbt` 檔案已完整歸位為 12 套件 DAG 架構（`core`/`cube`/`face_bdd` → `algebra`/`derived`/`cubical`/`finite` → `kernel` → `homotopy` → `autonomy` → `structures`/`bench`），外部未授權套件依賴（`@gcd`、`@swar`、`@sym`、`@topos`）已全面移除或純本地 `BigInt`/套件實作替代。
- 6 處潛在跨套件符號重名（`int_pow`、`glue_at`、`partial_empty`、`Iso`/`ua`、`Term`、`PolyTerm`）已透過獨立套件邊界與命名隔離徹底清除。

### 5.2 計算性單值性補齊與全代碼健檢結果

- **單值性完整閉環（`kernel/equiv_glue.mbt`、`kan_ast.mbt`、`nbe_dep.mbt`、`specs_levels.mbt`、`homotopy/circle_hit.mbt`、`structures/glue_hae_universe_classifier.mbt`）**：
  - 修復 `glue_equiv_endpoint_parts` 於 `FTop` 面塌縮時保留錯誤基底的問題，並以雙端 CCHM `ua_type_at` 搭配 `glue_collapse` 確保所有端點與非自同態傳輸嚴格可算。
  - 新增 `DTerm::DPathToEquiv` 語法與型別檢查／求值路徑，並實作 `path_to_equiv_value`、`ua_beta_path_value`、`ua_beta_inv_path_value`、`ua_id_path_value`、`ua_eta_path_value`、`path_to_equiv_ua_beta_path_value` 與一等單值性等價 `univalence_equiv_value`。
  - 於 `@kernel.check_computational_univalence` 針對閉合（`Bool`）及開放中立上下文（`A, B : U`, `e : Equiv A B`, `x : A`, `y : B`, `p : Path U A B`）實測所有單值性 `β/η/id` 等式全數通過；於 `@structures.verify_glue_hae_and_universe_classifier_suite` 擴大驗證雙向 `ua(not) ⬝ ua(not)` 與跨型別 `Bool ≃ Lift(Bool)`。
- **全代碼健檢與清理**：
  - `moon check --target wasm` 與 `--target native` 均為 **0 錯誤、0 警告**（已補全 `algebra/monad.mbt` `Term` 之 `Debug`/`Eq` pub extend 消解 `[0079]`）。
  - 完成去重與死碼清除：`voa.mbt`、`face_bdd.mbt`、`kan_dep.mbt`、`univalence_wbtest.mbt`、`circle_hit.mbt`、13 處空 `///|` 塊、7 處 `ignore(...)` 及死局部變數 `off_big`／`pt`。
- **規模統計與最終實測**：
  - 全專案共 **52 份 `.mbt` 檔**（合計 **25,716 總行數**、**20,911 純代碼行**、**936 個公開函式**、**231 個私有函式**、**44 個單元測試**、**32 個執行期數學檢查器 `check_*`/`verify_*`**），連同專案設定／文件／生成介面檔共 **87 份倉庫非建置檔案**。
  - `moon fmt --check`、`moon test --target wasm`（44/44）、`moon test --target native`（44/44）、`moon run --target native bench` 及所有 32 個執行期定理檢查器全數通過。
  - 統計報表已匯出至 `alge3_stats_report.xlsx`（緊湊多工作表排版，欄寬精簡不橫溢）。

---

## 6. 更新紀錄（2026-11-13 流水式追加：工具鏈升級、端點缺陷修復、frontier 十二主題）

環境：Linux x86_64 sandbox；`moon 0.1.20261104`／`moonc v0.10.20+65efd5b93`；native target。

### 6.1 基準（本次實測節選）

```text
rank 512x512 us: bitset 28195.65, scalar 1309529.66, speedup 46.44
matmul 256 us: bitset 3870.51, scalar 407948.96, speedup 105.40
bar construction BZ/2 degree 8 us: 5924.76
surjection operad E(4) through degree 3 us: 247664.09
Wick 16-point us: DP 15270.50, brute 688384.29, speedup 45.08
Milnor number E8 us: 326.66
ua-beta exhaustive Fin 6 (720 equivs) us: 6844.27
comp in U x50 (Fin 6 lines) us: 2819.69
frontier small cubical operators check us: 1254.11
```

### 6.2 缺陷修復與測試

- 修復 `kernel/kan_ast.mbt` `glue_endpoint_parts`（`DVGlue`）於 `FTop` 塌縮端點誤保留 `parts.base` 之缺陷（改取 `generic.base`；非 ⊤ 端點保留 `parts.base`），並使 `comp_glue_value` 的底線 `a_line` 端點感知；與已修復之 `glue_equiv_endpoint_parts` 對稱。迴歸測試 `kernel/kernel_wbtest.mbt`：修復前 1 項斷言失敗（`base` 實得塌縮分部型別 `Nat` 而非底型別 `Bool`），修復後通過。

```text
moon test --target wasm
Total tests: 59, passed: 59, failed: 0.
moon test --target native
Total tests: 59, passed: 59, failed: 0.
```

- 新增：`kernel` 2 項、`frontier` 13 項；原有 44 項不變。

### 6.3 frontier 數學輸出（`moon run --target native bench` 節選）

```text
frontier suite all ok: true
derived pullback betti (shifted): [0, 1]
magnetic plaquette holonomy: [1, 0]
complemented subobjects of const Bool presheaf: 4
```

十二主題（德摩根立方體代數、小立方體算子、可判定性與合流性、路徑類型局部可補性、形變函子與模塔、衍生纖維積、聯絡與曲率及水平分佈、泛覆疊空間、高維群胚模型、弱歐米茄群胚、伴隨邏輯、符號動態執行與 NbE 整合）的定義、模型與驗證方法見 `docs/frontier.md`；套件程式為 `frontier/{cubical_ops,path_local,derived_geo,logic_nbe,frontier}.mbt`，測試為 `frontier/frontier_wbtest.mbt`。

---

## 7. 更新紀錄（2026-11-13 流水式追加：大立方體 → 3 維）

- 新增 `frontier/hypercube3d.mbt` 與 `frontier/hypercube_wbtest.mbt`（8 項），互動頁 `docs/hypercube3d.html` 與專文 `docs/hypercube3d.md`。
- 管線：$I^n$ 胞腔複形 →（單對象 A∞ 模型 $m_1$）頂邊界 $z_n$ → 循環同調（$\rho$ 循環雙複形，$z_n$ 不變）→ 纖維積分 $\pi_!$ → $z_3=\partial[I^3]$ → 單值等價 `ua` transport 到 3 維影子類型；n=3,4,5 全驗，頂點纖維 $2^{n-3}$。

```text
moon test --target wasm
Total tests: 67, passed: 67, failed: 0.
moon test --target native
Total tests: 67, passed: 67, failed: 0.
hypercube3d pipeline ok: true
big cube I^5 solid betti: [1, 0, 0, 0, 0, 0]
top boundary dI^5 (= S^4) betti: [1, 0, 0, 0, 1]
cyclic homology betti (low, n=5): [1, 0, 0, 0]
projected top boundary facets pi_!(z_5): 6
hypercube3d full check us: ~111326
```

- 附帶修復 `Bits::xor_inplace` 跨字長越界（短操作數零擴展）。

---

## 8. 更新紀錄（2026-11-13 流水式追加：spectral nexus）

- 新增 `frontier/nexus_fft.mbt`、`frontier/nexus_geo.mbt`、`frontier/nexus_wbtest.mbt`（11 項），互動頁 `docs/nexus_fft.html` 與專文 `docs/nexus.md`（十個短語逐個標明有限模型解讀）。

```text
moon test --target wasm
Total tests: 78, passed: 78, failed: 0.
moon test --target native
Total tests: 78, passed: 78, failed: 0.
spectral nexus all ok: true
butterfly ops (n=16): 32
line bundles over C4 iso classes (monodromy): 4
trefoil determinant: 3
spectral nexus full check us: ~360966
```
