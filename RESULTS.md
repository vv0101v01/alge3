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

