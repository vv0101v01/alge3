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
- **bench**：可執行基準；**docs/paper.md**：定理、定義、算式與複雜度分析。

## 工具鏈

```text
moon 0.1.20261012 / moonc v0.10.15+943464bfa (2026-10-12)
```

安裝：`curl -fsSL https://cli.moonbitlang.com/install/unix.sh | bash`，然後 `export PATH="$HOME/.moon/bin:$PATH"`。

## 快速開始

```bash
git clone https://github.com/vv0101v01/alge3.git
cd alge3
export PATH="$HOME/.moon/bin:$PATH"
moon test --target wasm        # 44/44
moon test --target native      # 44/44
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

