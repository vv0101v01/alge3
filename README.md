# moonmath — 編譯期導出數學（MoonBit）

[![CI](https://github.com/vv0101v01/alge3/actions/workflows/ci.yml/badge.svg)](https://github.com/vv0101v01/alge3/actions/workflows/ci.yml)
[![License: Apache-2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE)

Repository: <https://github.com/vv0101v01/alge3>

以 MoonBit 由零實作的有限、可驗證高階數學引擎：

- **core**：GF(2) 位元向量與位並行線性代數（rank、Boolean 矩陣乘）、鏈複形、持久同調、有限體 `F_p`。
- **homotopy**：單純複形與三角剖分（S¹、S²、T²、RP²、Möbius）、內角填充（擬範疇）、么半群神經／棒複形、span/correspondence 合成。
- **algebra**：自由 Monad 與 substitution、Eilenberg–Moore fold、常數摺疊、A∞（Stasheff）、E∞（surjection operad 可縮性）、VOA（Heisenberg 模式、Wick DP、特徵標、rank variety）。
- **derived**：加權齊次奇點的 Milnor／Tjurina 數與 Hilbert 函數（ADE）、箭圖表示的 Ext⁰/Ext¹。
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
moon test --target wasm        # 31/31
moon test --target native      # 31/31
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

## 文件

- 完整論文：`docs/paper.md`（HTML 版 `docs/paper.html`：單檔、公式內嵌成 SVG、無任何外部請求，離線可讀）。
- 基準原始輸出與說明：`RESULTS.md`。
- 方法論、定理、複雜度分析：論文 §1–§7；實作驗證 §8；限制 §9。

## 專案結構

```text
core/       GF(2) 位元向量、位並行線性代數、鏈複形、持久同調、F_p
homotopy/   單形複形、內角填充、神經／棒複形、correspondence
algebra/    自由 Monad、A∞、E∞（surjection operad）、VOA
derived/    Milnor／Tjurina、Hilbert 函數、箭圖 Ext
bench/      可執行基準（moonbitlang/core/bench）
docs/       paper.md / paper.html
scripts/    check.sh
```

執行 `moon test` 時每個 package 的 `*_wbtest.mbt` 即為對應定理的可執行版本（31 個測試）。

## 2026 MoonBit 語法注意

- `trait`/`impl` 方法要 `fn`；泛型寫 `fn[T] f`。
- `Int` = `Int32`；`UInt64` 用 `UL`。
- `moon.pkg` DSL；`using @pkg { type T, value }`；`using` 塊不接受 `fn`。
- 範圍 `for i in (a + 1)..<n` 要括號。
- 熱路徑已標 `#inline`；測試以 `moon test --target wasm` 執行。
