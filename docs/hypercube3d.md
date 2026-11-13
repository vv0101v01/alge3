# 大立方體到 3 維：A∞ 頂邊界、循環同調、單值等價

日期：2026-11-13。程式：`frontier/hypercube3d.mbt`（+ 測試
`frontier/hypercube_wbtest.mbt`）；互動畫面：`docs/hypercube3d.html`
（單檔、零外部依賴，可離線旋轉/縮放查看 n=3..7 的投影）。

問題：高維立方體 $I^n$（n 大）「睇唔見」——無法直接在 3 維空間
呈現。本層給出一條**可計算、已驗證**的路徑，把大立方體的頂邊界
經 A∞ 模型與循環同調，單值等價到 3 維立方體的頂邊界，並把
「睇唔見」的遺忘方向精確量化為纖維（fiber）重數。

---

## 1. 大立方體與小立方體

- 面以 `(mask, vals)` 編碼：`mask` 標記被固定的座標、其值在
  `vals`；$k$-面的數目是 $\binom{n}{k}2^{n-k}$，全部面 $3^n$ 個。
- 胞腔鏈複形（$\mathbb F_2$）：實心立方 Betti 為 $[1,0,\dots,0]$
  （可縮），頂邊界 $\partial I^n$ 的 Betti 為
  $[1,0,\dots,0,1]$（即 $S^{n-1}$），`d²=0` 以精確位長逐列驗證
  （n=3,4,5）。頂邊界鏈 $z_n=\partial[I^n]$ 是 $2n$ 個
  $(n-1)$-面的和，且是循環（cycle）：每個 $(n-2)$-面恰屬於
  兩個面片，故 $\partial z_n=0$。
- 小立方體：每軸二分，$I^n$ 細分為 $2^n$ 個小立方體。小頂邊界
  之和（$\mathbb F_2$）等於大頂邊界的細化：內部面（中間層 1）
  恰出現兩次而相消，外層面（層 0/2）恰出現一次，
  把每個大面片細分為 $2^{n-1}$ 個小面片（n=3,4,5 已驗）。

## 2. A∞ 範疇中的頂邊界

把胞腔鏈複形做成**單對象 A∞（dg）模型**：基底是全部面、按
餘維數分次，$m_1$ = 胞腔邊界、$m_2=m_3=0$。頂胞腔（次數 0）的
$m_1$ 正是頂邊界 $z_n$；第一 Stasheff 恆等式 $m_1^2=0$ 即
$\partial^2=0$。程式以 `@algebra.AInf` 建構 n=2,3 的模型
（n 大時 $m_3$ 表是面數的三次方，故 A∞ 證書只建到 n=3，
組合複形則驗到 n=5），連同既有的外代數、截斷多項式、線 dga
一併通過 `check_all()`（Stasheff 恆等式全驗）。

## 3. 循環同調

座標的循環輪換 $\rho:i\mapsto i+1 \bmod n$ 是邊界胞腔複形的
自同構，$\rho\partial=\partial\rho$、$\rho^n=1$，且 $z_n$ 在
$\rho$ 下不變（$\rho$ 置換其 $2n$ 個面片），故 $z_n$ 是循環
模型的循環循環。循環同調取循環雙複形的全複形：
$\mathrm{Tot}_t=\bigoplus_{p=0}^{t}C_{t-p}$，
微分 $D=\partial+h_p$，其中 $h_p$ 在奇數 $p$ 是 $1-\rho$、
在偶數 $p\ge2$ 是範數 $N=1+\rho+\cdots+\rho^{n-1}$
（$\mathbb F_2$ 上符號消失）；$D^2=0$ 用
$(1-\rho)N=N(1-\rho)=0$ 驗證（n=3,4,5）。
低度數循環 Betti 數（MoonBit 實算，獨立複核一致）：

| n | 循環 Betti（次數 0..3） |
|---|---|
| 3 | [1, 0, 1, 0]（次數 2 即 $S^2$ 頂類） |
| 4 | [1, 1, 1, 2] |
| 5 | [1, 0, 0, 0]（頂類在次數 4，於低窗口之外，由 §4 搬運） |

## 4. 等價到 3 維：纖維積分 + 單值等價

遺忘座標 $3,\dots,n-1$ 的投影 $\pi:I^n\to I^3$ 在鏈層面用
**纖維積分**（shriek / 纖維積分）$\pi_!$：一個面存活當且僅當
其遺忘部分是整條纖維 $I^{n-3}$（無遺忘座標被固定），像取前三
座標的限制；否則送 0。$\pi_!$ 次數降 $n-3$，且是鏈映射
（$\pi_!\partial=\partial\pi_!$，逐面驗證：固定遺忘座標會同時
破壞兩邊的纖維完整性）。於是

$$\pi_!(z_n)=z_3=\partial[I^3],$$

因為固定保留座標的面片存活、固定遺忘座標的面片纖維不完整而
消失——大立方的頂邊界**嚴格**等於 3 維頂邊界（6 個面），
不是近似投影。頂點層面：影子是遺忘座標的商集，每個 3 維
頂點的纖維恰有 $2^{n-3}$ 個高維頂點（n=4,5 已驗）。

單值等價（univalence）：影子面類型（side-major 序）與 $I^3$
面類型（axis-major 序）之間有顯式等價
$e$（置換 $[0,2,4,1,3,5]$）；頂點影子同理（Gray 碼序置換）。
`@cubical.ua(e)` 把 $e$ 變成有限立方宇宙中的路徑，
`transport (ua e)` 計算出 $e$ 本身（uaβ，逐元素驗），且
`idtoeqv (ua e) = e`（單值兩邊往返皆驗）。即影子不是類比，
是沿單值路徑的 transport。

## 5. 「睇唔見」的解決與誠實邊界

- 可見部分：投影後 6 個頂邊界面、8 個影子頂點、$I^3$ 線框；
  互動頁可旋轉、開關頂邊界影子/細分/纖維高亮，n 可調 3..7。
- 不可見部分被量化而非假裝消失：遺忘方向成為纖維重數
  $2^{n-3}$ 與「纖維不完整面」的相消（$\mathbb F_2$ 兩兩取消）。
- 誠實邊界：$I^n$ 與 $I^3$ 同為可縮，但作為集合不等、
  $\partial I^n\cong S^{n-1}$ 與 $S^2$ 不同倫；本層的等價是
  **經纖維積分/商集與循環同調截斷後、有限影子類型之間**的
  單值等價。畫面用的線性相機（軸方向表與
  `hc_vertex_xyz` 同）只是顯示裝置，不承載等價的證明。

## 6. 驗證

```bash
export PATH="$HOME/.moon/bin:$PATH"   # moon 0.1.20261104 / moonc v0.10.20
moon fmt --check
moon check --target wasm --deny-warn
moon check --target native --deny-warn
moon test --target wasm               # 67/67
moon test --target native             # 67/67
moon run --target native bench        # hypercube3d pipeline ok: true
```

`bench` 實測（節選）：

```text
hypercube3d pipeline ok: true
big cube I^5 solid betti: [1, 0, 0, 0, 0, 0]
top boundary dI^5 (= S^4) betti: [1, 0, 0, 0, 1]
cyclic homology betti (low, n=5): [1, 0, 0, 0]
projected top boundary facets pi_!(z_5): 6
hypercube3d full check us: ~135773
```

另：本層觸發並修復了核心層一處潛在越界——
`Bits::xor_inplace` 在兩操作數字長不同（維度跨 64 位邊界）
時會讀越界；現改為對短操作數零擴展（只迭代較短長度）。
立方體複形的 `d²=0` 另以精確位長的自有檢查
`hc_solid_d2_ok`／`hc_boundary_d2_ok`／`hc_cyclic_d2_ok`
逐列驗證，不依赖通用 `ChainComplex::check_d2` 的累加器長度。
