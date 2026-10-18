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
