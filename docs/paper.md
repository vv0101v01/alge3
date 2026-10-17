# 編譯期導出數學：以 MoonBit 實作 ∞-範疇、A∞/E∞、VOA 與導出模空間的位並行演算法

> 模組：`arena/moonmath`　·　工具鏈：`moon 0.1.20261012` / `moonc v0.10.15+943464bfa`　·　目標：`wasm`（測試）、`native`（基準）
>
> 原始碼：`core/`、`homotopy/`、`algebra/`、`derived/`、`cubical/`、`bench/`。44 個測試全綠。

---

## 摘要

本文把一串高階結構——穩定無窮範疇、同倫類型論、Monad 與代數理論、VOA 的上同調支撐簇、A∞ 與 E∞ 代數、形式模空間與導出模空間——壓縮成同一套**可在有限資料上執行**的演算法，並以 MoonBit 由零實作。核心觀察有三點：

1. **同調計算是 GF(2) 線性代數**。把單形、鏈、過濾複形全部編碼成 `UInt64` 位元向量，Gaussian 消去、矩陣乘法、持久同調都變成「一個機器字 XOR 同時處理 64 個體元素」。實測 rank 加速約 43–45×、Boolean 矩陣乘約 98–102×。
2. **代數結構的公理就是可檢查的方程**。Monad 三律＝ substitution 三引理；A∞ 的 Stasheff 恆等式是 m₁,m₂,m₃ 的有限方程；E∞ 的 contractibility 是 surjection operad 各分量的同調群；VOA 的 Heisenberg 對易子與 Wick 定理是有限 Fock 空間上的矩陣恆等式。
3. **「代碼同態置換」是結構保持的編譯變換**。自由 Monad 上的 substitution 是 Kleisli 合成；常數摺疊是 term homomorphism；把定理寫成測試，等於在編譯期／測試期把代數公理內化成型別與函數的不變量。

全部演算法都只用到整數與位元運算，沒有浮點誤差；只在基準計時使用單調時鐘。

後記：§10 將單價公理（univalence axiom）轉換成立方體演算法：在有限立方體模型中以 Glue 類型與 Kan 合成 `comp` 定義 $\mathsf{ua}$，使 $\mathsf{transport}\,(\mathsf{ua}\,e)$ 真正計算到 $e$；完整論文見 `docs/cubical.md`。

---

## 0. 版本、語法與專案結構

### 0.1 工具鏈（2026-10 最新穩定）

以官方安裝腳本安裝後得到：

```text
moon 0.1.20261012 (748b63c 2026-10-12)
moonc v0.10.15+943464bfa (2026-10-12)
moonrun 0.1.20261012 (748b63c 2026-10-12)
```

方案檔由 `moon.mod`（模組）與每個套件目錄的 `moon.pkg`（DSL）組成；沒有 `moon.pkg.json`。測試分黑盒 `_test.mbt` 與白盒 `_wbtest.mbt`。

### 0.2 2026 語法要點（實測）

- `trait` 與 `impl` 的方法必須加 `fn`：
  ```moonbit
  pub trait Semi {
    fn zero() -> Self
    fn add(Self, Self) -> Self
  }
  impl Semi for Z2 with fn zero() { Z2::{ val: 0 } }
  ```
- 泛型函數的型別參數在函數名之前：`pub fn[T : Semi] twice(x : T) -> T { ... }`。
- `Int`／`UInt` 是 `Int32`／`UInt32` 的別名；`UInt64` 字面量用 `UL`。
- 列舉、結構體可 `derive(Debug, Eq)`；`derive` 的隱式方法提升在 2026 版會發出 `implicit_impl_as_method` 警告（可用 `pub extend T with Eq::{...}` 顯式聲明）。
- `using @pkg { type T, value }` 重新匯出型別／值；`using` 塊內**不接受 `fn` 關鍵字**。
- `for i in (a + 1)..<n`：範圍運算只可在 `for .. in` 中使用，且 `+` 與 `..<` 需要括號。
- `#inline` 可標注熱路徑小函數。
- 預設目標為 `wasm`；`moon test --target wasm`、`moon run --target native bench`。

### 0.3 套件分層

```text
moonmath/
  core/        Bits（GF(2) 位元向量）、BoolMat、ChainComplex、Filtration、F_p
  homotopy/    SimplicialComplex、三角剖分、內角填充、Monoid nerve/bar、Span
  algebra/     Term/Monad、Eilenberg–Moore fold、AInf、surjection operad、VOA
  derived/     加權齊次奇點 μ/τ、Hilbert 函數、箭圖表示 Ext
  cubical/     區間/面格、CubeTy、Glue、comp、ua（立方體單價，見 §10）
  bench/       可執行基準與數學摘要
```

依賴方向嚴格單向：`core ← homotopy/algebra/derived/cubical ← bench`；`core` 不依賴任何自訂套件。

---

## 1. 方法論：代碼同態置換與零成本抽象

### 1.1 三層架構

| 層 | 數學物件 | 代碼物件 | 不變量 |
|---|---|---|---|
| 結構層 | ∞-範疇、operad、VOA | 型別、trait、套件 | 公理方程 |
| 演算法層 | 邊界算子、柱消去、Wick 收縮 | 位並行線性代數、DP | 同調群／配對 |
| 生成層 | 導出模空間、特徵標 | 基準、報表 | 數值表 |

### 1.2 同態置換的定義

**定義 1.1（代碼同態）**　設 $T$ 為自由 term monad，$\eta: \mathrm{Id}\to T$、$\mu: T^2\to T$。一個代碼變換 $F: T(X)\to T(Y)$ 稱為**同態置換**，若

$$
F(\eta(x)) = \eta(f(x)),\qquad
F(\mu(t)) = \mu(F(F(t))).
$$

在我們的 `Term` 實作中，$\mu$ 就是 `subst`：$ \mu(t) = t[\,\mathrm{Var}(i)/x_i\,] $。三條 substitution 引理

$$
t[x_i := e_i][y_j := g_j] = t\bigl[x_i := e_i[y_j := g_j]\bigr],
$$
$$
(\mathrm{Var}(i))[x_i:=e_i] = e_i,\qquad
t[x_i:=\mathrm{Var}(i)] = t
$$

正好是 monad 的左么元、右麼元與結合律。

**定理 1.2（常數摺疊保持語義）**　若 $A$ 是簽名 $\Sigma$ 的代數，$\mathrm{fold}_A: T_\Sigma(X)\to A$ 是唯一同態，$O: T_\Sigma(X)\to T_\Sigma(X)$ 是常數摺疊，則

$$
\mathrm{fold}_A \circ O = \mathrm{fold}_A .
$$

*證明.* 對 $t$ 的結構歸納。葉子不變；若所有子項皆為常數，$O$ 把它們換成字面量，而 `fold` 在字面量上的值就是其常數，與先 fold 子項再套用運算相同。∎

這條定理在代碼上的意思：**最佳化是 term 的同倫等價**，而不是改語義。測試 `fold is invariant under constant folding` 以具體算術簽名驗證 $42=42$。

### 1.3 零成本抽象

**命題 1.3（單態化消除）**　若泛型函數 $f[A]$ 只透過 trait 約束使用 $A$ 的方法，且所有型別參數在呼叫點具體化，則 MoonBit 的單態化＋`#inline` 把 trait 方法解析成直接呼叫；執行期不存在字典或動態分派。

這不是形式化定理（語言未提供成本模型），但可由 `moon info` 的 `.mbti` 與生成的 wasm 驗證：本專案所有熱路徑（`Bits::get/set/flip`、`popcount64`、`trailing_zeros64`）皆標注 `#inline`，且 `rank` 對 `Bits` 是具體型別，沒有 trait object。

**設計原則**：抽象留在原始碼，成本留在編譯器；資料佈局（`Array[UInt64]`）在 API 邊界固定，避免抽象洩漏成配置。

---

## 2. ∞-範疇、同倫類型論與 correspondences

### 2.1 擬範疇與內角填充

**定義 2.1（擬範疇）**　單純集 $X$ 稱為**擬範疇**（quasi-category，$(\infty,1)$-範疇的一種模型），若對所有 $n\ge 2$、$0<k<n$，每個內角映射

$$
\Lambda^n_k \longrightarrow X
$$

都能延伸為 $n$-單形 $\Delta^n\to X$。

**定理 2.2（Joyal）**　單純集範疇與單純範疇（simplicial categories）之間存在 Quillen 等價；擬範疇正是其 fibrant objects。 nerve 函子

$$
N: \mathbf{Cat}\to \mathbf{sSet}
$$

全忠實，且是 h-範疇函子 $ho$ 的右伴隨。

**定理 2.3（神經填充）**　對任意小範疇 $\mathcal C$，$N\mathcal C$ 的所有內角都可填充；外角 $\Lambda^n_0,\Lambda^n_n$ 只在對應態射可逆時才必然填充。

*證明要點.* $N\mathcal C_n = \mathrm{Fun}([n],\mathcal C)$。給內角，除了 $d_k$ 以外的面都已給；用 $\mathcal C$ 的合成填補缺失的 $k$-面，範疇公理保證與其他面交換。∎

**演算法 2.4（有限複形上的內角填充檢查）**

```text
for every 4-set {a,b,c,d}:
    faces = [bcd, acd, abd, abc]
    for missing in {1,2}:            # 內角 Λ³₁, Λ³₂
        if exactly the other 3 faces exist and tetrahedron abcd absent:
            return false
return true
```

在 `homotopy/simplicial.mbt` 中，`fills_inner_horns_2/3` 用位元遮罩與二元搜尋實作，測試覆蓋：

- $\Delta^3$ 的完整 3-單形：填充成功；
- $\partial\Delta^3=S^2$：$\Lambda^3_1$ 的三個面存在但無 3-單形，填充失敗。

### 2.2 神經、棒複形與分類空間

么半群 $M$ 的神經 $NM$ 的 $k$-胞是 $k$-元組 $(a_1,\dots,a_k)$。其面映射

$$
d_i(a_1,\dots,a_k)=
\begin{cases}
(a_2,\dots,a_k), & i=0,\\
(a_1,\dots,a_i a_{i+1},\dots,a_k), & 0<i<k,\\
(a_1,\dots,a_{k-1}), & i=k.
\end{cases}
$$

在 $\mathbb F_2$ 上，鏈複形 $C_k=\mathbb F_2[M^k]$ 的微分是 $\sum_i d_i$（符號消失）。我們用位並行 rank 計算 $H_*(BM;\mathbb F_2)$：

| $M$ | $H_0$ | $H_1$ | $H_2$ | $H_3$ | $H_4$ |
|---|---|---|---|---|---|
| 平凡么半群 | 1 | 0 | 0 | 0 | 0 |
| $\mathbb Z/2$ | 1 | 1 | 1 | 1 | 1 |
| $\mathbb Z/3$ | 1 | 0 | 0 | 0 | 0 |

$\mathbb Z/3$ 的正度同調為零，因為 $3$ 在 $\mathbb F_2$ 中可逆（$H_1=\mathbb Z/3\otimes\mathbb F_2=0$，其餘由萬有係數定理）；這與程式的 `[1,0,0,0,0]` 一致。$\mathbb Z/2$ 的週期性 $1,1,1,\dots$ 正是 $H^*(B\mathbb Z/2;\mathbb F_2)=\mathbb F_2[t]$。

**複雜度**：$\dim C_k=n^k$，邊界矩陣有 $n^k$ 列、每列 $k+1$ 個面；rank 以 $64$ 位並行後為

$$
O\!\left(\frac{k\,n^{2k}}{64}\right)
$$

算術字操作（對 $k\le K$ 求和）。

### 2.3 Correspondences 與 profunctor 合成

**定義 2.5（span / correspondence）**　範疇 $\mathcal C$ 中的一個 span 是圖

$$
A \xleftarrow{\;f\;} R \xrightarrow{\;g\;} B .
$$

在 $\mathbf{Rel}$（布林半環上的關係）中，span 由關係矩陣 $M_{ij}\in\{0,1\}$ 表示；兩個 span 的合成是拉回：

$$
(M\circ N)_{ik} = \bigvee_j (M_{ij}\wedge N_{jk}).
$$

**定理 2.6**　span 的合成滿足結合律與單位律；在 $\mathbf{Rel}$ 中它等於布林矩陣乘法，因而可用位並行 `BoolMat::mul_or` 計算。

*證明.* 拉回的泛性質給出 $(R\times_S T)\times_U V\cong R\times_S(T\times_U V)$，逐點展開即得 $\bigvee$ 的結合律。∎

**演算法 2.7**

```text
for each row i of A:
    acc = 0
    for each set bit j of row i:
        acc |= B.row[j]
    C.row[i] = acc
```

成本：$O(mkn/64)$ 字操作，對 $n=256$ 實測比純量三重迴圈快 97×。

### 2.4 同倫類型論

**定義 2.8（恆等型）**　在 Martin–Löf 型別論中，對 $a,b:A$ 有恆等型 $\mathrm{Id}_A(a,b)$；其元素是「$a$ 與 $b$ 之間的同倫」。J-消除子給出路徑歸納。

**定理 2.9（Voevodsky）**　單價公理

$$
\mathrm{ua}: \prod_{A,B:\mathcal U} (A\simeq B)\to (A=B)
$$

與 J-消除子相容，並推出函數外延性；在同倫語義中，型別解釋為 $\infty$-groupoid，恆等型解釋為路徑空間。

**定理 2.10（代碼搬運）**　若 $e:A\simeq B$ 是等價，且 $P$ 是可傳輸的型別族，則任一程式 $p:P(a)$ 可沿 $e$ 傳輸為 $e_*p:P(b)$，且傳輸與合成相容：

$$
(e\circ e')_* = e_* \circ e'_* .
$$

在實作層，這對應「同態置換」：`map_vars`／`subst` 是 term 的函子與 monad 作用，測試 `monad laws for substitution` 驗證其相容性。這是「代碼同態置換」的可執行影子：結構映射保持合成與單位。

---

## 3. Monad 與代數理論

**定義 3.1（Monad）**　三元組 $(T,\eta,\mu)$，其中 $T:\mathcal C\to\mathcal C$ 是自函子，

$$
\eta: \mathrm{Id}\Rightarrow T,\qquad \mu: T^2\Rightarrow T,
$$

滿足
$\mu\circ T\mu=\mu\circ\mu T$（結合律）、$\mu\circ T\eta=\mathrm{id}=\mu\circ\eta T$（單位律）。

**定理 3.2（Eilenberg–Moore / Beck）**　若 $T$ 來自伴隨 $F\dashv U$，則 $T=UF$ 是 monad；其 Eilenberg–Moore 代數範疇 $\mathcal C^T$ 與「配備 $T$-運算且滿足單位與結合的公理」的物件等價。若 $U$ 保持某些餘等化子且反映它們，Beck 單子性定理給出 $\mathcal C^T\simeq\mathcal D$。

在程式語言中，$T$ 是「帶效果的計算」；自由 monad $T_\Sigma$ 是語法樹，$\mu$ 是 substitution，$\eta$ 是 `Var`。`Algebra` 的 `fold` 是 EM 代數結構映射：

$$
\alpha: T(A)\to A,\qquad
\alpha\circ\eta_A=\mathrm{id}_A,\qquad
\alpha\circ\mu_A=\alpha\circ T\alpha .
$$

**命題 3.3（substitution 成本）**　對大小 $|t|$ 的 term 與環境 $E$，樸素 substitution 的成本是 $O(|t|\cdot|E|)$；若環境以閉包／de Bruijn level 表示，可降到 $O(|t|)$。本專案的 `subst_cost` 實作前者，並在測試中以 $|t|=7, |E|=2$ 驗證成本為 7（葉子替換）。

分配律（distributive law）$\lambda: TS\Rightarrow ST$ 的例子：`List ∘ Option → Option ∘ List` 的矩陣轉置；測試 `distributive law hexagon` 驗證兩條六邊形公理在具體資料上成立。它給出複合 monad $ST$，對應「先列舉再失敗」的語義。

---

## 4. A∞ 與 E∞ 代數

### 4.1 A∞ 的 Stasheff 恆等式

**定義 4.1**　 graded $\mathbb F_2$-向量空間 $A=\bigoplus A_d$ 上的 $A_\infty$-結構是一族運算

$$
m_n: A^{\otimes n}\to A,\qquad |m_n|=2-n,
$$

滿足對所有 $n\ge 1$：

$$
\sum_{r+s+t=n}(-1)^{r+st}\,
m_{r+1+t}\bigl(\mathrm{id}^{\otimes r}\otimes m_s\otimes \mathrm{id}^{\otimes t}\bigr)=0.
$$

當 $n=3$、$m_1=0$ 時，這條式子退化為 $m_2$ 的嚴格結合律；$m_3$ 的自由度出現在 $n=4$，量度 $m_2$ 的結合子（associator）的同倫。這正是「結合律 up to coherent homotopy」的精確含義。

**定理 4.2（Kadeishvili；HPT）**　設 $(A,d,\mu)$ 是 dg 代數，$H=H^*(A)$。存在 $A_\infty$-結構 $\{m_n^H\}$ 於 $H$ 上，使 $m_1^H=0$、$m_2^H$ 為誘導乘法，且存在 $A_\infty$-擬同構 $H\rightsquigarrow A$。此結構在 $A_\infty$-擬同構意義下唯一。

**柱消去轉移公式**（$\mathbb F_2$ 上，$p,i,h$ 為 SDR）：

$$
m_2^H=p\,\mu\,(i\otimes i),\qquad
m_3^H=p\,\mu\,\bigl(h\mu\otimes 1+1\otimes h\mu\bigr)(i^{\otimes 3}).
$$

**演算法 4.3**　以位元向量表示 $m_n$ 的輸出，逐項檢查：

```text
check_m1sq:        for i: sum_{j in m1[i]} m1[j] == 0
check_derivation:  m1(m2(i,j)) + m2(m1 i,j) + m2(i,m1 j) == 0
check_stasheff3:   m1 m3 + m3(m1,1,1)+m3(1,m1,1)+m3(1,1,m1)
                   + m2(m2,1)+m2(1,m2) == 0
```

`algebra/ainf.mbt` 對三個例子驗證全部公理：外代數 $\Lambda(e_1,e_2)$、線性 dga $\mathbb F_2[1,x]$（$|x|=0,|y|=1,dx=y$）、截斷多項式 $\mathbb F_2[x]/(x^3)$。三者 `check_all()` 皆真。

### 4.2 E∞ 與 surjection operad

**定義 4.4（E∞ operad）**　拓撲 operad $\mathcal E$ 稱為 $E_\infty$，若每個 $\mathcal E(r)$ 可縮、$\Sigma_r$-自由，且 $\mathcal E(0)$ 非空。它編碼「交換律 up to 所有高階同倫」。

**定義 4.5（McClure–Smith surjection operad）**　$\mathcal X(r)_d$ 由**非退化 surjection**

$$
u:\{1,\dots,r+d\}\to\{1,\dots,r\},\qquad u(i)\neq u(i+1)
$$

自由生成；微分為刪去一個位置的交替和：

$$
\partial u=\sum_{i=1}^{r+d}(-1)^i\,u\circ\delta_i .
$$

**定理 4.6（McClure–Smith；Berger–Fresse）**　$\mathcal X$ 是 $E_\infty$-operad，且自然作用於奇異餘鏈；$\mathbb F_2$ 上 $C_\infty$ 與 $E_\infty$ 在 homotopy 意義下等價，故交換性可提升為嚴格的交換 dg 代數模型。

**演算法 4.7**　對固定 arity $r$，逐度 $d$ 列舉非退化 surjection，建邊界矩陣 $ \partial: \mathcal X(r)_d\to\mathcal X(r)_{d-1}$，用位並行 rank 計算

$$
\beta_d=\dim \mathcal X(r)_d-\mathrm{rank}\,\partial_d-\mathrm{rank}\,\partial_{d+1}.
$$

計算結果：

| $r$ | $\beta_0$ | $\beta_1$ | $\beta_2$ | $\beta_3$ |
|---|---|---|---|---|
| 2 | 1 | 0 | 0 | 0 |
| 3 | 1 | 0 | 0 | 0 |
| 4 | 1 | 0 | 0 | 0 |

即每個分量可縮，與 $E_\infty$ 公理一致。這是**用線性代數驗證 operad 拓撲性質**而非假設它。

**Dyer–Lashof 運算**：$E_\infty$ 結構在 $\mathbb F_2$ 同調上給出運算 $Q^s$（$s\ge 0$），滿足不穩定性 $Q^s(x)=x^2$（當 $s=|x|$）與 $Q^s(x)=0$（當 $s<|x|$）。本專案以 `free_einfty_dims` 計算自由 $E_\infty$-代數的加法基（與多項式代數同構）；分割數 $p(n)$ 由 DP 給出：$1,1,2,3,5,7,11,\dots$。

### 4.3 Bar 構造

對 $A_\infty$-代數 $A$，bar 構造

$$
B(A)=\bigoplus_{n\ge 0} A^{\otimes n},\qquad
d(a_1|\cdots|a_n)=\sum_{k\ge 1}\sum_{i} m_k(a_i,\dots,a_{i+k-1})\,|\,\cdots
$$

在 $A_\infty$ 公理下滿足 $d^2=0$。它是 $A$ 的 Hochschild 鏈複形；quasi-isomorphism $A\to A'$ 誘導 $B(A)\to B(A')$ 的 quasi-isomorphism。此構造把 $\infty$-代數問題化為有限鏈複形問題——正是本專案 `ChainComplex` 的輸入格式。

---

## 5. VOA 與上同調支撐簇

### 5.1 定義與模式

**定義 5.1（頂點算子代數）**　向量空間 $V=\bigoplus_{n\in\mathbb Z}V_n$（或 $\mathbb N$-graded），配備真空 $ \mathbf 1\in V_0$、平移 $T$、態場對應

$$
Y: V\to \mathrm{End}(V)[[z,z^{-1}]],\qquad
Y(a,z)=\sum_{n\in\mathbb Z} a_{(n)}\,z^{-n-1},
$$

滿足真空、平移、局部性（locality）與 $Y(Ta,z)=\partial_z Y(a,z)$。模式 $a_{(n)}$ 稱為 $a$ 的第 $n$ 個模式。

### 5.2 Heisenberg VOA

**定義 5.2**　rank 1 Heisenberg VOA 的 Fock 空間

$$
M_1=\mathbb C[\alpha_{-1},\alpha_{-2},\dots]\,|0\rangle,
\qquad
[\alpha_m,\alpha_n]=m\,\delta_{m+n,0},
$$

態場 $ \phi(z)=\sum \alpha_n z^{-n-1}$ 的 OPE

$$
\phi(z)\phi(w)\sim \frac{1}{(z-w)^2},
\qquad c=1.
$$

真空特徵標

$$
\chi(q)=\mathrm{tr}_{M_1}q^{L_0-c/24}
= q^{-1/24}\prod_{n\ge1}\frac{1}{1-q^n}
= q^{-1/24}\sum_{n\ge0}p(n)q^n .
$$

**演算法 5.3（模式矩陣）**　以關聯多項式 $p_m$ 的次數向量表示 Fock 態；$\alpha_{-m}$ 乘 $p_m$，$\alpha_m=m\,\partial/\partial p_m$。在截斷 $ \sum k m_k\le N$ 上建矩陣，驗證

$$
[\alpha_m,\alpha_{-n}]=m\delta_{m,n}\,\mathrm{id}
$$

於「有空間」的子空間上。測試 $N=6,m=1,2$ 全真。

### 5.3 Wick 定理與複雜度

**定理 5.4（Wick）**　自由玻色場的 $2n$-點函數

$$
\left\langle \phi(x_1)\cdots\phi(x_{2n})\right\rangle
=\sum_{\text{pairings }\pi}\prod_{(i,j)\in\pi}\frac{1}{(x_i-x_j)^2}.
$$

**演算法 5.5（子集 DP）**　令 $D[S]$ 為點集 $S$ 的所有完美匹配之和：

$$
D[\varnothing]=1,\qquad
D[S]=\sum_{j\in S\setminus\{i\}} G_{ij}\,D[S\setminus\{i,j\}],
$$

其中 $i=\min S$、$G_{ij}=1/(x_i-x_j)^2$。成本 $O(n^2 4^n)$，對比樸素列舉 $(2n-1)!!$。實測 16 點：DP 12.5 ms vs 樸素 517–592 ms（41–47×）。

另有行列式／Pfaffian 公式（對複雜玻色子）：$ \langle\prod_i e^{ik_i\phi(x_i)}\rangle=\prod_{i<j}(x_i-x_j)^{k_ik_j}$，成本 $O(n^2)$；Pfaffian 以 Gaussian 消去 $O(n^3)$ 計算，兩者與 Wick DP 可互相驗證。

### 5.4 Zhu 代數與支撐簇

**定義 5.6（Zhu 代數）**　對 $V=\bigoplus_{n\ge0}V_n$，

$$
A(V)=V_0/O(V),\qquad
O(V)=\mathrm{span}\{\,a_{(n)}b\mid a,b\text{ homogeneous},\ n>0\,\}.
$$

**定理 5.7（Zhu）**　在適當條件下，$A(V)$-模範疇等價於 admissible $V$-模範疇；不可約 admissible 模對應 $A(V)$ 的單模。

對 Heisenberg VOA，$A(M_1)\cong\mathbb C[\alpha_{-1}]\cong\mathbb C[t]$，故支撐簇是 $\mathbb A^1$ 或其原點，取決於模的支撐。

**定義 5.8（rank variety / 支撐簇）**　對有限維 $\mathbb F_p$-代數 $\Lambda$ 與有限 $\Lambda$-模 $M$，令 $ \xi(t)=\sum_i t_i x_i$。rank variety 是

$$
V(M)=\{\,t\in\mathbb A^n \mid \mathrm{rank}\,\xi(t)<r_{\max}\,\}\cup\{0\},
$$

其中 $r_{\max}$ 是 generic rank；對 exterior algebra $\Lambda=\wedge(x_1,\dots,x_n)$，這與 cohomological support variety 一致（Avramov–Eisenbud 的 rank variety 定理）。

**演算法 5.9**　在 $\mathbb F_p^n$ 上枚舉 $t$，對每個 $t$ 以 $O(d^3)$ 的 `fp_rank` 計算 $\xi(t)$ 的 rank；統計最大 rank 與低 rank 點數。

測試：$n=2$、regular module $\Lambda$ 上，$t=0$ 時 rank 0，其餘 3 點 rank 2，故低於最大值者恰 1 點；trivial module 的 rank 恆為 0。自由費米子 VOA 的零模滿足 Clifford 關係 $\{ \psi_r,\psi_s\}=\delta_{r+s,0}$，其 Fock 空間正是這類 exterior/Clifford 模；因此上述 rank 分層就是 VOA 模支撐簇的離散模型。

---

## 6. 形式模空間與導出模空間

### 6.1 dgLie / L∞ 與 Maurer–Cartan

**定義 6.1**　dg Lie 代數 $(\mathfrak g,d,[\ ,\ ])$ 的 Maurer–Cartan 方程為

$$
dx+\tfrac12[x,x]=0,\qquad x\in\mathfrak g_1 .
$$

其解空間 modulo gauge（$x\mapsto x+d\alpha+[\alpha,x]+\cdots$）是形式模空間 $\mathrm{MC}(\mathfrak g)/\sim$。

**定理 6.2（Lurie）**　在特徵 0 域上，形式模問題（formal moduli problems）與 dg Lie 代數（或 L∞-代數）之間有範疇等價；切複形給出 $T^i$，且 obstruction theory 由 $T^2$ 控制。

在 $\mathbb F_p$ 上，同倫代數需以 simplicial／derived 方法處理；本專案以 Jacobian 環與 Koszul 型線性代數提供可計算的不變量。

### 6.2 孤立超曲面奇點

設 $f\in\mathcal O=\mathbb F_p[x_0,\dots,x_{n-1}]$ 是孤立奇點。

**定義 6.3**

$$
\mu(f)=\dim_{\mathbb F_p}\frac{\mathcal O}{(\partial_0 f,\dots,\partial_{n-1}f)},
\qquad
\tau(f)=\dim_{\mathbb F_p}\frac{\mathcal O}{(f,\partial_0 f,\dots,\partial_{n-1}f)} .
$$

$\mu$ 是 Milnor 數（函數 $f$ 的展開參數空間維度），$\tau$ 是 Tjurina 數（超曲面 $\{f=0\}$ 的一階變形空間維度）。

**定理 6.4（Saito）**　若 $f$ 是 quasi-homogeneous 且孤立，則 $\mu(f)=\tau(f)$。

**演算法 6.5（Jacobian 秩）**　取加權么半群基 $B_D=\{x^e: \sum w_i e_i\le D\}$。對每個生成元 $g\in\{f,\partial_0f,\dots\}$ 與每個乘子 $x^m\in B_D$，把 $x^m g$ 展成 $B_D$ 的坐標，堆成矩陣 $J$。則

$$
\dim \mathcal O/I=\#B_D-\mathrm{rank}\,J .
$$

以 $D=n\cdot \deg f$ 截斷（對 quasi-homogeneous 足夠），用 `fp_rank` 計算。

**ADE 表**（實測，$\mu=\tau$）：

| 型 | $f$ | 權重 | $\deg f$ | $\mu$ |
|---|---|---|---|---|
| $A_1$ | $x^2+y^2$ | (1,1) | 2 | 1 |
| $A_2$ | $x^3+y^2$ | (2,3) | 6 | 2 |
| $A_4$ | $x^5+y^2$ | (2,5) | 10 | 4 |
| $D_4$ | $x^3+xy^2$ | (2,2) | 6 | 4 |
| $E_6$ | $x^3+y^4$ | (4,3) | 12 | 6 |
| $E_7$ | $x^3+xy^3$ | (3,2) | 9 | 7 |
| $E_8$ | $x^3+y^5$ | (5,3) | 15 | 8 |

**Hilbert 函數**：對 quasi-homogeneous 且 Jacobian 理想為完全交的場合，

$$
\mathrm{Hilb}_{\mathcal O/(\partial f)}(t)
=\prod_{i=0}^{n-1}\frac{1-t^{\deg f-w_i}}{1-t^{w_i}} .
$$

程式以逐度 rank 的差分計算，對 $A_2$ 得到 $1+t^2$（基 $1,x$），與公式一致。

### 6.3 箭圖表示的變形複形

**定義 6.6**　有限箭圖 $Q$ 的表示 $M=(\{V_i\},\{A_a:V_i\to V_j\})$。其變形複形

$$
C^0=\bigoplus_i \mathrm{End}(V_i),\qquad
C^1=\bigoplus_{a:i\to j}\mathrm{Hom}(V_i,V_j),
$$

微分

$$
\delta^0(X)_a=X_{t(a)}A_a-A_aX_{s(a)} .
$$

**命題 6.7**

$$
\dim\mathrm{Ext}^0(M,M)=\dim\ker\delta^0,\qquad
\dim\mathrm{Ext}^1(M,M)=\dim\mathrm{coker}\,\delta^0,
$$

且 $\mathrm{Ext}^1$ 是形式模空間 $\mathrm{Rep}(Q,\mathbf d)/\!/GL(\mathbf d)$ 在 $M$ 處的 Zariski 切空間。

實測：Kronecker 箭圖（兩支箭頭 $0\to1$、維度 $(1,1)$）$\mathrm{Ext}^0=1,\mathrm{Ext}^1=1$；$A_2$ 的 $(1,1)$ 表示 $\mathrm{Ext}^1=0$（剛性）。

---

## 7. 演算法、複雜度與實測

### 7.1 複雜度表

| 問題 | 樸素成本 | 本實作 | 關鍵技巧 |
|---|---|---|---|
| GF(2) rank $n\times n$ | $O(n^3)$ | $O(n^3/64)$ | 位元向量、低位 pivot |
| Boolean 矩陣乘 $m\times k\times n$ | $O(mkn)$ | $O(mkn/64)$ | 位並行 OR |
| 持久同調 $m$ 胞 | $O(m^3)$ | $O(m^3/64)$ | 柱消去＋位元 XOR |
| 神經 $B M$ 至度 $K$ | $O(K n^{2K})$ | $O(K n^{2K}/64)$ | 邊界矩陣位並行 |
| surjection operad $E(r)_{\le D}$ | $O(N^3)$ | $O(N^3/64)$ | rank 位並行 |
| Wick $2n$-點 | $(2n-1)!!$ | $O(n^2 4^n)$ | 子集 DP |
| Milnor/Tjurina | 解線性方程 $O(M^3)$ | $O(M^3)$（$M$=monomials） | 稀疏→稠密 rank |
| substitution | $O(|t|\cdot|E|)$ | 同左；可用閉包降 | 環境替換 |

### 7.2 基準（native，單調時鐘，5 次平均）

| 基準 | 位並行／DP | 純量／樸素 | 加速 |
|---|---|---|---|
| rank $512\times512$ | 23.8–24.3 ms | 1.03–1.10 s | 43–45× |
| Boolean matmul $256^3$ | 3.1–4.0 ms | 315–393 ms | 98–102× |
| Wick 16 點 | 12.5 ms | 517–592 ms | 41–47× |
| $B\mathbb Z/2$ 至度 8 | 4.6 ms | — | — |
| $E(4)$ 至度 3 | 194–244 ms | — | — |
| Milnor $E_8$ | 0.22–0.27 ms | — | — |
| Heisenberg 對易子檢查 | 11.8–14.2 ms | — | — |

> 數字依機器而異；比率比絕對值穩定。`wasm` 目標下所有測試亦通過。

### 7.3 為何「位並行」不會損失正確性

位元向量運算 $ \oplus,\wedge $ 與 $\mathbb F_2$ 的加法、乘法逐位對應；rank 的低位 pivot 消去是域上 Gaussian 消去的精確模擬。持久同調的柱消去只用到「最低非零位」與 XOR，這兩者在位元表示下與純量表示同構。因此加速是**常數因子 64**（外加記憶體局部性），不是近似。

---

## 8. MoonBit 實作與驗證

### 8.1 關鍵型別

```moonbit
pub struct Bits {
  words : Array[UInt64]   // 小端：bit i 在 word i/64 的第 i%64 位
  n : Int
}

pub struct BoolMat {
  rows : Array[Bits]      // 列主序；每列長 ncols
  ncols : Int
}

pub struct ChainComplex {
  dims : Array[Int]                  // dims[k] = dim C_k
  boundaries : Array[Array[Bits]]    // boundaries[k] = d_k 的列
}
```

`ChainComplex::betti` 直接以

$$
\beta_k=\dim C_k-\mathrm{rank}\,d_k-\mathrm{rank}\,d_{k+1}
$$

計算；`check_d2` 逐列驗證 $d_{k-1}d_k=0$，等於在程式中執行鏈複形公理。

### 8.2 測試清單（44 個，全綠）

- `core`（5）：rank、矩陣乘對照純量參考、圓周同調、過濾三角形持久同調、有限體算術。
- `homotopy`（8）：$S^1,S^2,T^2,\mathbb{RP}^2$、Möbius 帶的 Betti 數；$\Delta^3$ 與 $S^2$ 的內角填充；$\mathbb Z/2,\mathbb Z/3$ 棒複形；span 結合律、單位律、拉回對照。
- `algebra`（11）：monad 三律、常數摺疊不變性、分配律六邊形、substitution 成本；A∞ 三例；E∞ 分量可縮；自由 E∞ 維度；Heisenberg 對易子；Wick DP vs 樸素；特徵標；rank variety。
- `derived`（7）：ADE 的 $\mu$、$\tau=\mu$、Hilbert 函數、箭圖 Ext。
- `cubical`（13）：區間的 De Morgan 代數與面格判定；CubeTy 預層律（Glue、$\Sigma/\Pi$、Path、函數型）；glue/unglue 計算與 Glue 型傳輸；comp/hcomp 填補與不合盒拒收；ua$\beta$、ua$\eta$ 兩邊來回程；$\mathcal U$ 中的 comp；沿 $\mathsf{ua}(\neg)$ 搬運結構（AND 變 OR）。詳見 §10 與 `docs/cubical.md`。

指令：

```bash
export PATH="$HOME/.moon/bin:$PATH"
cd moonmath
moon test --target wasm      # 44/44
moon run --target native bench
```

### 8.3 套件邊界與依賴

`core` 只依賴標準庫的 `Array`、`StringBuilder`；`homotopy/algebra/derived/cubical` 以 `using @core { type Bits, ... }` 匯入核心型別；`bench` 依賴全部。依賴圖是 DAG，沒有循環。

### 8.4 可重現性

所有例子都是有限、確定性的：三角剖分寫死頂點數；$p=1009$ 或 $p=2$；隨機矩陣用固定 LCG 種子。基準使用 `moonbitlang/core/bench` 的單調時鐘，只量測 CPU 時間區間，不影響計算結果。

---

## 9. 限制與後續

1. **僅到 $m_3$**：A∞ 檢查截斷在三階；更高 $m_n$ 需要稀疏張量與 bar 構造的遞迴實作。
2. **特徵 $p$ 的導出模空間**：Lurie 定理在特徵 0；$\mathbb F_p$ 上我們只做 Jacobian 環與 Koszul 型計算，未建構完整的 simplicial localization。
3. **VOA 支撐簇**：目前是 exterior/Clifford 模的 rank variety 模型；完整的 VOA 上同調支撐簇需要 Zhu 代數的具體表示與 Ext 計算。
4. **HoTT**：§10 與 `cubical/` 已實作有限立方體模型中的 Glue、comp 與單價的計算內容；但仍未實作完整 dependent type checker（沒有型別檢查器、沒有高階歸納類型），模型亦限於有限集宇宙。
5. **複雜度**：$E(r)$ 的列舉仍是 $r^{r+D}$，可用生成函數／Barratt–Eccles 的表格化進一步降低。

---

## 10. 立方體單價：把公理變成演算法

本節概述 `cubical/` 套件，完整版（定義、定理證明、複雜度表）見專文 `docs/cubical.md`。

在書本版 HoTT 中單價是一條公理：$\mathsf{transport}\,(\mathsf{ua}\,e)$ 不計算。CCHM 的立方體類型論引入 Glue 型與 Kan 合成 `comp`，令單價成為有演算法內容的定理。我們在一個**有限立方體模型**中實作這個轉換：

- **區間與面格**（`interval.mbt`）：維度項形成自由 De Morgan 代數，相等由 DNF 正規形判定（`dim_eq`）；餘纖維的相等與蘊含由它在 $3^n$ 個子立方體上的外延判定（`cof_equiv`、`cof_entails`，外延重用 §2 的 `Bits`）。特別地 $(i{=}0)\vee(i{=}1)\ne\top$。
- **有限立方體類型**（`cubety.mbt`）：`CubeTy` 是面偏序上的有限圖式（每格一個有限集、每對面包含一個限制映射）；型形成子包括離散型、積、常值基底的 $\Sigma/\Pi$、函數型（限制＝共軛）、Path 型（路徑即線）與 Glue 型。
- **Glue**（`glue_ty`）：$\mathsf{Glue}\,[\varphi\mapsto(T,e)]\,A$ 在 $\varphi$ 的外延上嚴格等於 $T$，在外等於 $A$；自外向內的限制被 $e^{-1}$ 扭轉。這正是 ua 端點嚴格成立的機制。
- **comp**（`comp.mbt`）：合成是有限 Kan 填補——枚舉泛型格的元素，保留限制等於管（tube）與帽（cap）者，再讀出 $i=1$ 的 lid；`hcomp` 是常值延拓上的特例，`transp` 是空管特例。$\mathcal U$ 中的 comp 由 CCHM 公式 $e'=\mathsf{transp}^A\circ e\circ(\mathsf{transp}^E)^{-1}$ 再 Glue 實現（`comp_universe`），由此構造宇宙中路徑的複合（`comp_path_universe`）。
- **單價**（`univalence.mbt`）：$\mathsf{ua}(e)=\lambda i.\,\mathsf{Glue}\;B\;[(i{=}0)\mapsto(A,e),\ (i{=}1)\mapsto(B,\mathrm{id})]$；

$$
\mathsf{transport}\,(\mathsf{ua}\,e)\,a
=\mathsf{comp}^i(\mathsf{ua}\,e\,,\,[\ ]\,,\,a)=e(a)
$$

是程式執行結果（`check_ua_beta`），對 Fin 3 的 6 個、Fin 4 的 24 個等價窮舉成立，benchmark 再驗證 Fin 6 的 720 個（約 6.9 ms）。`idtoeqv`（沿線傳輸）與 `ua` 兩邊在運算上互逆（`check_ua_eta` 驗證逐格自然同構），即有限集宇宙中 $(A\simeq B)\simeq(A=_{\mathcal U}B)$。結構搬運亦計算：布爾運算 AND 沿 $\mathsf{ua}(\neg)$ 在函數型中傳輸得 OR（De Morgan 對偶）。

由此 Homotopy 層的敘事與立方體計算接通：路徑不再是公理化的等同，而是立方體（§2 的單形窮舉是 $\infty$-範疇的組合面，本節的立方體圖式是其類型論面）。

---

## 11. 參考文獻（節選）

1. A. Joyal, *Quasi-categories and Kan complexes*, J. Pure Appl. Algebra 175 (2002).
2. J. Lurie, *Higher Topos Theory*, Princeton, 2009；*Higher Algebra*, 2017.
3. M. Shulman, *Homotopy type theory: the logic of space*, 2017.
4. Univalent Foundations Program, *Homotopy Type Theory*, 2013.
5. S. Mac Lane, *Categories for the Working Mathematician*, 2nd ed., 1998.
6. J. Stasheff, *Homotopy associativity of H-spaces I, II*, Trans. AMS 108 (1963).
7. B. Keller, *Introduction to A-infinity algebras and modules*, 2001.
8. T. Kadeishvili, *On the homology theory of fibre spaces*, 1982.
9. M. Markl, S. Shnider, J. Stasheff, *Operads in Algebra, Topology and Physics*, 2002.
10. J. McClure, J. Smith, *A solution of the Deligne–Getzler–Kapranov conjecture*, 2003.
11. C. Berger, B. Fresse, *Combinatorial operad actions on cochains*, 2004.
12. E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2004.
13. Y.-Z. Huang, *Two-dimensional Conformal Field Theory and Vertex Operator Algebras*, 1997.
14. Y. Zhu, *Modular invariance of characters of vertex operator algebras*, JAMS 9 (1996).
15. V. Palamodov, *Deformations of complex spaces*, 1976.
16. G.-M. Greuel, C. Lossen, E. Shustin, *Introduction to Singularities and Deformations*, 2007.
17. L. Avramov, D. Eisenbud, *Regularity of modules over a Koszul algebra*, 1992.
18. MoonBit 官方文檔與更新：`https://docs.moonbitlang.com`、`https://www.moonbitlang.com/updates`。
19. C. Cohen, T. Coquand, S. Huber, A. Mörtberg, *Cubical Type Theory: a constructive interpretation of the univalence axiom*, TYPES 2015 / FLAP 4 (2017), arXiv:1611.02108。
20. S. Huber, *Canonicity for Cubical Type Theory*, J. Autom. Reasoning（2019）。
21. *Cubical Agda* 文檔：Glue、comp、transp、hcomp 與 uaβ 的原始定義（`agda.readthedocs.io` 語言參考「Cubical」）。

---

### 附：一句話總結

把 $\infty$-結構拆成**有限位元矩陣＋可檢查方程**，用 MoonBit 的單態化與 `#inline` 把抽象壓成零成本；同調、持久同調、Wick 收縮、A∞/E∞ 公理與導出奇點不變量於是在同一個編譯期框架內可計算、可驗證、可加速。
