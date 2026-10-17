# 把單價公理轉換成立方體演算法：Glue、comp 與有限立方體模型

> 模組：`arena/moonmath`　·　套件：`cubical/`（`interval.mbt`、`cubety.mbt`、`comp.mbt`、`univalence.mbt`）　·　工具鏈：`moonc v0.10.15+943464bfa`
>
> 測試：`moon test --target wasm` 與 `--target native` 均為 44/44（其中 `cubical` 新增 13 個）。

---

## 摘要

在《同倫類型論》（HoTT Book）入面，單價（univalence）係一條**公理**：

$$
\mathsf{ua} : (A \simeq B) \to (A =_{\mathcal U} B),
\qquad
\mathsf{transport}\,(\mathsf{ua}\,e)\,a \equiv e(a)\ \text{只能命題地成立（ua}\beta\text{）}。
$$

因為係公理，左邊嘅傳輸（transport）唔識計數——佢係 stuck term。Cohen–Coquand–Huber–Mörtberg（CCHM 2015/2018）嘅立方體類型論（cubical type theory）唔同：佢直接操作 $n$ 維立方體，引入 **Glue 類型**同 **Kan 合成運算 comp**，令單價變返一條**有演算法內容嘅定理**：$\mathsf{transport}\,(\mathsf{ua}\,e)$ 真係會一步步計到去 $e$。

本文就係把呢個轉換落地成 MoonBit 程式。我哋喺一個**有限立方體模型**入面實作：類型係立方體面偏序上嘅有限圖式（finite diagram）、等價係有限集同構、comp 係有限搜尋嘅 Kan 填補（Kan filling）。喺呢個模型入面：

1. 區間同面格（face lattice）嘅相等與蘊含係可判定嘅演算法（DNF 正規形＋子立方體外延）；
2. Glue 喺外延面上嚴格等於被貼上嘅類型，限制映射經 $e^{-1}$ 扭轉——呢點正係 ua 端點嚴格成立、ua$\beta$ 識計數嘅原因；
3. $\mathsf{ua}(e) := \lambda i.\,\mathsf{Glue}\;B\;[(i{=}0)\mapsto(A,e),\ (i{=}1)\mapsto(B,\mathrm{id})]$，而「transport 沿 $\mathsf{ua}(e)$」就係對呢條 Glue 線做一次 comp，輸出逐點等於 $e$；
4. 以上全部用窮舉測試驗證：Fin 3 嘅 6 個、Fin 4 嘅 24 個等價喺測試入面逐個行勻 ua$\beta$ 同兩邊來回程（round trips），benchmark 再行勻 Fin 6 嘅 720 個（約 6.9 ms）。

換句話講：單價公理喺度唔再係假設，而係一隻由 Glue＋comp 砌出嚟、跑得又驗得嘅程式。

---

## 1. 區間、面格與餘纖維

### 1.1 定義（區間的 De Morgan 代數）

立方體集合嘅區間 $\mathbb I$ 有端點 $0,1$、反轉 $\neg$、以及連接（connections）$\wedge,\vee$，滿足 **De Morgan 代數**律（有界分配格＋對合反轉）。維度項（dimension terms）：

$$
r,s ::= 0 \mid 1 \mid i \mid \neg r \mid r \wedge s \mid r \vee s .
$$

注意 $\mathbb I$ **唔係** Boolean 代數：$i \wedge \neg i \neq 0$、$i \vee \neg i \neq 1$。代碼對應 `Dim`（`DZero/DOne/DVar/DNot/DAnd/DOr`）。

### 1.2 定理（維度項相等可判定）

把 $\neg$ 用 De Morgan 律推到去原子，再寫成析取範式（DNF）、做吸收（$x \vee (x\wedge y)=x$）與字典序排序，得到唯一正規形。兩個維度項喺自由 De Morgan 代數入面相等，當且僅當正規形相同。代碼：`Dim::dnf`、`dim_eq`。測試驗證 De Morgan 律、分配律、吸收律，以及非-Boolean 兩點。

維度項可以喺三值 Kleene 語義下求值（`Dim::eval3`）：變量賦值 $0$（偽）、$1$（真）或 $*$（自由），$\wedge,\vee$ 取 $0 < * < 1$ 序嘅 min、max，$\neg$ 翻轉而 $\neg * = *$。求值結果係 $0/1$ 定係 $*$，決定一條方程式喺子立方體上係咪被迫成立。

### 1.3 定義（子立方體與面關係）

$n$ 維立方體嘅一個**子立方體**由每維一個三進制數字決定：$0$、$1$（釘喺面）或 $*$（自由），所以一共有 $3^n$ 個子立方體；以三進制碼編號（`pow3`、`subcube_digit`）。面關係 $\tau \subseteq \sigma$：逐維檢查（$\sigma$ 釘咗嘅維，$\tau$ 必須跟住；$\sigma$ 自由，$\tau$ 任意）。交集 `meet_cube` 逐維取訊息量較大者，衝突即不交。

### 1.4 定義（餘纖維／面公式）

面格 $\mathbb F$ 由方程式 $(r = \varepsilon)$（$\varepsilon\in\{0,1\}$）以 $\wedge,\vee,\top,\bot$ 生成。一個餘纖維 $\varphi$ 喺子立方體 $\sigma$ 上**成立**，當且僅當每個方程式喺 $\sigma$ 上被迫為常數，即用 §1.2 嘅三值求值得到正正係 $\varepsilon$ 而非 $*$。代碼：`Cof`、`Cof::holds`、面餘纖維 `face_cof(dim, eps)` 即 $(i=\varepsilon)$。

### 1.5 定理（外延判定）

餘纖維由它嘅**外延**決定：$\mathrm{ext}(\varphi)=\{\sigma \mid \varphi\ \text{喺}\ \sigma\ \text{上成立}\}$，一個對子面封閉（downward closed）嘅子立方體集合，用核心套件嘅 `Bits` 位集合表示。於是：

$$
\varphi = \psi \iff \mathrm{ext}(\varphi)=\mathrm{ext}(\psi),
\qquad
\varphi \le \psi \iff \mathrm{ext}(\varphi)\subseteq \mathrm{ext}(\psi),
$$

全部可以數 $3^n$ 個子立方體判定（`Cof::extent`、`cof_equiv`、`cof_entails`）。兩個重要例子：

- $(i{\wedge}j = 0)$ 同 $(i{=}0)\vee(j{=}0)$ 外延相同（連接同面格咬合）；
- $(i{=}0)\vee(i{=}1) \ne \top$：佢嘅外延欠咗泛型子立方體（generic cube）——正係呢個「中間冇釘死」，先容許 §5 嘅 $\mathsf{ua}$ 線有一個真正中間嘅類型。

外延嘅極大子立方體（`cof_maximal_faces`）有限個就覆蓋外延；部分元素（partial elements，見 §4）正係逐個極大面比一個分量。

---

## 2. 有限立方體類型

### 2.1 定義（`CubeTy`）

一個 **$n$ 維有限立方體類型**係面偏序 $\{0,1,*\}^n$ 上嘅一個預層圖式：每個子立方體 $\sigma$ 一個有限集（以基數 `card[σ]` 表示，元素編碼做 $0..\mathrm{card}[\sigma]-1$ 嘅整數），每個面包含 $\tau\subseteq\sigma$ 一個**限制映射**

$$
(-)|^\sigma_\tau : X_\sigma \longrightarrow X_\tau,
\qquad
(x|^\sigma_\sigma)=x,\quad
(x|^\rho_\sigma)|^\sigma_\tau = x|^\rho_\tau \ (\tau\subseteq\sigma\subseteq\rho).
$$

一個「上下文入面嘅元素」就係泛型子立方體上面嘅元素 $x\in X_{*^n}$；佢所有面都係限制。`CubeTy::check` 窮舉驗證預層兩律。有限集之間嘅映射一律用圖表陣列表示；有限集等價（isomorphism）以 `Iso { dom, cod, fwd, bwd }` 表示，並有決策程序 `fn_inv`：有限集來講，$\mathsf{isEquiv}\,f$ 可判定且等價於 $f$ 係雙射。

### 2.2 類型形成子

| 形成子 | 代碼 | 語義 |
|---|---|---|
| 離散常值類型 | `const_ty(n, c)` | 每格 `Fin c`，限制恒等；立方體必須常值，路徑即相等命題 |
| 積 | `prod_ty` | 逐格笛卡兒積，元素編碼 $a\cdot|Y_\sigma|+b$ |
| 常值基底上的 $\Sigma$ | `sigma_const_ty` | $\Sigma_{s:\mathrm{Fin}\,m} B_s$，逐格不交并＋累積偏移編碼 |
| 常值基底上的 $\Pi$ | `pi_const_ty` | $\Pi_{s:\mathrm{Fin}\,m} B_s$，元組混合進制編碼 |
| 函數類型 | `fun_ty` | 見 §2.3 |
| 路徑類型 | `path_ty` | 見 §2.4 |
| Glue | `glue_ty` | 見 §3 |
| 面、反轉、常值延拓、換維 | `face_ty`、`reverse_ty`、`extend_ty`、`swap_dims_ty` | 立方體代入（substitution）的有限版本：取面 $i:=\varepsilon$、$i:=\neg i$、加一個冇用嘅新維（degeneracy）、交換坐標 |

### 2.3 函數類型：共軛

當定義域 $A$ 的所有限制映射都係雙射（`all_res_bijective`，ua 線、Glue 線、常值線都有呢個性質），函數類型逐格取集合函數，限制係**共軛**：

$$
(f|^\sigma_\tau) \;=\; \mathrm{res}^B_{\sigma\tau}\;\circ\; f \;\circ\;(\mathrm{res}^A_{\sigma\tau})^{-1}.
$$

呢條式就係「沿等價搬運結構」嘅數學心臟，§5.5 會用到。`fun_ty` 用真值表混合進制編碼每格嘅函數。

### 2.4 路徑類型：路徑即線

$\mathsf{Path}_X\,a\,b$ 嘅 $\sigma$-立方體，正是 $X$ 喺 $\sigma\times\mathbb I$ 上（用 `extend_ty` 加一維）両端面分別係 $a|_\sigma$、$b|_\sigma$ 嘅立方體。`path_ty`
...[truncated 12725 chars]