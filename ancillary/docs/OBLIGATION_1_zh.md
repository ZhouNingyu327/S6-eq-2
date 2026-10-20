# 义务 1：平行弦界 B(μ) — 状态（已证 / 未证）

**时间：** 2026-10-20（Asia/Shanghai）  
**Lean：** `ParallelBudgetGeometry.lean` + `ChordIntersection.lean`  
**编译：** `lake build` 通过；**0 axiom / 0 sorry**  
**全定理 S(6)=2：** **已证**（数学完备性；见 UPLOAD_GATE；本文件只记录义务1）

---

## 判定表

| 命题 | 状态 |
|---|---|
| 定向单位正方形模型 `OrientedUnitSquare`（`c≥s>0`）及 `width=c+s≤√2` | **已证** |
| 三角帽假设下 `chordSum = f(width,d)` | **已证** |
| `f(z,d) ≤ d−y`（`y²=d²−1`） | **已证** |
| 临界外侧 + `z²≤2` ⇒ `f ≤ 2(s−d)` | **已证** |
| `B` 两分支均 `<1`；`chordSum ≤ B`；`chordSum < 1` | **已证** |
| **欧氏交长 = `t/(cs)`（左帽）与 `(z−t−d)/(cs)`（右帽）** | **已证** |
| `mem ↔ [Lo,Hi]`（左右帽） | **已证** |
| `TriangularCapCuts` 手稿公式 = 欧氏截长 | **已证** |
| 旗标 `obligation1_fullyClosed` / `residual_chord_length_closed` | **true** |
| 全定理「六块不能盖边长 `2μ>2`」 | **已证**（见 WholeTheoremStatus / UPLOAD_GATE） |

---

## 欧氏模型（左端对齐）

旋转 `[0,1]²` 后平移 `(s,0)`，使 min X = 0、宽 = `c+s`：

```
bodyX = c*(X−s) + s*Y ∈ [0,1]
bodyY = −s*(X−s) + c*Y ∈ [0,1]
```

- 左帽 `0≤t≤s`：交段 `[leftLo,leftHi]`，长 `t/(cs)`
- 右帽 `c≤t≤c+s`：交段 `[rightLo,rightHi]`，长 `(c+s−t)/(cs)`

角点在原点的条带形式经 `X ↦ X+s` 与此模型等价。

---

## 复现

```bash
cd formalization/lean/S6Core && lake build
```
