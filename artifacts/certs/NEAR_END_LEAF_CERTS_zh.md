# 近端叶闭合证书登记

- 存活叶：**17**
- 已挂脚本：**17**
- harness 全 UNSAT（z3+cvc5）：**7**
- 另有 z3/精确证书全通过：**10**
- **合计全证书级闭合：17/17**

诚实：挂接 ≠ Lean 几何证明；PDF 模块仍是几何权威。

| 叶 | 模块 | harness | 全证书 | 几何假设（摘要） |
|---|---|---|---|---|
| bothMeet/meet/pos | R13 | False | True | Near-end G2 normalisation; centre mid in C; F-horizontal sign + |
| bothMeet/meet/neg | R13 | False | True | Near-end G2; centre mid in C; F-horizontal sign − |
| bothMeet/gap/empty | R14 | False | True | Near-end G2; left status gap; F axis-aligned |
| bothMeet/meet/empty | R16 | False | True | Near-end G2; F axis-aligned; both outer meet |
| bothMeet/gap/neg | R17 | False | True | Near-end G2; left gap; F sign − |
| bothMeet/gap/pos | R18 | False | True | Near-end G2; left gap; F sign + |
| topGap/gap/empty | R19 | False | True | Near-end G2; topGap; left gap; F axis-aligned |
| topGap/gap/neg | R19 | False | True | Near-end G2; topGap; left gap; F − |
| topGap/meet/pos | R19 | False | True | Near-end G2; topGap; left meet; F + |
| topGap/meet/neg | R19 | False | True | Near-end G2; topGap; left meet; F − |
| topGap/meet/empty | R26 | True | True | Near-end G2; topGap; left meet; F axis-aligned — main R26 branch |
| rightGap/meet/empty | R27/R28 | True | True | Near-end G2; rightGap; dual-branch closure |
| rightGap/meet/pos | R27/R28 | True | True | Near-end G2; rightGap |
| rightGap/meet/neg | R27/R28 | True | True | Near-end G2; rightGap |
| rightGap/gap/empty | R27/R28 | True | True | Near-end G2; rightGap; left gap |
| rightGap/gap/pos | R27/R28 | True | True | Near-end G2; rightGap |
| rightGap/gap/neg | R27/R28 | True | True | Near-end G2; rightGap |

## 各叶几何假设详情
### bothMeet/meet/pos（R13）
- **rt**: outer R and T both meet the square
- **left**: left ray meets
- **fh**: F has positive horizontal component (rightward)
- **closer**: R13 pair/closures: positive F projection + three-ray budgets
- **assumes**: Near-end G2 normalisation; centre mid in C; F-horizontal sign +

### bothMeet/meet/neg（R13）
- **rt**: outer R and T both meet
- **left**: left ray meets
- **fh**: F has negative horizontal component
- **closer**: R13
- **assumes**: Near-end G2; centre mid in C; F-horizontal sign −

### bothMeet/gap/empty（R14）
- **rt**: R and T both meet
- **left**: left gap
- **fh**: F horizontal empty (axis-aligned F)
- **closer**: R14 J-certificate / bridge / junction
- **assumes**: Near-end G2; left status gap; F axis-aligned

### bothMeet/meet/empty（R16）
- **rt**: R and T both meet
- **left**: left meets
- **fh**: F horizontal empty
- **closer**: R16 gap-phase / geometric reduction / interval cover
- **assumes**: Near-end G2; F axis-aligned; both outer meet

### bothMeet/gap/neg（R17）
- **rt**: R and T both meet
- **left**: left gap
- **fh**: F horizontal negative
- **closer**: R17 analytic negative projection
- **assumes**: Near-end G2; left gap; F sign −

### bothMeet/gap/pos（R18）
- **rt**: R and T both meet
- **left**: left gap
- **fh**: F horizontal positive
- **closer**: R18 positive projection
- **assumes**: Near-end G2; left gap; F sign +

### topGap/gap/empty（R19）
- **rt**: top outer gap (T misses)
- **left**: left gap
- **fh**: F horizontal empty
- **closer**: R19 top-gap closures
- **assumes**: Near-end G2; topGap; left gap; F axis-aligned

### topGap/gap/neg（R19）
- **rt**: topGap
- **left**: left gap
- **fh**: F horiz −
- **closer**: R19
- **assumes**: Near-end G2; topGap; left gap; F −

### topGap/meet/pos（R19）
- **rt**: topGap
- **left**: left meet
- **fh**: F horiz +
- **closer**: R19
- **assumes**: Near-end G2; topGap; left meet; F +

### topGap/meet/neg（R19）
- **rt**: topGap
- **left**: left meet
- **fh**: F horiz −
- **closer**: R19
- **assumes**: Near-end G2; topGap; left meet; F −

### topGap/meet/empty（R26）
- **rt**: topGap
- **left**: left meet
- **fh**: F empty
- **closer**: R26 g2_top dual harness
- **assumes**: Near-end G2; topGap; left meet; F axis-aligned — main R26 branch

### rightGap/meet/empty（R27/R28）
- **rt**: right outer gap
- **left**: left meet
- **fh**: F empty
- **closer**: R27/R28
- **assumes**: Near-end G2; rightGap; dual-branch closure

### rightGap/meet/pos（R27/R28）
- **rt**: rightGap
- **left**: meet
- **fh**: +
- **closer**: R27/R28
- **assumes**: Near-end G2; rightGap

### rightGap/meet/neg（R27/R28）
- **rt**: rightGap
- **left**: meet
- **fh**: −
- **closer**: R27/R28
- **assumes**: Near-end G2; rightGap

### rightGap/gap/empty（R27/R28）
- **rt**: rightGap
- **left**: gap
- **fh**: empty
- **closer**: R27/R28
- **assumes**: Near-end G2; rightGap; left gap

### rightGap/gap/pos（R27/R28）
- **rt**: rightGap
- **left**: gap
- **fh**: +
- **closer**: R27/R28
- **assumes**: Near-end G2; rightGap

### rightGap/gap/neg（R27/R28）
- **rt**: rightGap
- **left**: gap
- **fh**: −
- **closer**: R27/R28
- **assumes**: Near-end G2; rightGap

