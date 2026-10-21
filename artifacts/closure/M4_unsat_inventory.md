<!-- auto-status batch26f-docs -->
**Status 2026-10-22 Asia/Shanghai:** exact batch24–26f family = **151** (checker PASS 151/151 at `80e8ee0`); remaining (S) from post-batch25 set of 91 = **0**. Handoff: `CERT_TO_LEAN_HANDOFF.md`. Clearing (S) ≠ theorem proved.


# M4：z3-UNSAT 步骤清单与第二路线状态（peer_ready 定稿计数）

**数据来源：** `certs/z3_second_route_progress_zh.md` 与 `certs/item3_certs/`。  
**历史脚本级合计：** 各 check 脚本报告的 UNSAT 之和为 **403**（已去掉 R29 original 副本）。  
**去重后跟踪集：** cvc5-only 队列去重后 **260** 条；加上第一轮 exact **121** 与 hand **10**，与队列升级结果合计跟踪 **391** 条唯一查询（队列原始行数 272，含 12 行重复键）。

**状态标签：** `exact` / `hand` / `cvc5-only` / `open`（定义同前）。

---

## 1. 总表（唯一查询）

| 状态 | 条数 | 说明 |
|---|---|---|
| exact（第一轮 harness） | 121 | FM/Farkas / 单变量 CAD 等 |
| hand / Bernstein 补证 | 10 | R28/R32/R36/R35k/R41 等 |
| exact（Item3 自队列升级） | 109 | Bernstein / 有理 IBB / Or 分拆等 |
| **cvc5-only（仍无精确证书）** | **0** | 原 batch25 后 91 条 (S) 已全部升级为 batch24–26f 族可核 (E)/(H)（PASS 151/151） |
| open | 0 | |

**精确/手证第二路线：** **240**（约占跟踪唯一集的 61.4%）  
**仍仅 cvc5（跟踪的 post-batch25 (S) 集）：** **0**；batch24–26f 族可核 exact/hand **151**

诚实说明：cvc5-only **不能**写成机器无关证明。历史“403”与去重后 “391” 的差额来自队列重复键及跨脚本重复计数，不以抬高 exact 比例的方式隐瞒。

机器可读计数：`artifacts/closure/certificate_counts.json`；剩余清单 `S_tier_remaining.json`（0）。

---

## 2–3. 细目与已闭模块

见 `z3_second_route_progress_zh.md` 与既有 R15/R31/R37/R41 闭包说明。R41 两 JSON 已入 `sources/`，219 系数核验通过。

---

## 4. 主文 §12 措辞（已并入）

（E）精确证书；（H）手证；（S）双求解器 UNSAT。本稿对（S）不声称机器无关证明。当前跟踪唯一集中约 **61%** 为（E）或（H），约 **39%** 为（S）。

---

## 5. 完成度声明

**不宣称**全部查询已 exact。仍余 **91** 条（S）。送外部审稿时必须保留本声明。


---

## 6. 2026-10-21 inventory pointer

Public remaining-(S) ledger: `S_tier_inventory.md` / `S_tier_remaining.json` / `item3_certs/`.
Headline unique remaining (S) after batch24 family: **91** (see `S_tier_inventory.md` / `certificate_counts.json`). Prior Item3-only figure was 151.


---

## 7. 2026-10-22 batch24 family

Added **26** machine-checkable Bernstein / rational-IBB / half-angle-identity certificates under
`item3_certs/exact_certs_batch24/`, verified by `scripts/check_exact_certs_batch24.py` (PASS 26/26).
Remaining **(S) = 125**. Private name-only “exact-hand” labels without payloads were not counted.


---

## 8. 2026-10-22 batch25 continuation

Further checkable conversions; family total **60** certs (PASS). Remaining **(S) = 91**.
