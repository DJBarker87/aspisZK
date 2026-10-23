# Attempt 26 six-fixture CU comparison

This is a comparison audit of already completed attempt 26 outputs. The authorized S4 comparator is the retained frozen-baseline `stage1_cu` / `settlement_cu` pair in `results/baseline/cu.json`; `b1_stage1` / `b1_settlement` remain separately reported historical strict-B1 values.

| Fixture | Baseline stage1 / settle | Legacy B1 stage1 / settle | Helper933 stage1 / settle | Combined stage1 / settle | Delta vs approved baseline | Delta vs helper933 |
|---|---:|---:|---:|---:|---:|---:|
| transfer-1023 | 1193428 / 1169306 | 1199687 / 1160974 | 1204226 / 1177390 | 1204226 / 1177634 | +10798 / +8328 | +0 / +244 |
| transfer-13 | 1197177 / 1138518 | 1199648 / 1129757 | 1207994 / 1146613 | 1207994 / 1146857 | +10817 / +8339 | +0 / +244 |
| transfer-255 | 1199286 / 1169558 | 1199567 / 1161066 | 1210100 / 1177657 | 1210100 / 1177901 | +10814 / +8343 | +0 / +244 |
| withdrawal-1023 | 1195178 / 1176341 | 1198386 / 1170263 | 1205984 / 1184422 | 1205984 / 1184666 | +10806 / +8325 | +0 / +244 |
| withdrawal-13 | 1193569 / 1148816 | 1198225 / 1138950 | 1204366 / 1156885 | 1204366 / 1157129 | +10797 / +8313 | +0 / +244 |
| withdrawal-255 | 1193699 / 1178769 | 1198264 / 1170523 | 1204498 / 1186862 | 1204498 / 1187106 | +10799 / +8337 | +0 / +244 |

All six approved +12,000 checks: **True**. All six headroom checks (1,183 stage1 / 3,901 settlement): **True**. Outputs match: **True**. Legacy strict B1 all-pass: **False**.

Baseline revision: `b2727acd3abf79315d18b754a260f58f4b1c6326`; baseline-source manifest SHA256 `87b4c5c696e02b2aa433aefab2b99c83c248a0a039b4be68ec58395d61a3d75e`; retained `cu.json` SHA256 `a86721fad52e8b16fe3b1e8f6061ac2b1a6923ec730d7f24d50c601d294a473d`. The referenced baseline cost-probe artifact currently hashes to `dfc2a91ab24e1ec4f57debd8f124cb4f6a3c38ba2662b7318e2e4f3b4acdde34` on the NUC; the historical runner record pins its path/revision but not an execution-time artifact digest.

Combined weights SHA256 `241a4f7dfe57666576b7653556c09d3dedef8606cf02f4ac4cd4cddf5c7663f8`; SBF artifact SHA256 `603af510fca0a54209d6950d814256af257cb8da4e239bbb73e25e01daeb64a2`; helper-only artifact SHA256 `5aac14ef69f482c8b3bc95a400c321288b6a27f2b5b96adabcd21ad0c41019eb`.
