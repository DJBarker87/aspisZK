# R752 literal SCC certificate compilation status

All 40 SCC blocks other than SCC 6 compiled successfully as literal left-inverse certificates. Of these, 39 were the new blocks completed in this continuation; SCC 4 had already been completed before it. The 40 comprise SCC 0–5 and 7–40, with 1,627 scalar entries in total; maximum dimension 16. SCC 6 (dimension 39) remains separately covered by R747–R751.

This proves the generated finite matrix identities and determinant nonzero facts only. It does not connect the matrices to selected verifier execution or close privacy/security.

All jobs used the pinned Lean 4.32 cached workspace, `-j1 -M4500`, cgroup `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`. Full receipt records (source revision/hash, wall time, child peak RSS, swap, full axioms) and the matching NUC `.olean` hashes are in `R752_SUCCESS_INVENTORY.json` and `NUC_OLEAN_SHA256SUMS.txt`. The pinned generator check reports 40 blocks, 1,627 entries, 59 row chunks, certificate SHA `d170dc15f81b0aac68da6cb9291e9907ad72e1738cf3a6b6fd7faf9e32a951f4`.

Every unique final module source matched the source snapshot used by a successful focused compile, and every compiled module has a recorded cached `.olean` hash. There were 139 unique successful module targets: 40 matrix modules, 59 row-chunk modules, and 40 inverse modules. SCC 4 inverse had one failed aggregate attempt, preserved with its exact source/log/receipt, followed by a successful corrected aggregate; no other failed attempts appear in this set.

| SCC | Size | Focused target runs (matrix, row chunks, inverse) |
|---:|---:|---|
| 0 | 6 | Inverse: `1791144748013332000`; Matrix: `1791144726188883000`; Rows01: `1791144733341783000`; Rows02: `1791144741280056000` |
| 1 | 1 | Inverse: `1791144771498263000`; Matrix: `1791144760126971000`; Rows01: `1791144765520757000` |
| 2 | 3 | Inverse: `1791144796158323000`; Matrix: `1791144782982090000`; Rows01: `1791144787990846000` |
| 3 | 8 | Inverse: `1791144825355638000`; Matrix: `1791144802575806000`; Rows01: `1791144807966253000`; Rows02: `1791144816555353000` |
| 4 | 16 | Inverse: `1791144556298809000`; Matrix: `1791144317882369000`; Rows01: `1791144336469554000`; Rows02: `1791144371522965000`; Rows03: `1791144387882307000`; Rows04: `1791144401782541000` |
| 5 | 1 | Inverse: `1791144856491509000`; Matrix: `1791144843875682000`; Rows01: `1791144849046044000` |
| 7 | 2 | Inverse: `1791144873708881000`; Matrix: `1791144863144493000`; Rows01: `1791144868040001000` |
| 8 | 8 | Inverse: `1791144909506155000`; Matrix: `1791144886435045000`; Rows01: `1791144892046524000`; Rows02: `1791144901474858000` |
| 9 | 16 | Inverse: `1791144979405765000`; Matrix: `1791144922734498000`; Rows01: `1791144928746224000`; Rows02: `1791144941310295000`; Rows03: `1791144953784465000`; Rows04: `1791144966678309000` |
| 10 | 1 | Inverse: `1791145016570528000`; Matrix: `1791145002926236000`; Rows01: `1791145010864694000` |
| 11 | 4 | Inverse: `1791145037156138000`; Matrix: `1791145022696198000`; Rows01: `1791145029255431000` |
| 12 | 16 | Inverse: `1791145108875919000`; Matrix: `1791145050017095000`; Rows01: `1791145058057607000`; Rows02: `1791145070458562000`; Rows03: `1791145083353168000`; Rows04: `1791145096150264000` |
| 13 | 4 | Inverse: `1791145137808345000`; Matrix: `1791145125243012000`; Rows01: `1791145130652340000` |
| 14 | 1 | Inverse: `1791145154653090000`; Matrix: `1791145143697664000`; Rows01: `1791145148802932000` |
| 15 | 4 | Inverse: `1791145174815246000`; Matrix: `1791145163120735000`; Rows01: `1791145168179970000` |
| 16 | 2 | Inverse: `1791145192342140000`; Matrix: `1791145181224014000`; Rows01: `1791145186340158000` |
| 17 | 1 | Inverse: `1791145210961696000`; Matrix: `1791145199882815000`; Rows01: `1791145205101425000` |
| 18 | 2 | Inverse: `1791145245661559000`; Matrix: `1791145234306660000`; Rows01: `1791145239762045000` |
| 19 | 4 | Inverse: `1791145265286880000`; Matrix: `1791145253107474000`; Rows01: `1791145258637433000` |
| 20 | 2 | Inverse: `1791145283136810000`; Matrix: `1791145271774793000`; Rows01: `1791145276880029000` |
| 21 | 1 | Inverse: `1791145303731577000`; Matrix: `1791145292535013000`; Rows01: `1791145297793994000` |
| 22 | 8 | Inverse: `1791145343127689000`; Matrix: `1791145317755797000`; Rows01: `1791145323283609000`; Rows02: `1791145334566547000` |
| 23 | 2 | Inverse: `1791145361335425000`; Matrix: `1791145349876027000`; Rows01: `1791145355449191000` |
| 24 | 2 | Inverse: `1791145384245357000`; Matrix: `1791145367633062000`; Rows01: `1791145374063722000` |
| 25 | 2 | Inverse: `1791145406838959000`; Matrix: `1791145395166596000`; Rows01: `1791145400189730000` |
| 26 | 1 | Inverse: `1791145425905244000`; Matrix: `1791145412794398000`; Rows01: `1791145418246357000` |
| 27 | 4 | Inverse: `1791145444870072000`; Matrix: `1791145431766887000`; Rows01: `1791145437587369000` |
| 28 | 2 | Inverse: `1791145462914581000`; Matrix: `1791145451261169000`; Rows01: `1791145456491950000` |
| 29 | 1 | Inverse: `1791145491426656000`; Matrix: `1791145479811427000`; Rows01: `1791145485475990000` |
| 30 | 2 | Inverse: `1791145509247098000`; Matrix: `1791145497533761000`; Rows01: `1791145503287292000` |
| 31 | 2 | Inverse: `1791145529514131000`; Matrix: `1791145517838584000`; Rows01: `1791145523670179000` |
| 32 | 8 | Inverse: `1791145566884160000`; Matrix: `1791145535703825000`; Rows01: `1791145542991638000`; Rows02: `1791145558468000000` |
| 33 | 8 | Inverse: `1791145608373386000`; Matrix: `1791145581710207000`; Rows01: `1791145588381560000`; Rows02: `1791145596926850000` |
| 34 | 4 | Inverse: `1791145635312824000`; Matrix: `1791145615540349000`; Rows01: `1791145625573850000` |
| 35 | 2 | Inverse: `1791145653283513000`; Matrix: `1791145641707560000`; Rows01: `1791145647294994000` |
| 36 | 3 | Inverse: `1791145681139980000`; Matrix: `1791145667641561000`; Rows01: `1791145674235509000` |
| 37 | 4 | Inverse: `1791145706450467000`; Matrix: `1791145687855756000`; Rows01: `1791145698715865000` |
| 38 | 8 | Inverse: `1791145794648796000`; Matrix: `1791145772387729000`; Rows01: `1791145778689698000`; Rows02: `1791145786458697000` |
| 39 | 16 | Inverse: `1791145867150963000`; Matrix: `1791145809895115000`; Rows01: `1791145815246454000`; Rows02: `1791145827386286000`; Rows03: `1791145840929674000`; Rows04: `1791145854223407000` |
| 40 | 1 | Inverse: `1791145893756901000`; Matrix: `1791145882691935000`; Rows01: `1791145887846371000` |

All successful `#print axioms` reports use `[propext, Classical.choice, Quot.sound]`. Matrix-only modules contain no theorem declarations. The complete per-declaration output is preserved in each receipt.
