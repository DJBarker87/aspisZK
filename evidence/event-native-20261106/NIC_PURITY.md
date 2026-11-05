# Native purity progress

Target not yet established. Model interpretation is NIA_EventInterpretation, pinned in NIC_INPUT_PINS.json; NIC_PurityFrame.context_frame composes it on the SAME Context. Native certification is separate.

| Event kind | Native evidence | Status / domain |
|---|---|---|
| one | K001/K002 | positive PASS / reachable-digest control FAIL; constant M31::ONE |
| double | K003/K004 | PASS/FAIL; canonical arbitrary M31 |
| subtract | K005/K006 | PASS/FAIL; two arbitrary canonical M31 |
| trace | K007/K008 | PASS/FAIL; arbitrary tag/index and canonical E; deployed no-prover body |
| opening | K013/K014 | PASS/FAIL; arbitrary proof bytes and i<22 |
| geometry | K011/K012 | PASS/FAIL; one arbitrary row, arbitrary start; full-frame installation still requires accessor law |
| fields | K015/K016 | PASS/FAIL; one selected output index<4 and canonical decoded E; loop-step refinement pending |
| product | K019/K020 | PASS/FAIL; natural-spec stub, NFP_ProductLaw.emitted; every u32 pair |
| circle | K028 | TIMEOUT; split fixed stages next; no credit |
| line | pending | independent fixed-stage split planned |
| dots | pending | one native window plus existing NFM induction required |
| accumulate | pending | one native basis/row/tail step plus NFS induction required |

K021–K027 are failing activation controls for hashv, return-data set/get, CPI invoke/invoke_signed, log and compute-unit log respectively; digest activation is checked in each paired control. All unreachability stubs assert false, no runtime effect is silently turned into a value. No writable static, function-pointer observer or verified-contract substitution is used.

K017 copy-positive PASS and K018 inverted copy control FAIL use the exact KMX patch and same program-root features. Earlier non-copy value properties are not replayed. Geometry/fields full caller installation is explicitly pending; no row is promoted.
