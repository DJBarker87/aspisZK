# Development findings

NEO_K001 stopped at Rust type checking: the own flattening adapter accessed private WideExact fields from a sibling module (eight E0616 errors). No native result is credited. Replaced only that adapter with the already composed public to_limbs getter; NEO_K002/K003 use the corrected input snapshot. This repair changes neither frozen parser bodies nor the property. K002 copy positive PASS, K003 matched deliberately false copy assertion FAIL, under the same frozen-lock graph, exact KMX patch, core r0 helper features, optimized build and scope caps. No writable static, Option<fn>, or function contracts in this new harness.

NEO_L001 passed at exit 0, 4.486200800 s, 4,301,584 KiB, swap 0; printed axioms for all three top theorems are [propext, Classical.choice, Quot.sound]. This is cohort port and frame evidence plus the separately adopted z(1) native specialization, not a whole query theorem. It creates no composed row credit by itself.
