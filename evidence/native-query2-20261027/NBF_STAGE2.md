# Stage 2: native indexed context and single-row write

K002 passes arbitrary index<64 context, exact row pointer/power/basis/flush and
unchanged Vec pointer/len/capacity/terms: 0/400 failed, 3/3 covers, exit0,
wall29.313408408s, peak526864KiB, swaps0. K003 passes ONE row write on arbitrary
64-row contents, observed at arbitrary row/limb: 0/344 failed, 4/4 covers,
exit0, wall75.044308988s, peak1602984KiB, swaps0. Neither gate executes a64-row
update loop or compares two whole buffers. The boxed-slice allocation removes
the failed NBB append/conversion frame shapes and the context gate is split
from the mutation gate. K003 uses an unrestricted row reply and no multiplication.

NBF_Domain and NBF_Read compile (L002/L003); row phase and actual indexed read
are derived from the SAME cursor/list observation. Canonical power/basis are
still upstream domains, not silently discharged. Source/backend/dependency and
axiom pins are in receipts. Both graph checks equal the frozen graph and lock
hashes before/after equal5782e6a3…. No LPb stage is rerun or credited here.

No headline premise is removed. Next: connect actual emitted loop-body setters
to the global window frame, then query_values and SAME caller composition.
No shipped source changed and no ELF rebuild trigger fired.
