# NCB U00 — OPEN

Imports NBQ_Filled, NBC_Filled, NBP allocation/zero ports and NBS_FilledTrace unchanged. NCB_ResizeStep.next proves the standard-library model resize step appends exactly one value on arbitrary model prestate. NCB_Filled14759.model/selected instantiate the inherited model result at the exact preparation size. Neither is a native ownership or lifetime theorem.

Native K002 passes one actual byte Vec resize on arbitrary old byte/value and old length0..1, with spare capacity2. It establishes exact returned length, old/new cells, pointer and capacity. K001 fails the intended false-copy assertion with identical KMX hooks. K003's corresponding symbolic u32 window TIMEOUTs at90s; no credit or unchanged rerun. Next replacement splits fixed old length and selected postconditions.

K005 inherited arbitrary-positive ZST request is unbounded: std extend_with executes n iterations even for a zero-sized value. A finite small unwind bound cannot prove that domain. A bounded check must state its bound; it cannot replace arbitrary-size initialization/ownership. The replacement is a one-step/frame association plus existing NBS induction, not a whole14759-step unwind.

Still OPEN: actual arbitrary-positive-size returned allocation, initialization trace association, ownership, reserve-success/failure linkage and cleanup/lifetime through both expansions/view/preparation. No caller domain is silently narrowed. The exact NativeFilled14759 statement remains open.
