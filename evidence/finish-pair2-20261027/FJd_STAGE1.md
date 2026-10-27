# Stage 1: first P6 attempt and reference algebra

K001 original point constructor/five-digit reference timed out (exit124,
180.279138559s). No proof pass or source counterexample. Full original ten
canonical alpha coordinates were symbolic; constructor and reference ran
without stubs. Resource caps verified6G/8G/swap0/tasks64. Cgroup peak6687219712
bytes; GNU time reports2112KiB because timeout terminated descendants before
child accounting, so that is NOT aggregate RSS. A live sample observed6508208KiB
in CBMC. Scope inactive after timeout. No solver temp file for PID3078749
was found; other jobs' /tmp files were untouched.

Replacement K002 isolates digit0/entry0 while retaining all original inputs
and the full constructor call. It is not an unchanged retry. Other independent
loop harnesses remain available. No cap or timeout increase.

Lean001 proves the four reference entries equal model pairFactor and the
five reference digits equal tensorPoint on the SAME point. This is explicitly
model/reference algebra, NOT an installed constructor value. Exit0,
2.857440645s,5444776KiB,swap0,standard axioms; exact revision, hash,
command and dependency fingerprints in FJd_001/receipt.json.

Budget so far:1/100 Lean,2/20 Kani charged (K002 running).
Complete installed model meanings remains0/7; deployed ledger delta remains0.
No shipped source, top theorem, game, trust item or ELF was changed.
