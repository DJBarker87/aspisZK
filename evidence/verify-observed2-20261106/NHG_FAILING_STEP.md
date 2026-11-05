# NHG failing steps

## NHG_K001 — own harness input, compile rejection
Missing cfg(kani) allocator_api feature and duplicate Vec import. Repaired owned scratch input; no shared infrastructure change. No native credit.

## NHG_K002 — public producer field append
Assertion: for arbitrary word u32, prior initialized prefix n<=1880, the exact frozen loop iteration rejects value>=P without writes, otherwise appends exactly four LE bytes and preserves every prior byte. Exact KMX patch, deployed features, frozen graph/lock validated. CBMC timed out at90s; exit1,92.81387583306059s wall,1943780KiB RSS,swap0. No correctness counterexample, no credit, no unchanged rerun, no limit increase. Source snapshot in K002/sources. This is a TOOL LIMIT. Replacement must split an arbitrary observed window plus Lean KMX frame composition; reducing the caller domain alone is not closure.

## NHG_L004 — own model statement shape
The draft asserted structural Code equality even though source has extra lifted map_err/try steps. The observed Result and ordered effects, not literal Code syntax, are the target. Replaced by equality of Code.run in L005; both source and code theorems then pass with standard axioms. L004's failed compilation printed sorryAx for an unsolved tactic goal; its object is EXCLUDED and superseded by L005, never admitted. No new axiom was declared.

## NHG_K003 — split predecessor
One native field iteration with an arbitrary initialized Vec of length n<=1880 and capacity1884, arbitrary selected prior byte, and arbitrary u32 word PASSES (55.64446209510788s,1287936KiB RSS,swap0). This is only the no-growth branch. Caller capacity is NOT assumed to satisfy it: reallocation remains a named obligation. No full producer admission follows from this pass.

## NHG_E001 — extractor loop collapse
SemanticPublic and its carriers were made visible. Charon succeeded; Aeneas exited2 with Not_found at InterpReduceCollapse.collapse_ctx_following_sequence (1991), reached through loop evaluation. No generated Lean body is admitted. Single extraction allowance1/1 used; retain LLBC and exact tool/source/lock pins. Existing canonical model bodies remain available.

## NHG_K011 — complete begin pre-state log
Exact fifteen-call control with arbitrary child post-cursors and full32-byte before-state logs timed out (exit1,99.59319115290418s wall,1565432KiB RSS,swap0). No counterexample or credit. Replacement splits the extra before-state observation to ONE arbitrary byte with a Lean array-extensional frame lift; existing full next-state control is reused from NGX, not rerun unchanged. No timeout/cap increase.

## NHG_K012 — begin per-byte complete-history shape
Replacing full before-state logs by a single observed byte still timed out (95.07911560195498s wall,1470112KiB RSS,swap0). No native credit or rerun. Next split: ONE arbitrary callee window on arbitrary incoming state, with the unchanged NGX control certificate for the overall call sequence and the Lean frame chain connecting windows.

## NHG_K022/K023 — frontier Vec histories
K022 complete20-poststate history timed out:96.48332149209455s,3961660KiB RSS,swap0. K023 ONE arbitrary field window with a second full fresh Vec also timed out:93.62694365507923s,6347736KiB RSS,swap0. Neither is credited or rerun unchanged. Replacement uses the proved FieldBounds.source prefix frame: retain the full arbitrary existing prefix, append an arbitrary0..32-byte suffix in the selected window, and preserve the same mutable Vec place. This weak envelope includes every actual field post-value; no canonicality/success premise. Native capacity remains a local witness under explicit retained Std interpretation. Strict control forces an actually appended byte.

K024: arbitrary-window frontier with prefix-preserving appended suffix timed out at the unchanged 90-second solver limit. No credit. K025 fixes the callee index to zero, partitioning the 20-case control disjunction; all pre-state bytes and admissible lengths remain arbitrary.

K025: fixed window zero still timed out (96.37 s wall), no credit. K026 removes the oracle's suffix-copy construction, using only a safe-for-this-allocation initialized-tail set_len: the harness initially initializes all 1884 u8 slots before truncate; u8 has no destructor. Any exposed suffix is independent arbitrary initialized storage. This is an output oracle constrained by the proved child envelope, not a copy implementation or a native child proof. The parent still executes the exact 20-call control sequence, arbitrary window, lengths, prior bytes and error payload.

K026: 20-call arbitrary-window initialized-tail oracle timed out, no credit. K027 splits the source control at one callee boundary: one native arbitrary row/counter, same Vec, full raw frontier, full arbitrary initialized pre-state and suffix; no other frontier stage is executed natively. Lean source-to-chain equality and induction must compose all 20 steps before closure.

K031: producer routing cut hit outer 180 s limit after optimized compilation (4.51 s) and the harness checking banner, before any CBMC verification result or solver-timeout message. Exit 124; no native credit, not a Rust build success certificate. Do not rerun unchanged. Split at the public producer prefix/tail boundary and copied-snapshot windows; caller state/effects composition remains OPEN.

K044: full three-callee arbitrary-window tail timed out at90s solver (98.77 s wall), no credit. K045 splits at ONE callee boundary with arbitrary current Vec, arbitrary role old-frontier/next-root/new-frontier, typed immutable transition, exact error and owned Vec return; full three-call frame chain is model-side. No unchanged rerun or cap increase.

Public-transcript fidelity correction before admission: K029/K030 used the Wire Error type in the producer cut, whose map_err discards its argument. The frozen producer actually returns the distinct aspis_core::state_only_prefix::r0::Error. K029/K030 remain support only; K047/K048 will use that exact producer error type and arbitrary payloads. No nominal error-layout equivalence is assumed and no row was admitted from the earlier cut.
