# NHG failing steps

## NHG_K001 — own harness input, compile rejection
Missing cfg(kani) allocator_api feature and duplicate Vec import. Repaired owned scratch input; no shared infrastructure change. No native credit.

## NHG_K002 — public producer field append
Assertion: for arbitrary word u32, prior initialized prefix n<=1880, the exact frozen loop iteration rejects value>=P without writes, otherwise appends exactly four LE bytes and preserves every prior byte. Exact KMX patch, deployed features, frozen graph/lock validated. CBMC timed out at90s; exit1,92.81387583306059s wall,1943780KiB RSS,swap0. No correctness counterexample, no credit, no unchanged rerun, no limit increase. Source snapshot in K002/sources. This is a TOOL LIMIT. Replacement must split an arbitrary observed window plus Lean KMX frame composition; reducing the caller domain alone is not closure.

## NHG_L004 — own model statement shape
The draft asserted structural Code equality even though source has extra lifted map_err/try steps. The observed Result and ordered effects, not literal Code syntax, are the target. Replaced by equality of Code.run in L005; both source and code theorems then pass with standard axioms. L004's failed compilation printed sorryAx for an unsolved tactic goal; its object is EXCLUDED and superseded by L005, never admitted. No new axiom was declared.

## NHG_K003 — split predecessor
One native field iteration with an arbitrary initialized Vec of length n<=1880 and capacity1884, arbitrary selected prior byte, and arbitrary u32 word PASSES (55.64446209510788s,1287936KiB RSS,swap0). This is only the no-growth branch. Caller capacity is NOT assumed to satisfy it: reallocation remains a named obligation. No full producer admission follows from this pass.
