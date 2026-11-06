# NJT retained failures and pending association

Target not yet established. No proof timeout or memory kill has occurred. NJM E001 failed shared-borrow collapse; the changed NJT E001 reference emits successfully. NJM K009 allocation/data timeout is excluded, never retried. NJT allocation/carrier and data cuts remain split.

Own input/elaboration failures: L004 queried missing Std identifiers; L005 imported a legacy duplicate Phase owner, repaired through the coherent NJM import at L007. L006 failed before launch because its prerequisite object was absent. L010 required a constructor alias, repaired at L011–L014. L016/L019 failed the singleton/resize proof; L020 proves it via pinned generic specs. L021 failed an ambiguous singleton simp name; L022 unintentionally retained the same draft because the replacement pattern missed the token, and earns no credit. L023 fixed that name and exposed only Array.make carrier equality; L024 passes the repaired source. These were elaboration failures, not timeout/memory retries.

K001/K002 stopped before verification on missing frozen cfg(kani) input and missing own extern crate alloc. L012 restored the exact pinned predecessor inputs; L015 repaired the own cfg-only import. K003 passes singleton length/allocation identity; K004/K005 each fail exactly the intended corruption. K006 passes the one-iteration resize data window; K007 fails the intended data corruption. All reached runs validate the exact offline frozen graph and unchanged lock.

One attempted L020 submission was refused locally by the own active-client guard while K007 was running; no scope was launched. The eventual L020 compile ran only after K007 completed. No infrastructure bypass occurred.

Remaining129 association: canonicality and allocation-order transport are now proved, including NJT_AllocationLift.named_allocator's complete Result and returned allocator state. The full unsafe uninit/set_len/cast/assume_init P6 packet is still not installed into the cohort's StdCalls reserve/error/heap interpretation. The current std is a returning-success VALUE model. Native selected words, Result tags and address identity are not a proof of that whole interpretation.129 remains OPEN; safe std operations remain under ruling(au), not new child rows. See NJT_REMAINING.md/NJT-F1.

L025–L028 are retained Cohort elaboration drafts; L029 passes the final source. L031 had a reserved-keyword name in allocation_transport; L033 passes. L040/L041 allocation-lift drafts exposed only elaboration/alias issues; L042 passes with standard axioms. No failed-draft sorryAx output enters the module manifest or raw audit.

The final two combined imports (L036/L043), final NFX scan L044 and raw campaign L045/L046 pass. Strict(t) calibration QK006–QK011 produces all six expected verdicts; no new Lean object or third combined audit is introduced by that calibration. No timeout, memory kill, raised cap or renamed-verdict workaround occurred.
