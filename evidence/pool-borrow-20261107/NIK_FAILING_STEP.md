# NIK failing/open step

Stage E001: actual frozen processor::close_program_account_v1, exact NHR staging/lock/metadata, optimized Charon, pinned Aeneas. Charon succeeds; Aeneas exits 2 with non-ADT AccountInfo variant lookup failure in Substitute.ml. No scope semantics extracted; no native mismatch established. One permitted extraction consumed; no repeat.

Stage native certificates: NOT IMPLEMENTED / OPEN. No Kani was launched and no positive or negative control is claimed. The existing local-record SDK counter model does not by itself provide a typed physical interpretation for the actual frozen Pool guard-producing callers. At the three held-guard CPI sites and before_persist callback, a blanket assertion that all counters are nonexclusive would be false as a scope description; exact child footprint disjointness is required. Incoming arbitrary counters require both exclusion and saturation headroom; initial-zero or borrowed-success assumptions have not been derived from every caller. See NIK_OPEN_SITES.md per member.

This is an incomplete native/refinement step, not a Kani timeout, memory limit, compiler verdict, production exploit, soundness failure or proof that a valid native certificate cannot exist. A conditional model cleanup theorem is not substituted for it. The source census and model support are useful partial inputs only.

Lean failed attempts L001/L003/L005/L009/L010 are preserved. All were local elaboration errors, repaired by source changes without new axioms, heartbeat/depth changes or resource increases. L001/L002's rederived exclusive cleanup was superseded by reuse of NIE_AccessorPrecondition.exclusive_counter_roundtrip in L007.
