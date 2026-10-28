# Box value/ownership component

K030–045: eight positive checks PASS and eight exact paired inversions FAIL at
one assertion each; no extra failed/undetermined checks. Actual Box::new, deref,
pointer identity and Drop on complete typed records. Native field domains are
all valid initialized Rust values, including every u32 M31 representation;
no arithmetic is performed. The frame observes an arbitrary record field and
array coordinate plus an independent ambient byte coordinate. Allocator/P6
admission and successful allocation are retained; padding and failed allocation
are not asserted as initialized data or silently discharged.

K029 is excluded: whole-record equality compiled to a memcmp unwinding failure
with 254 undetermined checks. Explicit per-field/per-coordinate equality
constraints replace that own harness assumption, without changing Box or
increasing the unwind/caps. No unchanged killed/timed-out rerun occurred.

The exact KMX patch/stubs and full frozen graph/lock/tool environment match
between each positive/inverted pair (NCF_BOX_AUDIT.json). The actual adapter's
Box wrapper calls the decoder before Box::new; these checks are ONLY the
Box component. They do not prove decoder representability, original iterator
prestate, account-borrow, error/allocator frame or authentication association.
NBX's existing symbolic loop/value/frame laws are reused unchanged; none is
re-proved or relabelled as native caller closure.
