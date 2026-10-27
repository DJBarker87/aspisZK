# Stage 1: indexed stateful array traversal

Checked XRp_FromFnState.indexed_eq and from_fn_state_eq (L026): arbitrary
callback, closure, index, fuel, array size and prior output; all Result branches.
The explicit bounded indexed traversal preserves state and the final-step
index-overflow convention of the ACTUAL core.array.fromFnList definition.
No fabricated emitted sampler loop is used. This is a generic lemma, not the
concrete low_base_p_digits equality or a complete source-to-model refinement.
L018/L019/L020/L022/L023 are excluded failed elaborations, not axioms evidence.
All 17 unchanged XRn_Join kit sources compiled privately in L001-L017; source
hashes and selected direct dependency hashes are retained. No shared object
was written. L026 axioms: propext, Classical.choice, Quot.sound only.

Root inventory is one compile-free traversal; 6428 module names, 152 missing
coherent objects, 19 unresolved source names. It is not a complete kernel audit;
no claim of complete dependency closure is made where source is unavailable.
Canonical missing roots are not all green on RPv_0357's pinned LEAN_PATH.
Root audit deferred, no root repair cascade and no root compile attempted.

No actual-top premises removed, added or changed; 83T/3P/13G unchanged.
Before/after source snapshots are identical. A0-A8 remain OPEN. No accepted
joint root inhabitant or accepted TX1/TX2 fixture is established here.
No shipped/cfg(kani) source, ELF, key, existing theorem or other worker file changed.
