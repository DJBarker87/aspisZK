from pathlib import Path
import json,re
E=Path('docs/research/100bit-spend-path-20261013/evidence/prover-commit54-20261023')
p=Path('docs/research/v8-r0-zk-20261009/r1p-final/PROVER-COMMIT54-20261023.md')
s='''
## Stage 7: actual iterator states and query interfaces

The Stage-5 iterator-state limitation is narrowed here. Verification-only,
compiler-specific representation observers check the actual public constructors
and universally quantified next-state transitions of Copied<StepBy<Iter<T>>>
and Copied<StepBy<Skip<Iter<T>>>>. The element types are the byte-identical
shipped M31, QM31 and WideExact definitions, with arbitrary raw words, not just
canonical representatives. Constructor proofs establish pointer/end, stride,
first-item and skip state; transitions preserve the schema and return the exact
indexed value. Separate stub_verified harnesses compare that value and state
with owned_read. Exhaustion checks cover every even length through 256.
All raw proofs are pinned to Kani's rustc 1.93.0-nightly
(53732d5e0 2025-11-20), not a different installed rust-src tree.
The compiler and libcore hashes are in native-toolchain.txt; field/scalar pins
and the selected-limb body comparison are in native-source-pins.json.
These private-layout observers are not shipped or portable library theorems.

The full WideExact odd-value comparison was stopped after memory growth;
e-copied-odd-transition-v6 exits 1, 183.572 s, 6553352 KiB, swaps 0.
Its replacement checks an arbitrary limb in 0..8, with the same function body
and an unused selector parameter. The verified-stub comparison is correspondingly
pointwise. Universality over the selector yields all eight word equalities;
no full-record stub contract is claimed for that replacement. The retained
representation and source-body checks make the boundary reviewable.
No memory cap was raised and no failed input was rerun unchanged.

J10691 establishes the symbolic successful-step, exhaustion and finite sequence
induction. J10692 additionally identifies this finite sequence with the extracted
owned strided collector. This connects the state schema and owned list model;
Vec allocation and specialized native collect/fold assembly still need binding.
It is not a theorem about the entire native simulator.

The new complete-owner query wrappers are structurally extracted in v3.
J10694 checks the exact query declarations. J10698 proves the U32-to-Usize casts,
folded q/4 parent selection, and both opened C1/C2 and folded byte images at
those query indices, from the derived coefficient producer. No leaf-array
image is assumed. The complete opening producer remains composed at J10687,
with its explicit challenge-representation identities.

J10695/96 were stopped at 64.01/35.34 s, 5979700/5342072 KiB, zero swap,
when definal equality began expanding leaf callers. Opaque source/model
interfaces and an explicit cast equality replace that expansion. J10697 then
finishes in 1.67 s with a scalar-literal type mismatch; J10698 explicitly proves
the denominator value is 4 and removes the diagnostic trace tactics.
Failed snapshots contain elaborator placeholders; no accepted source does.

Accepted native scopes below all exit 0, swaps 0; MemoryHigh=6G,
MemoryMax=8G, MemorySwapMax=0, TasksMax=64. Each exact command, wall time,
peak RSS, source revision/hash snapshot, reservations, and cgroup are retained
in receipts/<name>/receipt.json, <name>-inputs.json and input-snapshots/<name>.
RUSTFLAGS is -C opt-level=3 -C link-arg=-Wl,--threads=4; expected time is
optimized verification compilation plus one named transition/contract check.
#print axioms is not applicable to Rust verification.

| Exact native receipt | Wall s | Peak RSS KiB |
|---|---:|---:|
'''
names=['m-copied-layout-v4','m-copied-transition-v4','m-copied-owned-v5','m-copied-odd-layout-v5','m-copied-odd-transition-v5','m-copied-odd-owned-v5','m-copied-exhausted-v5','q-copied-layout-v6','q-copied-transition-v6','q-copied-owned-v6','q-copied-odd-layout-v6','q-copied-odd-transition-v6','q-copied-odd-owned-v6','q-copied-exhausted-v6','e-copied-layout-v6','e-copied-transition-v6','e-copied-owned-v6','e-copied-odd-layout-v6','e-copied-odd-selected-v7','e-copied-odd-selected-owned-v7','e-copied-exhausted-v7']
for name in names:
 r=json.loads((E/'receipts'/name/'receipt.json').read_text());assert r['exit_status']==0
 s+=f"| {name} | {r['wall_seconds']} | {r['peak_rss_kib']} |\n"
s+='''
Accepted Lean compiles below all exit 0 and swaps 0. Every theorem prints only
a subset of propext, Classical.choice, Quot.sound. Exact revision, source and
dependency hashes, command, cap, raw output and errors are in lean/J*.json.

| Attempt | Exact module | Wall | Peak RSS KiB |
|---|---|---|---:|
'''
for a in [10691,10692,10694,10698]:
 r=json.loads((E/'lean'/f'J{a}.json').read_text());assert r['exit']==0
 wall=re.search(r'Elapsed .*?: (\S+)\n',r['time'])[1];rss=re.search(r'Maximum resident set size \(kbytes\): (\d+)',r['time'])[1]
 s+=f"| J{a} | {r['module']} | {wall} | {rss} |\n"
p.write_text(p.read_text()+s)
