# pv-alib resume at 86aae376c0

Worktree `/Users/dominic/ZK/.worktrees/pv-alib`, branch
`codex/pv-alib-20261027`. **Target not yet established.**

The initial report is retained verbatim in `REPORT-initial-stop.md`. Lead
ruling D304 supersedes its stop decision: the checked `[17,29]` allocation
mismatch refutes the proposed copy reference, not ledger row V184. Both pinned
and initial native receipts remain in this directory and the counterexample
remains part of this report. No ledger statement was weakened.

## V184 progress

Before: `ProverRwFull.ExternalFuns.op33`, exact complete Result/value law with
allocation/world carrier, arbitrary generic inputs.

The new safe `pop_move_reference<T>` has no Copy/Clone bound and uses
`remove(len-1)` only on a nonempty vector. The optimized pinned nightly native
differential `pop-move-world-03` passes 99 cases: lengths 0–32, capacities
length+0/+1/+17, payload `Result<Vec<u32>,Vec<u8>>`. Native and reference retain
their respective buffer identities and capacities, return identical complete
values and remaining contents, and each make zero alloc/realloc/dealloc calls.
This is a measurement, not an unbounded machine theorem.

No-stub Kani `kani-pop-noncopy-01` passes 697 checks (12 unreachable), arbitrary
bytes and both Result variants, lengths 0–4, unwind 6. No arithmetic stubs or
function replacement was used. Buffer/capacity preservation is checked; the
allocator counts come from the separate native differential, not from Kani.

Lean attempts 52706–52707 prove `PV_AL_PopWorld.complete`, `.retains_buffer`,
`.remaining`, `.zero_allocations`, `.nonvacuous`, and
`PV_AL_PopSelected.{callback,consumed,world_projection}`. These use an explicit
world and retained buffer/capacity carrier; arbitrary pre-existing allocation
history is preserved. Every vector has an admissible carrier, and the complete
Result is `ok` without a conclusion-shaped premise. These are model and
candidate installation theorems, not a completed native remove source law.

The borrowed reference extracts with the unchanged pinned extractor, but
`Vec::remove` remains external. Expanding native `remove`/`try_remove` is
rejected by the fail-closed structured-Drop preflight; the owned wrapper is
also rejected for structured Drop. The emitted external axiom template is
retained as rejected extraction evidence, never installed or kernel-accepted.
After: native remove fidelity remains; V184 stays **OPEN**, no closing theorem.
Work continues on alternative source routes and the other two rows.

## Remaining rows

V233 / op209 and V265 / op259 remain OPEN while their source gates are worked.
V232 and SHA-NI semantics are untouched. No endpoint premise or T field changed.
No `crates/` or `programs/` file changed, so no ELF rebuild is claimed; the
three release pins remain inherited, not freshly checked.
