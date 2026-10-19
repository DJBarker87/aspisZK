# Rho source invariants and existing-runtime zip composition

The active candidate-12 goal is still open. This checkpoint makes two caller
requirements concrete; it does not claim complete optimization equivalence.
Production Rust stays frozen at 39c2971dd16c95858a4cfd2c9ae35da052eacfa9.

## Source basis and exact coordinate input

The old/new accumulator bodies have a byte-identical complete basis prefix.
extract-rho-basis.py retains it and checks inverse substitution of the stable
a.weights.len() read by the scalar input length. The exact prefix and existing
M31.double body emit with the original strict reference producer. Generated
Types/Funs are promoted bytes-unchanged, with the external M31.mul/add/sub
names bound to the original checked arithmetic functions, not stubs.

CuSavingsRhoBasis.source_success proves every successful execution of that
whole emitted basis function returns canonical entries. It assumes neither
node canonicality, a length bound nor termination. Failure/divergence cases
remain in the actual program. Its nested-loop proof uses a separately checked
generic success invariant over the original partial-fixpoint loop, avoiding
large concrete reductions.

CuSavingsRhoInputs derives index bounds, uniqueness and complete coverage from
the typed basis array and bounded length. CuSavingsRhoBasisPipeline consumes
the emitted basis success theorem to supply all coordinate/basis admission
conditions to the checked batch pipeline, preserving failed/divergent basis
results. Canonical query power and actual source context/length binding remain.

## Zip without a new primitive axiom

The original reference cache already supplies generic Zip.next and the mutable
slice-iterator next/writeback definition. CuSavingsZipLoans packages the latter
writeback as the yielded loan value and uses the unchanged generic Zip.next.
CuSavingsZipFill proves the complete equal-length assignment traversal, including
every writeback and termination, under these existing definitions.
CuSavingsRhoZipInitialization consumes the exact previously extracted four-word
assignment and proves the resulting raw vector is exactly initialState's vector.
It then composes that result into the already checked batch arithmetic pipeline.

These four modules compile with the exact original reference cache prioritized;
the selected Aeneas owner is d3bfce818c2409992274bc1852aa00280cb7a8139465ef0bab674498e4cdc69d.
They add no iterator axiom. This is a proved runtime-component interpretation,
not an assertion that the failed whole-new emission succeeded. The full new
source wrapper, allocation/error flow and source-to-component binding are still
required before candidate completion.

## Focused evidence

All ten successful targets are listed with exact source/receipt hashes,
commands/revisions/features/import pins/wall/RSS/swap and printed axioms in
RHO-SOURCE-INVARIANTS.json and their receipts. Each takes about 1.8–2.2 seconds,
peaks below 2.6 GiB process RSS, uses zero observed process/cgroup swap, and
prints only standard Lean axioms. Failed local attempts are retained separately.
No unchanged successful Lean or runtime regression was repeated.

The transparent-Zip extraction diagnostic exposes a different unsupported
mutable projection and is NOT_ADMITTED. Existing monomorphize-mut=all expanded
outside the focused initializer; it was stopped after 72.6 seconds. No compiler
change was made. Terminating the timed process group prevented final GNU-time
process RSS/swap output; the 5,721,403,392-byte cgroup peak and zero observed
cgroup swap remain recorded. These are not invented process-peak metrics.
The successful basis Charon/Aeneas runs take 0.401/0.802 seconds and peak at
164,320/76,228 KiB, with zero observed swap.

## Remaining goal requirements and next action

1. Bind the whole BatchedWeights::new wrapper to allocation plus this proved
   assignment loop, including its exact constant error mapping, and justify
   sufficient-resource allocation from the pinned allocator contract.
2. Bind the actual accumulate/query contexts to the new basis/coordinate
   results; derive canonical powers and length/counter invariants from actual
   constructors/resume and the unchanged field recurrence.
3. Consume those source results in all three transaction wrappers and the
   unchanged checkpoint/relation/oracle/effect contexts. A full source-consuming
   theorem and final requirement audit are still required.

Re-pin inventory: source prefix basis and its two loop/body declarations are
AspisR1RhoBasis.basis, basis_loop0, basis_loop0.body,
basis_loop0_loop0 and basis_loop0_loop0.body. M31.double is also emitted there;
unchanged base methods bind directly to AspisR1Qm31ArithmeticProbe.field.M31.
The new zip proofs consume the original core.iter.adapters.zip.Zip generic
next and core.slice.iter.IteratorIterMut.next; no Rust owner was changed.
