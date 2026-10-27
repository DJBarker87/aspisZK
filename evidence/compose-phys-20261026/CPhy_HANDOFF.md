# CPhy handoff: requested composition and physical rows discharged

Branch codex/cx-compose-phys-20261026. No push. S2 OPEN; the 100-bit target
is not yet established. Work stops because all assigned rows have been removed
from the concrete-observation joint endpoint, not because the budget expired.

## Exact result and before/after

Final top: `AspisR1.CPhy_Physical.accepted_pair_unified` in
`lean/CPhy_Physical.lean`, checked CPhy_013 and audited CPhy_014.
`CPhy_before-statement.lean.txt` is the exact SdkD input statement;
`CPhy_after-statement.lean.txt` is the exact final statement. Stage1/2 packets
record the intermediate steps; the final source supersedes their earlier
narrower native-writer-conjunct descriptions.

Before: SdkD's one f,s,cuts exports the reference writer. A separate WAdm top
exports native writer admission. Its caller continuation still requires
writer/reader header joins, six node ranges, and compact scan y1 range.
After: CPhy_Accepted preserves SdkD's conclusions and enriches SdkD's OWN
Tx1Q Run with WAdm Admitted, WideInputs, emitted-source writer result and
native-installed writer result, all on the same prepared value, flushed
accumulator, proof/public slices and saved Vec, before WhenBound. Neither
a second accepted execution nor output agreement is assumed. The explicit
SessionAPrepare and query SessionAPrimitives are WAdm's retained owners.
`CPhy_Audit.dictionary_compatibility` proves the union SDK dictionary equals
the Tx1Q specialization, using Uni_Install.compose_tx1; no compatibility input.

The final physical top derives writer.header/size, reader.checkedHeader,
both NodeRanges and scan Y1Range as unconditional conjuncts from the actual
pair. Its caller continuation uses the concrete digest-field decoder,
installed nodeSlot buffers for each actual proof, and Op4P's compact scan
y1. The formerly arbitrary decoder/nodes/y1 binders are explicitly specialized
to these source-derived observations. This does not assert facts about
independently chosen buffers. All original nonphysical results and the
conditional Tx2N Outcome persist. Carriers, accepted execution inputs,
failure events and security metric are unchanged. Expanded semantic-wide-view
y1 is distinct from compact scan y1.

The reader resume is derived from the top's installed TX2 call; all comparison
and source callback bodies are retained. Header digests use the three actual
writer/reader digest calls and the existing success-only native oracle law.
Node physical facts include the same start/finish witnesses, bound and checked
index result; `CPhy_Ranges.physical` also proves the installed op3 returns that
exact buffer. Scan inversion proves the checked [7031,7495) range AND the
source check_values success on that SAME y1. No physical field is a premise.

## Ledger delta

| Removed row IDs in this endpoint | Derived evidence |
|---|---|
| L171-remainder/composition | CPhy_Accepted, same Run and saved Vec; all WAdm conclusions retained |
| L091, L092 | CPhy_Header.writer and cuts.first determinism |
| L093 | CPhy_Header.reader on actual installed resume |
| L100, L101, L102, L103 | CPhy_Ranges.physical/multiproof, actual first proof |
| L104, L105, L106, L107 | CPhy_Ranges.physical/multiproof, actual second proof |
| L108, L109 | CPhy_Ranges.scan on actual installed scan and same compact y1 |

Added row IDs/trust items: NONE. No credit for full L171's remaining
arithmetic/domain/ObservationBinding/WhenBound gates. No global premise-ledger
file or other worker's prefix was edited. This delta is against the Uni update
and SDK/writer handoff statements, not the obsolete raw ledger snapshot.

Retained: SDK/std/allocator/runtime and extraction association, P1/syscall,
site-projection child scope and global effects obligations, runtime protected
checkpoint version, P2Prime, FirstEntry/parser provenance, Session A immutable
prepare and query/geometry/arithmetic owners, all WhenBound/Tx2N Outcome
hypotheses (including authenticated_S1), source experiment/canonical oracle log,
query budgets, full release association and other cones. No global source/log,
probability, or 100-bit theorem is claimed.

## Non-vacuity and success conditioning

CPhy_Audit.physical_fixture constructs the six installed source node reads
and SAME compact scan y1/check_values result using the existing symbolic
Op3I header/Op4P scan fixture. No huge concrete scanner is kernel-evaluated.
WAdm_Nonvacuity.domain_nonempty and SdkD_Nonvacuity.instance_exists are
re-audited within their original local domains. These additions impose no
new acceptance restriction: their joins are derived before runtime/P2Prime/
FirstEntry hypotheses. This is NOT a proof that every remaining crypto/runtime
hypothesis is jointly inhabited by a complete accepted SDK spend.
All final claims are conditioned on the original two accepted entry calls;
there is no claim of arbitrary allocation success, total syscalls, full
rejected-prefix oracle transport, or arbitrary SBF heap equivalence.

## Validation, resource and frozen target fields

14/100 Lean submissions (9 pass, 5 fail), 0/30 Kani. No missing dependencies
needed compilation. All current source hashes match successful exact receipt
snapshots, indexed by CPhy_validation-index.json. Failed attempts are retained
as diagnostics only. CPhy_014 prints every new theorem's axioms, including
HeaderCells.selector, plus retained local non-vacuity theorems; all are subsets
of [propext, Classical.choice, Quot.sound]. No sorry/axiom/admit/native_decide
or heartbeat/recursion-depth override exists in current prefix sources.

Final targets (each exact argv, source/dependency SHA, revision/dirty flag,
exit, time, RSS, swaps and full axioms output are in the numbered receipts):

| Target | Attempt | Exit | Wall s | Peak RSS KiB | Swaps |
|---|---|---:|---:|---:|---:|
| CPhy_Accepted.lean | CPhy_012 | 0 | 3.157854 | 5239612 | 0 |
| CPhy_Physical.lean | CPhy_013 | 0 | 3.200324 | 5261392 | 0 |
| CPhy_Audit.lean | CPhy_014 | 0 | 1.941785 | 5221432 | 0 |

Source revision anchor b37871c7f7 plus exact dirty source snapshots; final
commit follows this handoff. Pinned Lean4 v4.32.0, lake env lean -j1 -M7000
-DElab.async=false. Each job ran in its own verified systemd scope,
MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64; never raised. Scope snapshots
before/after showed only init.scope. No timeout/memory kill, unchanged full
regression or package replay. Coherent SInt2 workspace and cached dependencies
reused as instructed; focused compilation, not a fresh frozen-release replay.
CPhy_final-object-manifest.json records hashes/sizes only, no binaries.

No shipped/cfg(kani) source, protocol parameter, feature, wire format, runtime
pin or artifact changed. Therefore no Rust/Kani/SBF rebuild trigger fired.
Inherited ELF pins, NOT freshly reproduced:
- default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
- devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
- Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548

No keys or funds were touched. No Session A live worktree/candidate was accessed
or modified. Next deliverable belongs to the remaining source-associated
oracle experiment/authenticated_S1 and WhenBound owners; this endpoint is
ready for lead integration within the documented retained trust boundaries.
