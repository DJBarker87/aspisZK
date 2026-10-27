# Native writer admission handoff — 2026-10-25

The local native writer admission gate is discharged on the **same original
accepted TX1 run**, at the retained typed-Rust/P6 standard-library and runtime
trust boundary. Final theorem:
`AspisR1.WAdm_NativeAccepted.accepted_pair_claims_tx1`
(`lean/WAdm_NativeAccepted.lean`, checked attempt088). Proof closure commit:
`43eb9c2a6d`. The final evidence/audit commit follows it on
`codex/cx-writer-adm-20261025`; no push was performed.

This supersedes the outstanding native-composition gap described in STAGE3.
It is a local source-refinement result, not a complete S2 security theorem.
**The 100-bit release target is not yet established by this work.**

## Exact premise removal and success conditioning

The original theorem/extraction/dictionary and original accepted pair are
retained. From its own `run.p`, query output and flushed weights, the theorem
derives S2, 64 weights, next10, canonical immutable WideExact fields and rhs,
private `from_limbs` realization, proof57607 and public1880. Public1880 comes
from the concrete original account read, not an added length assumption.
`WAdm_NativeInstall.on_run` then derives the concrete native-installed op16
call with those exact inputs and **the original saved Vec**. It is an
unconditional conjunct inside the original accepted-run existential, before
`WhenBound`; no native success, writer-admission or output-agreement
hypothesis is added. The original selector result remains as useful evidence
for that same invocation; replacing it uses the proven concrete native result.
The new installation changes only op16 (`writer_slot`, `other_slots`).

Before/after full statements are in `WAdm_before-statement.lean.txt` and
`WAdm_after-statement.lean.txt`. `WAdm_premise-audit.json` records the audit:
deleting the two permitted explicit owner parameters and new output
conjuncts recovers the original statement exactly after whitespace
normalization. Original failure events, security metric, carriers, accepted
executions and all original conclusions remain. This is not a new conclusion
under a writer-admission implication.

Two named owner parameters are made explicit, as authorized:
`WAdm_Domain.SessionAPrepare` contains only immutable successful preparation
fields; `Port5Q1_QueryPorts.SessionAPrimitives` contains the retained arithmetic
and `line_canonical` owners. Neither contains native writer success or
reference/native agreement. Existing geometry/domain, parser, authentication,
reader, binding, child and other WhenBound gates remain. The final theorem
does not move or discharge these unrelated implications.

The claim is success-conditioned on the original two accepted entry calls.
It does not claim all-input native/reference equality (the Port3 counterexample
still applies), allocation success for arbitrary heaps, full rejection-trace
transport, or a complete accepted native security experiment.

## Concrete source connection

1. `WAdm_KANI001` checks the unchanged shipped `verifier::checkpoint` against
   the proof-only fissioned Rust source using the **same** native Prepared,
   accumulator, slices and arbitrary three digest answers. The domain is
   S2/64/next10, private canonical WideExact, proof57607/public1880; raw K and
   query words are arbitrary. Both lengths, an arbitrary output byte, an
   arbitrary checksum-body byte, ordered hash calls, original proof/public
   pointer+length identities, domain and body width are checked. No function
   is stubbed. 1796 checks pass. `WAdm_KANI002` separately checks native scalar
   byte serialization (205 checks); the retained native K serializer proof is
   reused, not assumed as a writer-output equation.
2. Charon002/Aeneas004 successfully extract the fissioned source. The generated
   Funs body is retained exactly except removal of resource option lines;
   source types are explicitly aliased to the existing canonical records.
   `WAdm_FissionedRoot.emitted` proves every concrete append, loop, bound,
   massert, ordered digest call and returned Vec; no helper law slot remains.
   Pure owned-array iterator content is given concrete list operations at
   the retained std/runtime interpretation boundary. Scalar ports use the
   independently checked native contracts and retained emitted K writer.
3. `WAdm_FissionedFields.returned/body_bytes` identify the exact same original
   input record and physical body. `WAdm_NativeInstance.accepted` inverts the
   original reference success for its three hash observations and proves the
   complete concrete emitted source result is that same Vec. No second
   successful execution is hypothesized. `WAdm_NativeInstall.on_run` and
   `WAdm_NativeEndpoint.reached` compose this result with the original pair.

This is a mixed bounded native-source Kani certificate plus kernel-checked
emitted-source bridge. Kani certificates are not claimed to be Lean axioms or
kernel checked machine-code refinements. The retained typed-Rust/P6 validity,
standard-library/allocator and runtime syscall trust still applies; no
arbitrary SBF heap or release-ELF execution theorem is claimed. The failed
unmodified native-root Aeneas context matching is retained separately and
never imported. No extractor/tool repair was attempted.

## Non-vacuity

`WAdm_Nonvacuity.domain_nonempty` constructs an admitted local writer input.
The optimized actual shipped writer fixture `WAdm_RUST001` constructs canonical
zero fields with the exact sizes and checks the complete header/layout,
three digest calls and output. `extraction_satisfiable` retains the generic
extraction witness audit. These establish local domain/fixture non-vacuity;
they are **not** a new jointly accepted cryptographic pair satisfying all
Session A owners. No such global non-vacuity or full security claim is made.

## Validation and resource receipts

| Target | Exit | Wall seconds | Peak RSS KiB | Swap |
|---|---:|---:|---:|---:|
| whole emitted writer, attempt083 | 0 | 7.672060 | 5213712 | 0 |
| NativeInstance, attempt085 | 0 | 1.897557 | 5181088 | 0 |
| NativeAccepted, attempt088 | 0 | 2.149358 | 5189256 | 0 |
| final axioms/statement audit, attempt090 | 0 | 1.804855 | 5158508 | 0 |
| native paired certificate, KANI001 | 0 | 174.486013 | 3313484 | 0 |
| native WideExact byte contract, KANI002 | 0 | 1.765473 | 281720 | 0 |
| optimized native fixture, RUST001 | 0 | 21.670609 | 585204 | 0 |

Every new top theorem has `#print axioms`. Final audit090 prints only subsets
of `[propext, Classical.choice, Quot.sound]`. No new axiom, sorry, unsafe
reducibility override, heartbeat override or recursion-depth override remains
in compiled new sources. Earlier failed attempts/logs are retained, not proof
evidence. Audit089 failed on an unsupported printer option;090 removes it.

Budget: **90/100 conservatively counted Lean submissions**, comprising88
actual Lean processes and2 dependency preflights rejected before Lean started;
**2/40 Kani runs**. Stop now because the requested local gate is removed.
No package replay or unchanged full regression was run. Existing coherent
SInt2 objects and retained certificates were reused; this is not a fresh
whole-release closure rebuild. Every host job uses explicit 6G/8G/no-swap/64-task
scope limits, Lean `-M7000`; Rust compilation/gates are optimized. No cap
increase or unchanged timeout/memory-kill rerun occurred. Final scope snapshot
contains only init.scope.

`WAdm_validation-index.json` checks every receipt snapshot and all43 current
module sources against a passing exact source hash. Individual receipts retain
commands, scope caps, dependencies, source hashes, exit/time/RSS/swap and
axioms output. `WAdm_final-object-manifest.json` pins reused final objects;
`WAdm_source-audit.json` and `WAdm_host-source-check.json` pin all173 unchanged
shipped/dependency inputs and source linkage. Historical `source_revision`
fields sometimes contain an inherited earlier commit anchor; these are
explicitly qualified in `WAdm_source-revision-notes.json`, never rewritten as
clean-checkout claims. Exact source snapshots/hashes disambiguate those runs.
Final accepted theorem used source anchor3f1b7b6 and final audit43eb9c2a6d;
final committed source hashes and passing snapshots match.

## Frozen target and remaining work

No shipped source, feature or artifact changed, including no cfg(kani) edit;
the proof Rust crate lives only under this evidence directory. Thus no ELF
rebuild was triggered. Inherited release pins (not freshly reproduced):

- default: `f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4`
- devnet: `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`
- Pool: `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`

Remaining work belongs to the lead/other premises: instantiate retained Session
A owners and other WhenBound gates, compose their coherent accepted experiment,
and complete the release artifact/security argument. The next concrete
integration target is this NativeAccepted endpoint in the lead's accepted-pair
composition, using its original run and these exact source/certificate pins.
No other worker prefix, live Session A worktree or S1/S3/S4/S5/S6/S9 candidate
was modified. No key was removed and no funds were handled.
