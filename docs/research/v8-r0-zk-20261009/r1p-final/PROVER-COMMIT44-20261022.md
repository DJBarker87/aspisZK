# Prover commitment continuation 44

Target not yet established. Base: a99fab97ee2cf19835eba9e1b8625de13919be43.
Branch: codex/cx-prover-commit44-20261022.

## Stage 1: D156 parent collection

Exactly one named TrustedStd field is added:
`btree_set_from_iter_ordered`, specifying the `BTreeSet<usize>::from_iter`
collection/consuming iterator as `input.toFinset.sort (· ≤ ·)` on natural
images of usize keys. `MapAPI.set_from_iter` names the native operation.
No other trusted law is added. The universal model instance witnesses
consistency. The explicit trust inventory and before/after source are under
`../../100bit-spend-path-20261013/evidence/prover-commit44-20261022/trust/`.

`ProverCommitParents44.exact_order`, `ascending`, `duplicate_free` and
`parent_iff` establish precisely the ordered, unique parents of the decoded
current level. `traversal` and `continuation` preserve an arbitrary complete
accumulator and its subsequent observer; thus they retain coin order and
state, rather than merely parent membership. These are deterministic library
transport theorems. Native caller evidence is recorded separately, not
manufactured by a source callback hypothesis.

J9536 accepts the extended TrustedStd module (1.33 s, 2,547,684 KiB, zero
swaps). J9538 accepts all six parent theorems (1.18 s, 2,533,268 KiB, zero
swaps). Exit 0; every axiom list is [propext, Classical.choice, Quot.sound].
J9537 is a rejected type-inference draft, not accepted proof evidence.
All compiles use the pinned host Env J, -M7000, MemoryHigh=6G,
MemoryMax=8G, MemorySwapMax=0 and TasksMax=64. Exact source hashes,
source revision, dependency fingerprints, targets, commands and logs are in
`evidence/prover-commit44-20261022/lean/` beside the retained source snapshots.

The shared TrustedStd source/object is overwritten and snapshotted under the
branch-specific host workspace. Dependent modules used by subsequent stages
must be rebuilt against this object before their evidence is accepted.
Publication, source experiment conversion, concrete joins and endpoint remain
pending at this stage checkpoint. No shipped source changes or ELF rebuild.

## Stage 2: native parent transition and eighteen levels

The per-parent native transition check passes all 536 checks for arbitrary full
32-byte child/coin/root values and all source depths 0–17 and parent indices
below 2^17. It checks lazy left-then-right missing-child coins, the final-level
root substitution, both writes, one read-count increment, and the complete
ordered binary-parent call. The source body is retained verbatim except
`reads+=1` becomes `*reads+=1` for the harness's caller-owned counter.
Map get/insert and the recording digest callee remain explicit substitutes
at their named boundaries; no collection internals are claimed verified.
The accepted gate is `parent-transition-v3-eighteen-levels`: exit 0,
2.975 s, peak RSS 227,796 KiB, zero swaps. V1 fails a 96-byte `memcmp`
unwinding assertion. V2 passes on a 17-level stand-in but is superseded;
V3 checks the actual 18-level source domain and an arbitrary selected byte
of every returned digest. Neither earlier draft is the accepted final gate.

`ProverCommitParentStep44.step_decode`, `loop_decode` and `collected_loop`
transport both maps, lazy coins, the retained programming-call log and reads
through the native ordered parent sequence. `child_index_bound` proves the
binary child indices fit the source domain symbolically.
`ProverCommitTree44.level_decode`, `levels_decode`, `range_levels` and
`eighteen_levels` compose the state across the native depth order, preserving
every stored children map and subsequent coin state. These are caller/control
theorems; they do not identify the remaining concrete hash/codec/multiproof
callees or constitute a full publication certificate.

J9617 accepts the parent step (1.28 s, 2,541,736 KiB, zero swaps);
J9621 accepts the depth composition (1.39 s, 2,544,484 KiB, zero swaps).
Every axiom list is standard. J9619 is a rejected range-lemma draft.
J9540 was refused before compilation because an unrelated historical receipt
already occupies it; that receipt is not copied or attributed here. The
subsequent numbers were selected from a read-only receipt inventory.

The unchanged publication algebra, merge and salt consumers are rebuilt
against the extended TrustedStd object: J9539 (`ProverCommitPublication33`),
J9618 (`ProverCommitMerge33`) and J9620 (`ProverCommitLeaves43`), each exit 0,
zero swaps and standard axioms. These overwrite shared source/objects only
with the same tracked source bytes; branch-specific snapshots retain the
previous source/objects. Other dependent release modules have not been
replayed and no coherent release replay is claimed.

## Demonstrated next source interface: native map length

**Publication is incomplete; target not yet established.** The next guarded
source return in `sim.rs:389` is:

```rust
if level.len()!=1||level.get(&0)!=Some(&root) {return Err(Error::Merkle);}
```

The nine accepted TrustedStd fields specify empty, insert state/previous,
get, ordered iteration, lazy entry insertion, the D156 BTreeSet collector,
and the two TLS properties. None specifies **native `BTreeMap::len`**.
It is used again in `transcript.len()` at final publication. Replacing it
with the decoded entry-list length without a proof would silently add a
source/library law and can change the visible early error.

The focused original-root-guard diagnostic keeps BTreeMap opaque, per D145.
Charon exits 0 (0.174 s / 152,036 KiB) and Aeneas exits 0
(0.304 s / 62,304 KiB), zero swaps, `has_errors=false`. The generated
`root_guard` calls `alloc.collections.btree.map.BTreeMap.len`, and the
external file declares its unresolved template. All generated output is
retained as inert `.lean.txt` under `root-guard/generated/`; none is installed
or imported into the proof environment. Existing get semantics do not
supply the missing length projection. The complete source pin, field
inventory and exact next interface are in `root-guard/interface-audit.json`.

`ProverCommitLengthGap44.length_not_determined` provides a formal interface
countermodel: every accepted TrustedStd law holds for the very same singleton
map, get result, root and TLS instance; reported lengths zero and one still
produce different root-guard outcomes. This is **not a counterexample to Rust
BTreeMap**. It proves that the missing length identification is not a
consequence of the accepted fields. J9622 accepts it: exit 0, 1.21 s,
2,532,244 KiB, zero swaps, standard axioms.

**Exact next deliverable:** establish, for every reachable native level map,
that `BTreeMap::len` returns precisely the decoded ordered-entry cardinality,
with the usize image exact and the source result/error behavior retained.
Use that interface to close the `program_tree` root guard and the final
transcript read count. Adding another TrustedStd field is not authorized by
this task, and no length field, callback success law or source instance is
silently introduced. No collection internals are claimed verified.

Per the stopping rule, the remaining native publication certificate,
source-to-FSExperiments conversion, `shippedProverExperiment`, both concrete
WholeRunJoins, and endpoint premise removal stop here. The local ordered-byte,
merge/error and parent-control theorems have not been promoted to a complete
source experiment. D143's published-data projection and D146's announced
source-representable deployment domain remain the intended contract. The
public nonce and byte-blind environment remain adversary inputs in the
existing local models; there is no new nonce law or ledger cap.

## Verbatim endpoint before/after: unchanged

Both full files, including all section binders and theorem body, are saved
byte-identically in `endpoint/before.lean.txt` and `endpoint/after.lean.txt`.
The quantifier on `x` and the arbitrary runtime carrier remain unchanged.
No D146 domain narrowing or D143 observable projection is claimed installed
in an endpoint lacking its source join.

Before binders:

```lean
variable (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle)
local notation "h" => PhaseWireLog2Bin.honest input

variable (rust : FSExperiments K CommitHandle Aux R1Bat F)
```

After binders:

```lean
variable (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle)
local notation "h" => PhaseWireLog2Bin.honest input

variable (rust : FSExperiments K CommitHandle Aux R1Bat F)
```

Before theorem:

```lean
theorem privacy_headline_deployed
    (refinement : RustProverRefinement template outputs x rust observer_program)
 :
    ZK_FSS h B outputs rust x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x)
      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge < 1 / 2^100
```

After theorem:

```lean
theorem privacy_headline_deployed
    (refinement : RustProverRefinement template outputs x rust observer_program)
 :
    ZK_FSS h B outputs rust x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x)
      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge < 1 / 2^100
```

## Focused audit and source/artifact scope

J9623 accepts `R1Z.ProverCommitAudit44`: exit 0, 1.73 s, peak RSS
4,108,520 KiB, zero swaps. It prints all 15 new top theorems, the updated
TrustedStd consistency witness and the unchanged deployed endpoint, all
with axiom lists contained in [propext, Classical.choice, Quot.sound].
`final-proof-audit.json` checks every final installed changed source hash
and the audit receipt's dependency object hashes; `theorem-inventory.json`
lists the exact new statements. Exact target/command, source revision plus
source snapshots, source SHA256, dependency fingerprint, exit, wall, RSS,
swap, errors and full axiom lines are in `lean/attempts.json` and receipts.
No unchanged full regression or frozen manifest replay ran; the source
closure is not ready for a formal release replay.

Only the authorized BTreeSet field is added inside the existing TrustedStd
item. The named trust list remains P1, P7, TrustedStd, E1, E2; P6 remains an
explicit source/native evidence boundary. Timing and other side channels
remain outside the announced D143 privacy contract.

All 491 tracked files under `crates/` and `programs/` remain byte-identical to the
task base, with no new untracked shipped file (`shipped-sources-unchanged.json`).
The shipped-file rule does not trigger an ELF rebuild; unchanged-artifact
evidence is reused only for unchanged artifacts. No local Lean or cold
dependency build, uncapped host job, new resource option, new Lean axiom,
wallet/account key operation, push or merge occurred. No binary, object,
LLBC, ELF, tarball or local target directory is committed.

The direct native `indices.sort(); indices.dedup()` diagnostic, launched
before the length-interface finding, stops at its 600-second limit:
`sort-dedup-v1`, exit 124, wall 600.002 s, zero swaps, aggregate cgroup peak
5,516,099,584 bytes. GNU-time's 15,296 KiB reaped-parent RSS does not measure
CBMC's descendants; it is retained without being misreported as the peak.
The test uses actual standard-library sorting, no collection substitute,
all input lengths 0–12 and arbitrary u32 values. It does not establish the
sorted/dedup source bridge and is not rerun unchanged or with a larger cap.
That remains a further publication obligation after the native length
interface. No unfinished host job remains. The native/extraction manifest
`native-attempts.json` keeps every accepted, superseded, rejected and timed-out
run distinct, with exact commands, input hashes, revision and scope fields.

Stage commits: `e5dff6608` (one std field and ordered parent transport),
`88ab46652` (native transition and eighteen-level composition). The final
commit records the length obstruction, focused audit and this handoff.

`git diff --check` over the final staged change reports only the original
blank EOF lines in the two generated external-template `.lean.txt` evidence
files. Their bytes are retained as emitted; no source/proof whitespace error
is suppressed. The final host scope inventory is `host-jobs-finished.json`.
**Target not yet established.**
