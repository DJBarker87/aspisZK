# pv-runjoin5 result and exact outstanding statements

Branch codex/pv-runjoin-20261026; entry4148e0e59c. Target NOT established.
Original frozen implementation, headline, endpoint conclusion, guard, bad event,
simE and complete observer are unchanged. No original native premise or whole
ledger row was removed. No new trust/model choice was adopted. Options A/B
remain unadopted; both theorem modules are included in the focused audit imports.

| Endpoint measure | Before | After |
|---|---|---|
| Original partial source residual |6|6|
| Reviewed native runtime/boundary binders |2|2|
| Original PV_RunJoin_Premises fields |8|8|
| Whole native ledger rows removed |0|0|
| Candidate modeled-history residual |6|5, plus source identity/common-input obligations|

The candidate ledger field is proved from complete generic source control and
one common public reservation prefix. NativeSelectedInputs and InstalledFamily
install dict10's concrete carrier and selected dictionary using SAME selected
record for public and compiled fields. InstalledTransport.endpoint_row_call
is the exact original fixed endpoint transport, proved without a row premise.
SourceSelectionContract.selectedRecord and SelectedAdmission.Remainder expose
the selected compiler/admission record; SelectedAdmission.toPremises supplies
row_call. The other source fields are explicit. No concrete actual selection or
native successful compiler call is fabricated.

Pure source progress: selected op12/map-error parametricity, full continuation
and caller/header naturality, actual selected variant equation, reserve status
classification, seven-field caller erasure, public reservation and selected
compiler carrier round trips. FixtureSelectedSources.both_source checks both
release fixture fibres; it does not identify release bytes or prove their native
compiler calls. SelectedErrorPrelude constructs the source pre-draw prefix
under named Zeroizing value operations, discharges map-error/variant equations,
and proves first-OS-error Entropy return and source witness independence. Native
fill outcome, account success/nonzero, and operation association remain explicit.

## Original six residuals

The six are native-effect/probability/complete-interpretation obligations, not
consequences of Charon/Aeneas source extraction alone (D188). Pure source/control
sublemmas above are now discharged generally and for both fixture fibres.

### E1_V329

```lean
ProverCommitPublicNonce40.E1 boundary.law
```

### native_ledger_V337

```lean
∀ (w : (h).Instance), (h).public w = x.1 →
    ∀ secret (s next : State) status, runtime.body h x w secret s = .ok (status,next) →
      boundary.ledger next =
        match boundary.reservation secret s with
        | none => boundary.ledger s
        | some path => (ProverCommitLedger36.reserve boundary.schedule boundary.unix path (boundary.ledger s)).2
```

### byte_blind_V338

```lean
(∀ secret (s : State) kind,
      boundary.fault secret s kind = boundary.schedule (boundary.ledger s).history.length kind (boundary.ledger s).history) ∧
    (∀ t u rest, boundary.ledger (PV_RunJoin_Deployed.initialState runtime (boundary.coordinates.symm (t,rest))) =
      boundary.ledger (PV_RunJoin_Deployed.initialState runtime (boundary.coordinates.symm (u,rest)))) ∧
    (∀ (i : Fin 128) (t u : Fin 128 → ProverCommitPublicNonce40.Raw) (rest : Rest), (∀ j : Fin 128, j.val < i.val → t j = u j) →
      boundary.frame i (t,rest) = boundary.frame i (u,rest))
```

### kernels_V339

```lean
∀ c, boundary.nativeWeight c =
    PV_RunJoin_E1Joint.weight 128 boundary.law boundary.frame boundary.coordinates c
```

### disclosed_V038

```lean
∀ (adv : (rust).Adversary) (w : (h).Instance), (h).public w = x.1 →
    ∀ r : World, ¬ (∃ i, ProverCommitFuelJoin22.bad (oldBad w) (queries adv w) i r.coins) →
      ((rust).real h B outputs adv x w r).disclosed =
        ((source).real h B outputs (RomObserverBin.observerMap rust observer_program adv) x w r.coins.1.1).disclosed
```

### observerOracle_V038

```lean
∀ (adv : (rust).Adversary) (w : (h).Instance), (h).public w = x.1 →
    ∀ r : World, ¬ (∃ i, ProverCommitFuelJoin22.bad (oldBad w) (queries adv w) i r.coins) →
      ((rust).real h B outputs adv x w r).observerOracle =
        ((source).real h B outputs (RomObserverBin.observerMap rust observer_program adv) x w r.coins.1.1).observerOracle
```

## Native named world fields and exact matching

No predicate below is an axiom. Supplying Laws/Identity is an explicit unproved
interpretation obligation. It does not imply availability or a probability law.
World retains the SAME RawTape E plus entropyUsed, file-event list/fileUsed,
time list/timeUsed and worker list/workerUsed. File= PDict_FileCarrier.File and
Reply=PDict_World244.Reply, with constructor-preserving request/event map and
identical entropy/file cursors, are the dict10 identity obligation. Time/worker
fields extend that signature; they never replace entropy positions. Entropy
framing through file/time/worker replay is proved in OsWorldReplay.

Exact named outcome statements, including the complete pre-call world:

```lean
structure Laws (E File Reply Time Worker : Type) where
  entropyDraw : World E File Reply Time Worker → Nat →
    PV_RunJoin_CallerWorld.RawReply E → Prop
  open64 : World E File Reply Time Worker → List U8 → U32 → U32 → Reply → Prop
  read : World E File Reply Time Worker → File → Usize → Reply → Prop
  write : World E File Reply Time Worker → File → List U8 → Reply → Prop
  sync : World E File Reply Time Worker → File → Reply → Prop
  close : World E File Reply Time Worker → File → Reply → Prop
  time : World E File Reply Time Worker → Time → Prop
  worker : World E File Reply Time Worker → Worker → Prop
```

EntropyAllowed additionally requires entropyUsed=i.val and entropy i=reply.
FileAllowed additionally requires fileStep request world=some(reply,next).
TimeAllowed/WorkerAllowed likewise require their exact step equations.
NativeEffectInterface.Identity prints every matching iff at25672; the Native
predicate function and its equality with these Laws remain uninstalled.
Unix File::flush is pure/no-event in the checked sibling dictionary: OsWorld.flush
world=world; durability sync has its own outcome field above. It is not dropped
from the native interpretation. Source return/last_error does not encode history.

E1 must supply the actual successful-byte conditional uniform law; E2 must match
actual filesystem outcomes and their ledger/observer effects. Native density,
initial-ledger byte independence, causal frames, time/worker outcomes, and BOTH
V038 complete-view fields remain obligations. Side-channel assessment is in
side-channel-association.md: no whole L1 counts/errors or L2 F3/F5/F6 row closed.

## Validation and resource limits

100 Lean attempts25600–25699, all focused local small-new-module checks with
existing cache, Lean -M7000. No dependency build or host Lean scope. Failed proof
attempts are preserved as snapshots/logs; accepted source has no forbidden proof
mechanism. Receipt index records every exact target/status/wall/RSS/swap/revision,
source hash and printed axioms. The final target also audits retained cached
declarations. This is NOT frozen manifest/dependency-closure replay.

One of12 available Kani runs used: proofs::zeroizing_new_as_mut64_source_values,
actual zeroize1.9.1, opt-level3, no stubs:113 checks,0 failed,1 unreachable,
2.74s,174616KiB peak RSS,swap0,exit0. No cleanup/privacy/native OS claim follows.
11 Kani runs remain. Copy admission01 was refused and retired permanently;
copy02 and launch01 were allowed after3minutes. Host scope6G/8G/swap0/tasks64.
Quiet window honored; no attempt launched after refusal under the same ID.

The Lean allocation is exhausted. Next concrete deliverable: install the actual
selected compiler/admission family and dict10-compatible native OS event world,
prove its model ledger/E2 and complete observer/time/worker association, and
resolve the owner A/B model decision before claiming V038 or native coupling.
A coherent pinned dependency closure replay remains after those premises close.
No implementation changes, push, account/key creation or key cleanup occurred.

Final audit25699: R1Z/PV_RunJoin_CompleteEventStep, exit0,107.3752268343s,
2127740928bytes peak RSS,swap0,revision d03e0c5ce7 (uncommitted snapshot
hash recorded in receipt),56 cached imports plus corrected event theorem,
95 printed declarations; only propext/Classical.choice/Quot.sound or no axioms.
Accepted attempts57;distinct accepted modules57.
