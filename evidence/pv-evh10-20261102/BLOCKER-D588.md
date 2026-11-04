# D588 — source entry world producer remains unconstructed

Resume: `102cacae1c`, branch `codex/pv-evh-20261029`. Physical work has
stopped under l3-2. See L3-RESIDUAL.md; its named V370/L3 residual is not a
projection premise. The main task is incomplete. This is a construction
frontier, not an impossibility result or a shipped-source counterexample.

## Exact construction still required

For the original four binders, without changing the dictionary:

```text
(base : ProverRwFull.ExternalTypes)
(heap : R1Z.PV_RunJoin_WeightInstalled46.Heap)
(box : R1Z.PV_RunJoin_WeightInstalled46.Box)
(ops : @ProverRwFull.ExternalFuns
  (R1Z.PV_RunJoin_NativeResidual62.types
    (PV_EVH_NativeRawSelection.rawBase base)))
```

set the source dictionary to `opsNative (rawBase base) heap box ops`.
For every original proof-account invocation, quantify over its actual T,
`inst : AccountInst T`, public argument, compiled argument, hash callback,
nonce store and account capture, and the initial source resource world.
The target is a SOURCE interpreter of:

```text
RealR1_client.prove_for_proof_accounts inst public1 compiled hash store account
```

Construct `source_entry_world` on that unchanged invocation domain. This
name is a required construction, NOT an elaborated Lean declaration. Its
finite reached prefixes must preserve the actual continuation, source
receiver/capture/store, entropy cursor, nonce files, allocator post-state,
stack and thread answers, and ordered native events in ONE source world.
Every primitive is interpreted when reached at its current world; reject,
partial I/O, source fail/div, resource pending/exhaustion, panic and abort
remain. An interpreter fuel cutoff is pending, not a native divergence or
ordinary error. Every divergent execution retains all its finite prefixes.
No physical PC, mapping, frame exclusion or paired machine carrier is needed.

The only permitted conditional premises are **OWNER** (heap ownership from
pv-evhB5), **op227**, and **op257**, each with its actual source-bound meaning.
No concrete OWNER export is invented here. In particular, `source_entry_world`
or a whole-helper Result/trace cannot be supplied as a fourth hypothesis or
hidden inside OWNER. Primitive resource answers are world data, not promises
of success or adequacy. No successful-prefix filter is allowed.

Required source-composition law: interpreting each reached source bind must
run its first computation at w and its continuation at THAT computation's
post-world, concatenate events in order, and bypass the continuation on every
nonreturning/failure branch while retaining its post-world and events. This
must be established for the original entry's actual callees, not just the
abstract monad bind. Existing generic bind laws do not supply that instance.

For each unchanged RuntimeBinding index i=(env,observer,instance,randomness),
produce run(i) with E(i)=run(i).events and its faithful native terminal. Then
prove the five simultaneous BLOCKER-D583 equations on that deployed binding:

```text
rt.native env observer instance randomness = <E(i), terminal(i)>
rt.fileTrace i = PV_RJ4IDB.nativeFiles E(i)
rt.countTrace i = (PV_RJ4IDB.nativeCounts E(i),
                   PV_RJ4IDB.nativeRejections E(i))
rt.timeTrace i = PV_RJ4IDB.nativeTimes E(i)
rt.oraclePrefix i = PV_RJ4IDB.nativeOracle E(i)
```

These are specification targets, not typechecked theorems. The still-missing
source operational carrier/interpreter cannot be replaced with externally
chosen events or a subtype assuming these equations. Client D520/U/D524
before/after effects must also be reached effects, not fabricated suffixes.

## Checked first source join

The current top entry is `PV_EVH_NativeOperatorProver.entry_OPEN`, returning
`PV_EVH_Prefix.P Outcome = World → Prefix Outcome`. Its `entry_fixed` assumes
`same : ∀ n s, answers n s = getrandom.fill s`, together with account, head,
nonce, callback, leaf and frame compatibility. The source Result equality
uses a single dictionary. It does not establish the requested stateful
operational interpretation. In particular `same` forces all replies for an
identical buffer to be equal across cursor values; it cannot justify a
rejecting entropy draw followed by a different draw at the next cursor.

`PV_EVH_World.World` contains entropy/files/oracle/counters, but no allocator,
stack or thread answer state. `WorldLoop.Status` contains only finished
Result and interpreter exhaustion. In contrast `PV_EVH_Runtime.Q` preserves
runtime State and Fault, and pv-evhB's callback/allocator computations use Q.
`PV_EVHB_ReserveWorld.continuation` passes the allocator post-world correctly,
but is not installed in the P entry. `PV_EVHB_SaltsReserve.selected_prefix`
selects the original reserve at one world; its `afterReserve` executes the
source salt loop under that selected dictionary. This is not a dynamically
reselected full-entry interpreter. These facts remain true even granting
OWNER, op227 and op257: those residuals do not construct the source lift.

Thus the first blocked installation step is the concrete source entry
composition above. No additional compatibility/adequacy hypothesis is
admitted. A five-field adapter over an arbitrary supplied Run would establish
only model projection identities and would leave this exact obligation open.
The five deployed selectors were therefore not replaced with such an adapter.
No claim that this construction cannot be implemented is made.

## Evidence and next action

`source-projection-D588.json` pins the inspected sources and the five selectors;
`check_source_projection_d588.py --check` reproduces the source review and L3
attachment hashes. This is source inspection only, not semantic absence or a
Lean proof. No new theorem, host scope, native run, axioms audit, full replay or
unchanged regression. Historical axioms remain SUMMARY-BASED. NEXT Lean90267,
then91500–91596 (91597–91599 audits); native NEXTN91603. No IDs consumed.

Stop follows the inherited D580 focus instruction at this concrete source
producer construction, not the retired physical-frame task, not waiting for
another branch, and not budget exhaustion. Next: implement the fault/pending
aware source world lift through the original callback/entropy/nonce/salt
continuations at per-reached opsNative, consuming the existing components;
then install all five projections together and prove these equations.
Rows removed NONE; T unchanged; target not yet established. OWNER, op227,
op257, actual source execution/non-emptiness, V400 resource/failure timing,
D520/U/D524, L1/L2 and the separately named V370/L3 residual remain open.
No frozen implementation, soundness file, keys, accounts or funds were changed.
