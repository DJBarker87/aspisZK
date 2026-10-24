# Exact release interface change

**Composed acceptance withheld.** The candidate statements below compiled in a mixed cached import environment, but lean-024 found 111 modules with structural declaration differences across 246 changed root/A objects in a 7707-module root closure. This is not proof of semantic inequivalence, and is not a compatibility proof. The new root-only call-domain/control results remain validated on the original root cache; the concrete A consumer/driver/accounting/effects declarations are provisional until the matching-source dependency gate is satisfied. No new compatibility hypothesis is added. See compatibility.json for the full differences.


## Premise before

```lean
def LocalBudgets (rest : Implementation) (w : Nat → Nat) : Prop :=
  ∀ {A : Type} (op : Call A) (H : Bytes → State),
    operationId op ∈ delegatedIds → (eval H (rest op)).1.length ≤ w (operationId op)
```

## Premise after

```lean

def ReleaseCall {A : Type} : Call A → Prop
  | .op6 _ _ _ _ observer _ _ _ => observer = none
  | .op7 _ _ _ _ observer _ => observer = none
  | .op19 _ _ _ observer => observer = none
  | _ => True

/-- Every continuation, including values never returned by an implementation. -/
def CallsIn {A : Type} : Code A → Prop
  | .done _ => True
  | .step _ k => ∀ b, CallsIn (k b)
  | .call op k => ReleaseCall op ∧ ∀ b, CallsIn (k b)

def ReleaseBudgets (rest : Implementation) (w : Nat → Nat) : Prop :=
  ∀ {A : Type} (op : Call A) (H : Bytes → State),
    operationId op ∈ Port15DRIVER_Local.delegatedIds → ReleaseCall op →
      (eval H (rest op)).1.length ≤ w (operationId op)


```

CallsIn universally quantifies every continuation value, independently of any adversary, oracle or implementation. Port17RELEASE_Invariant.tx1/tx2 establish it for the unchanged Flow10/None and tx2_authenticated/None on every argument. Some is never mapped to None. Library mark callbacks in this actual driver are None as before. The weaker budget premise is justified by actual program syntax, not by restricting proof inputs, child outcomes or the prover.

## Complete driver before

```lean
theorem rust (ops : Ops) (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap)
    (rest : Implementation) (w : Nat → Nat) (budgets : LocalBudgets rest w)
    (adapter : AdapterRw.Ops) {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (hash : Hash) (H : Bytes → State) (i : OraclePortStoredExperimentC4.Input) :
    (eval H (Port1_Driver.rust adapter (Port9OR_Installed.implementation ops reserved unwrap rest)
      D hash i)).1.length ≤ 1046 + delegatedWeight w

```

## Complete concrete driver after

```lean
theorem rust (ops : Ops) (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap)
    (base : AspisR1CurrentCaller.Ops)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (other : Implementation)
    (w : Nat → Nat) (remaining : OtherBudgets other w)
    (adapter : AdapterRw.Ops) {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (hash : Hash) (H : Bytes → State) (i : OraclePortStoredExperimentC4.Input) :
    (eval H (Port1_Driver.rust adapter (implementation ops reserved unwrap base R B other)
      D hash i)).1.length ≤ 1161 + remainingWeight w

```

The concrete installation nests the unchanged owned op5/8/18 and library implementation around A's pinned release op7 body. base/R/B/other remain distinct parameters. No model arguments are identified with unrelated native leaves, and no native Result callback is assumed effect free.

## Residual premise (complete)

```lean
def OtherBudgets (other : Implementation) (w : Nat → Nat) : Prop :=
  ∀ {A : Type} (op : Call A) (H : Bytes → State),
    operationId op ∈ Port15DRIVER_Local.delegatedIds → operationId op ≠ 7 →
      ReleaseCall op → (eval H (other op)).1.length ≤ w (operationId op)

def weight (w : Nat → Nat) (id : Nat) : Nat := if id = 7 then 115 else w id


```

Remainder = 2*w3+w4+2*w6+2*w9+2*w10+2*w11+w12+w17+w19. No op7 premise remains; its 115 is supplied by installed_count. None of those other producers was supplied by this job. In particular, no always-reject, valueOnly, noReadOther, success assumption, whole-output equality, or all-driver budget premise is chosen as a witness. All original arbitrary inputs/oracles/results/provers remain quantified.

## Unchanged actual program and saved carrier

Port16CUT_Cuts.sourceOne/sourceTwo and sourceOne_eq/sourceTwo_eq are reused unchanged; Port16CUT_Driver.stages_eq and next are reused unchanged. On `.ok (.Ok saved)`, next invokes sourceTwo with saved.deref. Rejection prefixes remain in the same Program evaluations. Actual Flow definitions and the 1046 owned subtotal are unchanged. First-read and repeated-pass metrics remain distinct.

## Native association frontier

This is a selected source-model installation. The op7 effects equality is at A's exact per-H P3 dictionary; the arbitrary-D count is not a theorem identifying native D and H. All R decode/boundary/value and B fromFn/mask/add/mul/terminal/circle/claims leaves stay explicit through sourceOps. Base allocation/Result operations, original powers/from_fn/numeric/Std leaves, parser/query/root/transcript/terminal-classifier/nohit, native SDK/account/abort effects, StoredCarrierBinding and frozen release/artifact identities remain unproved associations where they were open in A/Port16. NativeBindings is not silently installed or discharged by these model count facts. No new trust assumption or security expression/metric change is introduced. Both deployed targets remain not yet established.

## Compatibility freeze and reuse qualifications

The immutable A final import manifest is selected over historical direct-import requests; historical dependency mismatches are preserved in dependency-inventory.json. All 13415 selected final .olean hashes matched before checking consumers. The source copy overlay contains only original committed bytes, with no import/declaration/model edits. The committed reused VTop_Model source is byte-identical to this root; VTop_Model and VTop_OracleCode object hashes also match root receipts exactly. Other imported module versions, including Aeneas and older preparation modules, are frozen by their actual final object hashes. Their changed bytes are not attributed to older receipts or to release ELF identity.

Root control proofs use the original pinned host cache. Concrete preparation/driver consumers use the authorized local pinned warm union after the Linux import/interpreter threshold failures; this is an explicitly assessed combined source-model cache, not a coherent SDK/frozen release replay. The raw import scanner checks actual root object headers, and all additional 611 root objects are pinned in root-local-pins-final.json. The local manifest additionally pins 11003 IR sidecars. All local outputs are task-owned; original caches and A's worktree/outputs are unmodified. No full manifest or unchanged source/environment replay ran. Pre-Lean guard attempt 011 is charged and explicitly lacks Lean metrics because no Lean process executed.

## Why the remaining zero-cost claim cannot be inferred

At the exact Implementation type, `fun {_} _ => .ask [] (fun _ => .done .div)` is an admissible oracle Program: every call issues one read then returns outer div. By the actual Program.eval equations it has log length 1 on every oracle, including on delegated op3. This is an analytical type-level counterexample, not a compiled native producer, not the installed implementation, and not a witness used by any theorem here. It shows why typing arbitrary `other`, or Result-lifting an unrelated helper, cannot discharge the zero-cost source/native producer gate. The final theorem retains those per-call premises instead.

## Joint installation parameters and native boundaries

| Parameter | Exact role in this installation | Association retained open |
| --- | --- | --- |
| `ops : VTop_Stages.Ops` | Existing Port9 library/owned checkpoint/batch dictionary | Actual SDK/native meanings of its retained non-owned leaves |
| `base : AspisR1CurrentCaller.Ops` | The SAME base passed to A body, code, sourceOps and installed effects/count | Native allocation/numeric/Std and all still-abstract current-caller leaves |
| `R : RoundModel.Boundaries` | SAME round boundaries in A's program and sourceOps | decode/boundary/value native associations |
| `B : FinishModel.Boundaries` | SAME finish boundaries in A's program and sourceOps | fromFn/mask/add/mul/terminal/circle/claims native associations; the structure also has unwrapRoot, which A replaces with its exact S1SemanticRootCopy.install implementation |
| `other : Implementation` | SAME retained implementation for all non-op7 delegated calls and observer-Some op7 | Actual reached source producers and their effects/bounds; no synthetic implementation supplied |
| `adapter : AdapterRw.Ops` | Existing driver input/public decoding and same saved-Vec control | Actual account/owned SDK source binding, abort effects and StoredCarrierBinding |
| `D`, `hash`, `H` | Unchanged complete op7 ABI and reply-driven Program interpretation | Native dictionary/oracle association; source/value equality is explicitly at A's per-H P3 dictionary |

No equality between `ops`, `base`, adapter leaves or an actual native installation follows merely from their types. A future native result must instantiate all of these SAME parameters under the existing NativeBindings/source obligations. This packet proves the count/effects of the explicit model installation and does not manufacture such a joint native binding.
