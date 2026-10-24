# Exact release interface change

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
