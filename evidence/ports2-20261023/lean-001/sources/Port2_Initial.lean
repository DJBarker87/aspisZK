import Port1_ModelOrder

/-! Complete S2 constructor shell and mathematical state conversion.
`newS2` is a source-shaped shell, not an adopted extraction of op12.
The actual filled-heap call and installed op12 equality remain explicit gaps. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port2_Initial
open Aeneas Aeneas.Std Result VTop_Stages
abbrev KRaw := aspis_core.field.QM31
abbrev ERaw := aspis_core.field.wide_exact.WideExact

def zeroK : KRaw := ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩
def oneK : KRaw := ⟨⟨1#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩
def zeroE : ERaw := ⟨zeroK,zeroK⟩
def initial (weights : alloc.vec.Vec KRaw) : verifier.Accumulator :=
  ⟨weights,zeroE,oneK,0#usize⟩

/-- Preserve outer failure/divergence and map only the allocation error. -/
def newS2 {AllocError : Type}
    (filled : Result (core.result.Result (alloc.vec.Vec KRaw) AllocError)) :
    Result (core.result.Result verifier.Accumulator verifier.Error) := do
  match ← filled with
  | .Ok weights => ok (.Ok (initial weights))
  | .Err _ => ok (.Err AdapterRw.aspis_r1_cost_probe.verifier.Error.Allocation)

theorem newS2_success {AllocError : Type}
    (filled : Result (core.result.Result (alloc.vec.Vec KRaw) AllocError))
    (a : verifier.Accumulator) :
    newS2 filled = ok (.Ok a) ↔
      ∃ weights, filled = ok (.Ok weights) ∧ a = initial weights := by
  cases filled with
  | fail e => simp [newS2]
  | div => simp [newS2]
  | ok r => cases r <;> simp [newS2, eq_comm]

theorem newS2_allocation {AllocError : Type} (e : AllocError) :
    newS2 (ok (.Err e)) = ok (.Err AdapterRw.aspis_r1_cost_probe.verifier.Error.Allocation) := rfl

/-- Conversion retains all four accumulator fields. The fallback matters only
outside the separate length invariant; no source admission is inserted. -/
def decode {K E : Type} [Field K] [Field E]
    (dk : KRaw → K) (de : ERaw → E) (a : verifier.Accumulator) :
    QueryAccumulator.State K E where
  weights := fun l => ((a.weights.val[l.val]?).map dk).getD 0
  rhs := de a.rhs
  power := dk a.power
  next := a.next.val

theorem initial_eq {K E : Type} [Field K] [Field E]
    (dk : KRaw → K) (de : ERaw → E) (weights : alloc.vec.Vec KRaw)
    (filled : weights.val = List.replicate 64 zeroK)
    (kzero : dk zeroK = 0) (kone : dk oneK = 1) (ezero : de zeroE = 0) :
    decode dk de (initial weights) = QueryAccumulator.initial := by
  apply QueryAccumulator.State.ext
  · funext l
    simp [decode,initial,filled,List.getElem?_replicate,l.isLt,kzero]
  · exact ezero
  · exact kone
  · rfl

/-- Before/after statement: a successful constructor shell plus the exact
filled-vector contents gives the entire mathematical initial state. -/
theorem returned_initial {AllocError K E : Type} [Field K] [Field E]
    (dk : KRaw → K) (de : ERaw → E)
    (filled : Result (core.result.Result (alloc.vec.Vec KRaw) AllocError))
    (contents : ∀ weights, filled = ok (.Ok weights) → weights.val = List.replicate 64 zeroK)
    (a : verifier.Accumulator) (returned : newS2 filled = ok (.Ok a))
    (kzero : dk zeroK = 0) (kone : dk oneK = 1) (ezero : de zeroE = 0) :
    decode dk de a = QueryAccumulator.initial := by
  obtain ⟨weights,hw,rfl⟩ := (newS2_success filled a).mp returned
  exact initial_eq dk de weights (contents weights hw) kzero kone ezero

#print axioms newS2_success
#print axioms newS2_allocation
#print axioms initial_eq
#print axioms returned_initial
end AspisR1.Port2_Initial
end
