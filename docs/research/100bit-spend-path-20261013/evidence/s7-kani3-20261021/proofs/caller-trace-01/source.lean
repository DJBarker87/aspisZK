import S7Kani3CallerStep
set_option autoImplicit false
noncomputable section
namespace S7Kani3CallerTrace
open Aeneas Aeneas.Std Result
open S7Kani2AccumulatorLoop (BatchedWeights K)
open S7Kani2OwnedRowRefinement (makeRow powerLimb)
open S8OwnedP6ValueModel (rowAt coordinate Q Row)
open S8OwnedP6Finish (Raw Weights)
open S8Kani2CallerJoin (CallerInvariant)
abbrev Sum := Nat → Fin 4 → Nat

def initialRow (q : Q) : Row :=
  makeRow (fun k => core.convert.num.FromU64U32.from (coordinate q k))
def initialRaw (old : Weights) : Raw :=
  ⟨old.val.map initialRow,by simpa using old.property⟩
def initialSum (old : Weights) : Sum := fun j k =>
  ((old.val[j]?).map (fun q => (coordinate q k).val)).getD 0

theorem initial_invariant (old : Weights) :
    CallerInvariant (initialRaw old) old (initialSum old) := by
  refine ⟨by simp [initialRaw],?_⟩
  intro j row h k
  change (old.val.map initialRow)[j]?=some row at h
  rw [List.getElem?_map] at h
  cases hq : old.val[j]? with
  | none => simp only [hq,Option.map_none] at h; cases h
  | some q =>
      simp only [hq,Option.map_some,Option.some.injEq] at h
      subst row
      simp only [initialRow,S7Kani3CallerStep.rowAt_makeRow,
        AspisR1.ExtractedCurrentCM31Mul.widen_value,initialSum,hq,Option.map_some,Option.getD_some]

/-- This trace records successful *actual emitted* Vec pushes. It deliberately
leaves query/TX trace membership and per-step canonicality/phase provenance
explicit; it is not a model of an arbitrary accepted frozen transaction. -/
inductive PushTrace (old : Weights) : BatchedWeights → Sum → Prop
 | initial : PushTrace old ⟨initialRaw old,0#usize⟩ (initialSum old)
 | push {before after : BatchedWeights} {sum : Sum}
     (history : PushTrace old before sum)
     (index : Usize) (power : K) (basis : U32) (x : Fin 4 → U64)
     (hi : index.val<before.raw.length)
     (hget : before.raw.val[index.val]?=some (makeRow x))
     (hc : ∀ k, (powerLimb power k).val<2^31-1)
     (hb : basis.val<2^31-1)
     (hp : ∀ k, S7Kani3PhaseInvariant.Phase before.terms.val (x k).val)
     (success : S7Kani2OwnedPush.push_owned before index power basis=ok after) :
     PushTrace old after
       (Function.update sum index.val (fun k => sum index.val k+(powerLimb power k).val*basis.val))
 | counter {state : BatchedWeights} {sum : Sum} (history : PushTrace old state sum)
     (terms : Usize) : PushTrace old {state with terms := terms} sum

/-- Reached raw lengths and sum congruence are derived by induction from
concrete initial rows and actual owned source pushes, not assumed at finish. -/
theorem reached_invariant (old : Weights) (state : BatchedWeights) (sum : Sum)
    (trace : PushTrace old state sum) : CallerInvariant state.raw old sum := by
  induction trace with
  | initial => exact initial_invariant old
  | push history index power basis x hi hget hc hb hp success ih =>
      obtain ⟨y,hy,hinv,_⟩ := S7Kani3CallerStep.push_caller_invariant _ old _ ih
        index power basis x hi hget hc hb hp
      have he := Result.ok.inj (success.symm.trans hy)
      simpa only [he] using hinv
  | counter history terms ih => exact ih

/-- S8's existing finish theorem is now instantiated for every such reached
source-push trace. The trace-membership obligation belongs to the TX caller. -/
theorem reached_finish (old : Weights) (state : BatchedWeights) (sum : Sum)
    (trace : PushTrace old state sum) :
    ∃ out : S8Kani2PendingWrite.FinishSlice,
      S8Kani2MutableExtraction.batched_weights.BatchedWeights.finish
        (⟨state.raw,state.terms⟩ : S8Kani2MutableValue.F.BW)
        (S8Kani2FinishReferenceJoin.toSlice old)=ok out ∧
      ∀ i : Usize, i.val<old.length → ∃ q : S8Kani2MutableValue.F.Q,
        Slice.index_usize out i=ok q ∧
        ∀ k : Fin 4, (S8Kani2CallerJoin.coordinate q k).val=sum i.val k%2147483647 ∧
          (S8Kani2CallerJoin.coordinate q k).val<2147483647 := by
  exact S8Kani2CallerJoin.finish_caller_join state.raw old state.terms sum
    (reached_invariant old state sum trace)

#print axioms initial_invariant
#print axioms reached_invariant
#print axioms reached_finish
end S7Kani3CallerTrace
