import R1Z.PV_RunJoin_SourceRoundFold
import R1Z.PV_Src_PortInternalRoundStep
/-! Proof draft reused read-only from srcid d597d31545. This new module is checked independently; no upstream draft is assumed compiled. -/

set_option autoImplicit false
namespace R1Z.PV_RunJoin_SourceInternalRounds
open Aeneas Aeneas.Std Result BuilderStdModels R0Z.PoseidonRefine
open BuilderForestStdPort BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_SourceRoundFold

abbrev Iter := core.iter.adapters.enumerate.Enumerate (core.array.iter.IntoIter U32 14#usize)
def iterator : core.iter.traits.iterator.Iterator Iter (Usize × U32) where
  next := core.iter.adapters.enumerate.IteratorEnumerate.next
    (core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator U32 14#usize)

def steps {F : Type}
    (callback : core.ops.function.FnMut F poseidon2.Poseidon2RoundTransition Unit)
    (xs : List (Usize × U32)) (s : State) (trace : F) (round : U8) (input : State) :
    Result (Output F) :=
  match xs with
  | [] => ok (s,trace,round,input)
  | (index,c)::tail => do
    let out ← R0PoseidonCopy.internal_round s c R0PoseidonCopy.INTERNAL_SHIFTS
    let (_,trace1) ← callback.call_mut trace
      ({round,kind := poseidon2.Poseidon2RoundKind.Internal (UScalar.cast .U8 index),
        input,output := out} : poseidon2.Poseidon2RoundTransition)
    steps callback tail out trace1 (U8.wrapping_add round 1#u8) out

theorem total (s : State) (c : U32) : ∃ out,
    R0PoseidonCopy.internal_round s c R0PoseidonCopy.INTERNAL_SHIFTS = ok out ∧ Canonical out := by
  letI : Fact (Nat.Prime 2147483647) := ⟨R0Z.m31_prime⟩
  obtain ⟨out,ho,_⟩ := internal_round_lift (K := ZMod 2147483647) s c R0PoseidonCopy.INTERNAL_SHIFTS
    PV_Src_PortInternalCopy.shifts_bound PV_Src_PortInternalCopy.shifts_model
  exact ⟨out,ho,fun j => internal_round_canon s c R0PoseidonCopy.INTERNAL_SHIFTS out ho j.val j.isLt⟩

theorem source {F : Type}
    (callback : core.ops.function.FnMut F poseidon2.Poseidon2RoundTransition Unit)
    (iter : Iter) (xs : List (Usize × U32)) (ht : FiniteTrace iterator iter xs)
    (s input : State) (trace : F) (round : U8) (hs : Canonical s)
    (hc : ∀ p ∈ xs, p.2.val < 2147483647) :
    poseidon2.permute_optimized_with_trace_loop1 callback iter s trace round input =
      steps callback xs s trace round input := by
  induction ht generalizing s input trace round with
  | done it it' hn =>
    simp only [iterator] at hn
    rw [poseidon2.permute_optimized_with_trace_loop1,hn]
    rfl
  | step it it' p xs hn tail ih =>
    simp only [iterator] at hn
    rcases p with ⟨index,c⟩
    have hconst : c.val < 2147483647 := hc (index,c) (by simp)
    have htail : ∀ p ∈ xs, p.2.val < 2147483647 := fun p hp => hc p (by simp [hp])
    rw [PV_Src_PortInternalRoundStep.source callback it it' s input trace round index c hn hs hconst]
    obtain ⟨out,ho,hcan⟩ := total s c
    simp only [steps,ho,bind_tc_ok]
    congr 1
    funext p
    exact ih out out p.2 (U8.wrapping_add round 1#u8) hcan htail

#print axioms total
#print axioms source
end R1Z.PV_RunJoin_SourceInternalRounds
