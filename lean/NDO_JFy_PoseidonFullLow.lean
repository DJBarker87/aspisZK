import NDO_JFy_PoseidonLowCall
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_PoseidonFullLow
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open state_only_poseidon.evaluate_state_only_poseidon_oracle_projected

theorem loop (xs : List Usize) (s : state_only_poseidon.StateOnlyPoseidonSelectors) (acc : field.QM31)
    (hs : canonical s.«local») (ha : Canon acc) (hb : ∀ i∈xs,i.val<16) :
    ∃ out,core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.fold (N:=3#usize)
      closure.Insts.CoreOpsFunctionFnMutPairQM31UsizeQM31 xs acc s=ok out ∧ Canon out := by
  induction xs generalizing acc with
  | nil => exact ⟨acc,rfl,ha⟩
  | cons i xs ih =>
    obtain ⟨next,hn,hnc⟩ := JFy_PoseidonLowCall.full s acc i hs ha (hb i (by simp))
    obtain ⟨out,tail,hout⟩ := ih next hnc (by intro i hi;exact hb i (List.mem_cons_of_mem _ hi))
    refine ⟨out,?_,hout⟩
    simp only [core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.fold]
    erw [hn,bind_tc_ok]
    exact tail
#print axioms loop

theorem source (s : state_only_poseidon.StateOnlyPoseidonSelectors) (hs : canonical s.«local») :
    ∃ out,core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.fold (N:=3#usize)
      closure.Insts.CoreOpsFunctionFnMutPairQM31UsizeQM31 [1#usize,9#usize,10#usize] field.QM31.ZERO s=ok out ∧ Canon out := by
  apply loop _ s field.QM31.ZERO hs FIv_NativeValue.zero.1
  intro i hi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl <;> decide
#print axioms source
end AspisR1.JFy_PoseidonFullLow
end
