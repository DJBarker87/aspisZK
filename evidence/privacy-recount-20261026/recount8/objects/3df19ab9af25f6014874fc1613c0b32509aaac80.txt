import R1Z.PV_RunJoin_FoldLoopValue44
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FoldCallerValue44
open Aeneas Aeneas.Std Result ProverRwFull
open ProverCommitWideOps48 ProverCommitMix48 PV_RunJoin_WideArithmetic44
open PV_RunJoin_FoldCell44 (array)
variable [ExternalTypes]

theorem complete (ops : ExternalFuns) (count outSize : Usize) (sizes : count.val / 4 = outSize.val)
    (small : outSize.val ≤ 256) (q z : Nat → Raw) (a : Raw) (dual : Bool)
    (hq : ∀ j, j < count.val → canonical (q j)) (ha : canonical a)
    (hz : ∀ j, j < outSize.val → canonical (z j))
    (hd : ∀ j, j < outSize.val → value (z j) = PV_RunJoin_FoldStepValue44.model q a dual j) :
    ∃ out : alloc.vec.Vec W,
      @prover.fold _ (ProverRwP6BodyCandidate.selected ops) (Array.to_slice (array count q))
        (current (source a)) dual = .ok out ∧
      Array.to_slice (array outSize z) = alloc.vec.Vec.deref out := by
  let input := Array.to_slice (array count q)
  have len : input.length = count.val := Array.length_to_slice _
  obtain ⟨k,hk,hkv⟩ := @PV_RunJoin_FoldThread44.quotient _ (ProverRwP6BodyCandidate.selected ops) input
  obtain ⟨out,hout,hv⟩ := PV_RunJoin_FoldLoopValue44.complete ops count q z a dual hq ha
    (fun j hj => hz j (by omega)) (fun j hj => hd j (by omega)) (count.val / 4)
    (alloc.vec.Vec.with_capacity W k) 0#usize (by change 0 + _ = _;omega)
    (by omega) (by
      have cap : 256 ≤ Usize.max := by scalar_tac
      change 0 + count.val / 4 ≤ Usize.max
      omega)
  refine ⟨out,?_,?_⟩
  · rw [@PV_RunJoin_FoldThread44.caller _ (ProverRwP6BodyCandidate.selected ops) input
      (current (source a)) dual (by rw [len];omega),hk]
    simp only [bind_tc_ok,len]
    exact hout
  · apply Subtype.ext
    dsimp only [Array.to_slice,alloc.vec.Vec.deref]
    change (array outSize z).val = out.val
    rw [hv,PV_RunJoin_SourceArray44.payload]
    simp only [alloc.vec.Vec.with_capacity,List.nil_append,show (0#usize).val=0 from rfl,Nat.zero_add,array,ProverCommitArray49.array,sizes]
    rfl
#print axioms complete
end R1Z.PV_RunJoin_FoldCallerValue44
