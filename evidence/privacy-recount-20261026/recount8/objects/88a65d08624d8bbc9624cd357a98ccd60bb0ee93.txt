import R1Z.PV_RunJoin_FoldStepValue44
import R1Z.PV_RunJoin_SourceArray44
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FoldLoopValue44
open Aeneas Aeneas.Std Result ProverRwFull
open ProverCommitWideOps48 ProverCommitMix48 PV_RunJoin_WideArithmetic44
open PV_RunJoin_FoldCell44 (array)
variable [ExternalTypes]

theorem complete (ops : ExternalFuns) (count : Usize) (q z : Nat → Raw) (a : Raw) (dual : Bool)
    (hq : ∀ j, j < count.val → canonical (q j)) (ha : canonical a)
    (hz : ∀ j, j < count.val / 4 → canonical (z j))
    (hd : ∀ j, j < count.val / 4 → value (z j) = PV_RunJoin_FoldStepValue44.model q a dual j)
    (n : Nat) (out : alloc.vec.Vec W) (i : Usize) (bound : i.val + n = count.val / 4)
    (small : count.val / 4 ≤ 256) (room : out.length + n ≤ Usize.max) :
    ∃ next, @PV_RunJoin_FoldThread44.phase _ (ProverRwP6BodyCandidate.selected ops)
      (Array.to_slice (array count q)) (current (source a)) dual n out i = .ok next ∧
      next.val = out.val ++ PV_RunJoin_BatchLoopValue44.payload z i.val n := by
  induction n generalizing out i with
  | zero => exact ⟨out,rfl,by simp only [PV_RunJoin_BatchLoopValue44.payload,List.append_nil]⟩
  | succ n ih =>
    have hi : i.val < count.val / 4 := by omega
    obtain ⟨y,mid,hm,hmv,hcy,hdy⟩ := PV_RunJoin_FoldStepValue44.step ops count q a dual hq ha
      i (by omega) (by omega) out (by omega)
    have same : y = z i.val := PV_RunJoin_WideUnique44.unique y (z i.val) hcy (hz _ hi)
      (hdy.trans (hd _ hi).symm)
    rw [same] at hmv
    have ml : mid.length = out.length + 1 := by
      rw [show mid.length=mid.val.length from rfl,hmv,List.length_append,List.length_singleton]
    have inc := PV_RunJoin_MergeLoop35.increment i (by omega)
    obtain ⟨next,hn,hnv⟩ := ih mid (Usize.wrapping_add i 1#usize) (by rw [inc];omega) (by rw [ml];omega)
    refine ⟨next,?_,?_⟩
    · simp only [PV_RunJoin_FoldThread44.phase,hm,bind_tc_ok,hn]
    · rw [hnv,hmv,inc,PV_RunJoin_BatchLoopValue44.payload,List.append_assoc,List.singleton_append]
#print axioms complete
end R1Z.PV_RunJoin_FoldLoopValue44
