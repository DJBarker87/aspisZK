import R1Z.PV_RunJoin_OpeningStep41
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OpeningLoop41
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_OpeningCell41 PV_RunJoin_OpeningStep41
variable [ExternalTypes]

def payload (p : Nat → W) (width start : Nat) : Nat → List U8
  | 0 => []
  | n+1 => piece (p start) width ++ payload p width (start+1) n

theorem length (p : Nat → W) (width start n : Nat) (hw : width≤32) :
    (payload p width start n).length=width*n := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
    rw [payload,List.length_append,PV_RunJoin_OpeningCell41.length _ _ hw,ih]
    rw [Nat.mul_succ]
    omega

/-- Complete actual base loop Result for every suffix, preserving lane order. -/
theorem base (ops : ExternalFuns) (p : Nat → W) (n : Nat)
    (i : Usize) (out : alloc.vec.Vec U8) (bound : i.val+n=26)
    (room : out.length+4*n≤Usize.max) :
    ∃ next, @prover.append_opening_base_row_loop _ (ProverRwP6BodyCandidate.selected ops) out
      (ProverCommitArray49.array 29#usize p) i=.ok next ∧
      next.val=out.val ++ payload p 4 i.val n := by
  induction n generalizing i out with
  | zero =>
    refine ⟨out,?_,by simp only [payload,List.append_nil]⟩
    unfold prover.append_opening_base_row_loop
    rw [ProverRw19LoopBind.loop_bind]
    simp only [PV_RunJoin_OpeningStep41.base_stop ops _ out i (by omega),bind_tc_ok]
  | succ n ih =>
    have hi : i.val<26 := by omega
    have inc := PV_RunJoin_MergeLoop35.increment i (by omega)
    obtain ⟨mid,hm,hv⟩ := PV_RunJoin_OpeningStep41.base_step ops p out i hi (by omega)
    have hl : mid.length=out.length+4 := by
      change mid.val.length=out.val.length+4
      rw [hv,List.length_append,PV_RunJoin_OpeningCell41.length _ _ (by decide)]
    obtain ⟨next,hn,hnext⟩ := ih (Usize.wrapping_add i 1#usize) mid
      (by rw [inc];omega) (by rw [hl];omega)
    refine ⟨next,?_,?_⟩
    · unfold prover.append_opening_base_row_loop
      rw [ProverRw19LoopBind.loop_bind]
      dsimp only
      rw [hm]
      simp only [bind_tc_ok]
      exact hn
    · rw [hnext,hv,inc,payload,List.append_assoc]
#print axioms base

/-- Complete actual secure loop Result for every suffix, preserving lane order. -/
theorem secure (ops : ExternalFuns) (p : Nat → W) (n : Nat)
    (i : Usize) (out : alloc.vec.Vec U8) (bound : i.val+n=28)
    (room : out.length+16*n≤Usize.max) :
    ∃ next, @prover.append_opening_secure_row_loop _ (ProverRwP6BodyCandidate.selected ops) out
      (ProverCommitArray49.array 29#usize p) i=.ok next ∧
      next.val=out.val ++ payload p 16 i.val n := by
  induction n generalizing i out with
  | zero =>
    refine ⟨out,?_,by simp only [payload,List.append_nil]⟩
    unfold prover.append_opening_secure_row_loop
    rw [ProverRw19LoopBind.loop_bind]
    simp only [PV_RunJoin_OpeningStep41.secure_stop ops _ out i (by omega),bind_tc_ok]
  | succ n ih =>
    have hi : i.val<28 := by omega
    have inc := PV_RunJoin_MergeLoop35.increment i (by omega)
    obtain ⟨mid,hm,hv⟩ := PV_RunJoin_OpeningStep41.secure_step ops p out i hi (by omega)
    have hl : mid.length=out.length+16 := by
      change mid.val.length=out.val.length+16
      rw [hv,List.length_append,PV_RunJoin_OpeningCell41.length _ _ (by decide)]
    obtain ⟨next,hn,hnext⟩ := ih (Usize.wrapping_add i 1#usize) mid
      (by rw [inc];omega) (by rw [hl];omega)
    refine ⟨next,?_,?_⟩
    · unfold prover.append_opening_secure_row_loop
      rw [ProverRw19LoopBind.loop_bind]
      dsimp only
      rw [hm]
      simp only [bind_tc_ok]
      exact hn
    · rw [hnext,hv,inc,payload,List.append_assoc]
#print axioms secure
#print axioms length
end R1Z.PV_RunJoin_OpeningLoop41
