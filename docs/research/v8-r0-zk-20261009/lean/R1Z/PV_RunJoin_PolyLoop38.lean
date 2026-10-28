import R1Z.PV_RunJoin_PolyStep38
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PolyLoop38
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_PolyCell38
variable [ExternalTypes]

/-- Independent coefficient order, with each 32-byte normalized field cell. -/
def payload (p : Nat → Q) (start : Nat) : Nat → List U8
  | 0 => []
  | n+1 => cell (p start) ++ payload p (start+1) n

theorem payload_length (p : Nat → Q) (start n : Nat) :
    (payload p start n).length=32*n := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih => rw [payload,List.length_append,PV_RunJoin_PolyCell38.length,ih];omega

/-- Complete source Result for every suffix of the actual 28-cell encoder.
The capacity guard is explicit and is discharged at the entry point. Native
allocation and copy effects are separate from this Aeneas value law. -/
theorem complete (ops : ExternalFuns) (p : Nat → Q) (n : Nat)
    (i : Usize) (bytes : alloc.vec.Vec U8) (bound : i.val+n=28)
    (room : bytes.val.length+32*n≤Usize.max) :
    ∃ next, @host_sumcheck.encode_polynomial_loop _ (ProverRwP6BodyCandidate.selected ops)
      (ProverCommitArray49.array 28#usize p) bytes i = .ok next ∧
      next.val=bytes.val ++ payload p i.val n := by
  induction n generalizing i bytes with
  | zero =>
    refine ⟨bytes,?_,by simp only [payload,List.append_nil]⟩
    unfold host_sumcheck.encode_polynomial_loop
    rw [ProverRw19LoopBind.loop_bind]
    simp only [PV_RunJoin_PolyStep38.stop ops _ bytes i (by omega),bind_tc_ok]
  | succ n ih =>
    have hi : i.val<28 := by omega
    have inc := PV_RunJoin_MergeLoop35.increment i (by omega)
    obtain ⟨mid,hmid,hval⟩ := PV_RunJoin_PolyStep38.step ops p bytes i hi (by
      change bytes.val.length+32≤Usize.max
      omega)
    have hlen : mid.val.length=bytes.val.length+32 := by
      rw [hval,List.length_append,PV_RunJoin_PolyCell38.length]
    obtain ⟨next,hnext,hbytes⟩ := ih (Usize.wrapping_add i 1#usize) mid
      (by rw [inc];omega) (by rw [hlen];omega)
    refine ⟨next,?_,?_⟩
    · unfold host_sumcheck.encode_polynomial_loop
      rw [ProverRw19LoopBind.loop_bind]
      dsimp only
      rw [hmid]
      simp only [bind_tc_ok]
      exact hnext
    · rw [hbytes,hval,inc,payload,List.append_assoc]

#print axioms payload_length
#print axioms complete
end R1Z.PV_RunJoin_PolyLoop38
