import R1Z.PV_RunJoin_WideStep38
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_WideLoop38
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WideStep38
variable [ExternalTypes]

def payload (f : Nat → W) (start : Nat) : Nat → List U8
  | 0 => []
  | n+1 => (PV_RunJoin_FlatBytes35.wire (f start)).val ++ payload f (start+1) n

theorem payload_length (f : Nat → W) (start n : Nat) :
    (payload f start n).length=32*n := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
    rw [payload,List.length_append,(PV_RunJoin_FlatBytes35.wire (f start)).property,ih]
    change 32+32*n=32*(n+1)
    omega

theorem complete (ops : ExternalFuns) (size : Usize) (f : Nat → W) (n : Nat)
    (k : Usize) (bytes : alloc.vec.Vec U8) (bound : k.val+n=size.val)
    (room : bytes.val.length+32*n≤Usize.max) :
    ∃ next,
      @prover.encoded_slice_loop _ (ProverRwP6BodyCandidate.selected ops)
        (input size f) bytes k = .ok next ∧
      next.val=bytes.val ++ payload f k.val n := by
  induction n generalizing k bytes with
  | zero =>
    refine ⟨bytes,?_,by simp only [payload,List.append_nil]⟩
    unfold prover.encoded_slice_loop
    rw [ProverRw19LoopBind.loop_bind]
    simp only [PV_RunJoin_WideStep38.stop ops size f bytes k (by omega),bind_tc_ok]
  | succ n ih =>
    have hk : k.val<size.val := by omega
    have inc := PV_RunJoin_WideStep38.increment size k hk
    obtain ⟨mid,hmid,hval⟩ := PV_RunJoin_WideStep38.step ops size f bytes k hk (by
      change bytes.val.length+32≤Usize.max
      omega)
    have hlen : mid.val.length=bytes.val.length+32 := by
      rw [hval,List.length_append,(PV_RunJoin_FlatBytes35.wire (f k.val)).property]
      rfl
    obtain ⟨next,hnext,hbytes⟩ := ih (Usize.wrapping_add k 1#usize) mid
      (by rw [inc];omega) (by rw [hlen];omega)
    refine ⟨next,?_,?_⟩
    · unfold prover.encoded_slice_loop
      rw [ProverRw19LoopBind.loop_bind]
      dsimp only
      rw [hmid]
      simp only [bind_tc_ok]
      exact hnext
    · rw [hbytes,hval,inc,payload,List.append_assoc]

#print axioms payload_length
#print axioms complete
end R1Z.PV_RunJoin_WideLoop38
