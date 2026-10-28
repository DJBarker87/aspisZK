import R1Z.PV_RunJoin_EncodedStep41
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_EncodedLoop41
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_EncodedStep41
variable [ExternalTypes]

def payload (values : Slice W) (start : Nat) : Nat → List U8
  | 0 => []
  | n+1 => (PV_RunJoin_FlatBytes35.wire (entry values start)).val ++ payload values (start+1) n

theorem length (values : Slice W) (start n : Nat) :
    (payload values start n).length=32*n := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
    rw [payload,List.length_append,(PV_RunJoin_FlatBytes35.wire _).property,show (32#usize).val=32 from rfl,ih]
    omega

/-- Complete source encoded_slice loop, retaining every byte of every wide
value. No canonicality, encoder-success or desired security equation premise. -/
theorem complete (ops : ExternalFuns) (values : Slice W) (n : Nat)
    (i : Usize) (out : alloc.vec.Vec U8) (bound : i.val+n=values.length)
    (room : out.length+32*n≤Usize.max) :
    ∃ next, @prover.encoded_slice_loop _ (ProverRwP6BodyCandidate.selected ops)
      values out i=.ok next ∧ next.val=out.val ++ payload values i.val n := by
  induction n generalizing i out with
  | zero =>
    refine ⟨out,?_,by simp only [payload,List.append_nil]⟩
    unfold prover.encoded_slice_loop
    rw [ProverRw19LoopBind.loop_bind]
    simp only [PV_RunJoin_EncodedStep41.stop ops values out i (by omega),bind_tc_ok]
  | succ n ih =>
    have hi : i.val<values.length := by omega
    have cap : values.length≤Usize.max := values.property
    have inc := PV_RunJoin_CompactStep39.offset i 1#usize (by change i.val+1≤Usize.max;omega)
    obtain ⟨mid,hm,hv⟩ := PV_RunJoin_EncodedStep41.step ops values out i hi (by omega)
    have ml : mid.length=out.length+32 := by
      change mid.val.length=out.val.length+32
      rw [hv,List.length_append,(PV_RunJoin_FlatBytes35.wire _).property]
      rfl
    obtain ⟨next,hn,hnext⟩ := ih (Usize.wrapping_add i 1#usize) mid
      (by rw [inc];omega) (by rw [ml];omega)
    refine ⟨next,?_,?_⟩
    · unfold prover.encoded_slice_loop
      rw [ProverRw19LoopBind.loop_bind]
      dsimp only
      rw [hm]
      simp only [bind_tc_ok]
      exact hn
    · rw [hnext,hv,inc,payload,List.append_assoc]
#print axioms length
#print axioms complete
end R1Z.PV_RunJoin_EncodedLoop41
