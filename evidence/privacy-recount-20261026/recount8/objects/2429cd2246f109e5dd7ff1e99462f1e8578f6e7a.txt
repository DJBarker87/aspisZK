import R1Z.PV_RunJoin_ResultPost41
import R1Z.PV_RunJoin_HighCell41
import R1Z.PV_RunJoin_HighAppend41
import R1Z.PV_RunJoin_ByteAppend38
import R1Z.PV_RunJoin_MergeLoop35
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_EndpointPost41
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_PolyCell38 PV_RunJoin_ResultPost41 PV_RunJoin_HighDomain40
variable [ExternalTypes]

/-- A successful endpoint loop retains its exact length and canonicality.
All coefficient/evaluation failures remain source failures. This is a success
postcondition, never a decoder or native-effect replacement. -/
theorem loop (ops : ExternalFuns)
    (columns : Array (alloc.vec.Vec Q) 29#usize) (variant : transport.Variant)
    (z : aspis_core.circle.SecureCirclePoint) (n : Nat) (i : Usize)
    (out : alloc.vec.Vec U8) (bound : i.val+n=29)
    (room : out.length+32*n≤Usize.max) (aligned : out.length%32=0)
    (canonical : HighZero out.val) :
    Post (fun next : alloc.vec.Vec U8 =>
      next.length=out.length+32*n ∧ HighZero next.val)
      (@host_semantic.endpoint_bytes_loop _ (ProverRwP6BodyCandidate.selected ops)
        columns variant z out i) := by
  induction n generalizing i out with
  | zero =>
    unfold host_semantic.endpoint_bytes_loop
    rw [ProverRw19LoopBind.loop_bind]
    simp only [host_semantic.endpoint_bytes_loop.body,
      show ¬i<29#usize from (by change ¬i.val<29;omega),↓reduceIte,bind_tc_ok]
    exact ⟨by omega,canonical⟩
  | succ n ih =>
    have hi : i<29#usize := by change i.val<29;omega
    have inc := PV_RunJoin_MergeLoop35.increment i (by omega)
    unfold host_semantic.endpoint_bytes_loop
    rw [ProverRw19LoopBind.loop_bind]
    simp only [host_semantic.endpoint_bytes_loop.body,hi,↓reduceIte,bind_assoc_eq]
    apply PV_RunJoin_ResultPost41.bind
    intro column
    apply PV_RunJoin_ResultPost41.bind
    intro coefficients
    apply PV_RunJoin_ResultPost41.bind
    intro q
    rw [show @aspis_core.field.wide_exact.WideExact.from_qm31 _
      (ProverRwP6BodyCandidate.selected ops) q=.ok (wide q) from embed ops q]
    simp only [bind_tc_ok]
    rw [show @aspis_core.field.wide_exact.WideExact.to_le_bytes _
      (ProverRwP6BodyCandidate.selected ops) (wide q)=
        .ok (PV_RunJoin_FlatBytes35.wire (wide q)) from
      PV_RunJoin_FlatBytes35.installed ops (wide q)]
    simp only [bind_tc_ok,lift]
    obtain ⟨mid,hm,hv⟩ := PV_RunJoin_ByteAppend38.append out
      (Array.to_slice (PV_RunJoin_FlatBytes35.wire (wide q))) (by
        change out.length+32≤Usize.max;omega)
    rw [hm]
    simp only [bind_tc_ok]
    have ml : mid.length=out.length+32 := by
      change mid.val.length=out.val.length+32
      rw [hv,List.length_append]
      exact congrArg (fun k => out.val.length+k) (PV_RunJoin_PolyCell38.length q)
    have mh : HighZero mid.val := by
      rw [hv]
      exact PV_RunJoin_HighAppend41.append out.val (cell q) (out.length/32)
        (by change out.length=32*(out.length/32);omega) canonical (PV_RunJoin_HighCell41.high q)
    have next := ih (Usize.wrapping_add i 1#usize) mid (by rw [inc];omega)
      (by rw [ml];omega) (by rw [ml];omega) mh
    have len : mid.length+32*n=out.length+32*(n+1) := by rw [ml];omega
    simpa only [len,host_semantic.endpoint_bytes_loop,host_semantic.endpoint_bytes_loop.body,
      lift,bind_tc_ok] using next
#print axioms loop
end R1Z.PV_RunJoin_EndpointPost41
