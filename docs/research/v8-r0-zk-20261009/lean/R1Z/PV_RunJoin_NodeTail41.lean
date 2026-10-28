import R1Z.PV_RunJoin_ByteAppend38
set_option autoImplicit false
namespace R1Z.PV_RunJoin_NodeTail41
open Aeneas Aeneas.Std Result ProverRwFull
abbrev Bytes := alloc.vec.Vec U8

/-- The exact tail of emitted append_node_slot, factored after the multiproof
and slot-cap reads. Native multiproof construction is not assumed proved. -/
def finish (out nodes : Bytes) (cap : Usize) : Result Bytes := do
  massert (alloc.vec.Vec.len nodes≤cap)
  let out1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out (alloc.vec.Vec.deref nodes)
  let padded := Usize.wrapping_sub
    (Usize.wrapping_add (alloc.vec.Vec.len out1) cap) (alloc.vec.Vec.len nodes)
  alloc.vec.Vec.resize core.clone.CloneU8 out1 padded 0#u8

theorem accepts (out nodes : Bytes) (cap : Usize) (fits : nodes.val.length≤cap.val)
    (room : out.val.length+nodes.val.length+cap.val≤Usize.max) :
    ∃ result, finish out nodes cap=ok result ∧
      result.val=out.val++nodes.val++List.replicate (cap.val-nodes.val.length) 0#u8 := by
  obtain ⟨after,ha,hv⟩ := PV_RunJoin_ByteAppend38.append out (alloc.vec.Vec.deref nodes) (by exact (show out.val.length+nodes.val.length≤Usize.max from (by omega)))
  have len : after.val.length=out.val.length+nodes.val.length := by
    rw [hv,List.length_append]
  have hfits : alloc.vec.Vec.len nodes ≤ cap := by scalar_tac
  have add : (Usize.wrapping_add (alloc.vec.Vec.len after) cap).val=after.val.length+cap.val := by
    rw [Usize.wrapping_add_val_eq]
    change (after.val.length+cap.val) % UScalar.size .Usize = _
    apply Nat.mod_eq_of_lt
    rw [UScalar.size_def,UScalarTy.Usize_numBits_eq]
    have max := Usize.max_succ_eq_pow
    omega
  have sub : (Usize.wrapping_sub (Usize.wrapping_add (alloc.vec.Vec.len after) cap)
      (alloc.vec.Vec.len nodes)).val=out.val.length+cap.val := by
    rw [Usize.wrapping_sub_val_eq,add]
    change ((after.val.length+cap.val+(UScalar.size .Usize-nodes.val.length)) %
      UScalar.size .Usize)=out.val.length+cap.val
    have size : Usize.max+1=UScalar.size .Usize := by
      rw [UScalar.size_def,UScalarTy.Usize_numBits_eq]
      exact Usize.max_succ_eq_pow
    have bound : out.val.length+cap.val<UScalar.size .Usize := by omega
    have cb : cap.val<UScalar.size .Usize := by omega
    have num : after.val.length+cap.val+(UScalar.size .Usize-nodes.val.length) =
        (out.val.length+cap.val)+UScalar.size .Usize := by omega
    rw [num,Nat.add_mod,Nat.mod_self,Nat.add_zero,Nat.mod_mod]
    exact Nat.mod_eq_of_lt bound
  let finalLen := Usize.wrapping_sub (Usize.wrapping_add (alloc.vec.Vec.len after) cap)
    (alloc.vec.Vec.len nodes)
  obtain ⟨result,hr,he⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.resize_spec core.clone.CloneU8 after finalLen 0#u8 rfl)
  change alloc.vec.Vec.resize core.clone.CloneU8 after
    (Usize.wrapping_sub (Usize.wrapping_add (alloc.vec.Vec.len after) cap)
      (alloc.vec.Vec.len nodes)) 0#u8=ok result at hr
  refine ⟨result,?_,?_⟩
  · simp only [finish,massert,hfits,if_true,ha,bind_tc_ok,lift,hr]
  · rw [he]
    have flen : finalLen.val=out.val.length+cap.val := sub
    simp only [List.resize,flen,Nat.zero_le,if_true]
    rw [List.take_of_length_le (by omega),hv]
    congr 1
    simp only [List.length_append]
    congr 1
    omega

#print axioms accepts
end R1Z.PV_RunJoin_NodeTail41
