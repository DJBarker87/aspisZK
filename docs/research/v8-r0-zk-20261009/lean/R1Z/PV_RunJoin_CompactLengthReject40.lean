import R1Z.PV_RunJoin_CompactComplete39
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CompactLengthReject40
open Aeneas Aeneas.Std Result ProverRwFull

/-- Nonintegral cell count rejects before any read or append. -/
theorem reject (logical : Slice U8) (out : alloc.vec.Vec U8)
    (bad : logical.length%32≠0) :
    host_compact.compact_values logical out=.ok (.Err compact.CodecError.Length,out) := by
  obtain ⟨r,hr,hv⟩ := WP.spec_imp_exists
    (UScalar.rem_spec (Slice.len logical) (y := 32#usize) (by decide))
  have rn : r≠0#usize := by
    intro he
    have value : r.val=logical.length%32 := hv
    rw [he] at value
    exact bad value.symm
  unfold host_compact.compact_values
  dsimp only
  rw [hr]
  simp only [bind_tc_ok,show (r != 0#usize)=true from (by simpa only [bne_iff_ne] using rn),↓reduceIte]
#print axioms reject
end R1Z.PV_RunJoin_CompactLengthReject40
