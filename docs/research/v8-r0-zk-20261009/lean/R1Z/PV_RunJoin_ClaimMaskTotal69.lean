import R1Z.PV_RunJoin_NativeMaskValueTotal69
import R1Z.ProverRwP6ArrayRead
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ClaimMaskTotal69
open Aeneas Aeneas.Std Result ProverRwFull
abbrev Q := aspis_core.field.QM31

theorem copy {T : Type} {n : Usize} (inst : core.marker.Copy T)
    (initial : Array T n) (src : Slice T) (size : src.length=n.val) :
    core.slice.Slice.copy_from_slice inst (Array.to_slice initial) src=ok src := by
  have same : Slice.len (Array.to_slice initial)=Slice.len src := by
    apply UScalar.eq_of_val_eq
    change initial.val.length=src.val.length
    exact initial.property.trans size.symm
  simp only [core.slice.Slice.copy_from_slice,same,if_true]

variable [ExternalTypes] [ExternalFuns]
theorem complete
    (zero : ∃ z,aspis_core.field.QM31.ZERO=ok z)
    (selected : ∀ c1 mask g point,∃ out,
      aspis_core.state_only_hiding.state_only_selected_mask_value c1 mask g point=ok out)
    (claims : Array Q 29#usize) (point : Array Q 10#usize) :
    ∃ out,host_semantic.claim_mask_value claims point=ok out := by
  obtain ⟨z,hz⟩ := zero
  have size : (Array.to_slice claims).length=29 := claims.property
  obtain ⟨s1,hs1,hval1,hsize1⟩ := WP.spec_imp_exists
    (core.slice.index.SliceIndexRangeToUsizeSlice.index.step_spec
      ({«end»:=16#usize} : core.ops.range.RangeTo Usize) (Array.to_slice claims) (by rw [size];decide))
  obtain ⟨s2,hs2,hval2,hsize2⟩ := WP.spec_imp_exists
    (core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
      ({start:=16#usize,«end»:=26#usize} : core.ops.range.Range Usize) (Array.to_slice claims)
      (by decide) (by rw [size];decide))
  have hi1 : core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice Q)) claims {«end»:=16#usize}=ok s1 := hs1
  have hi2 : core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Q)) claims {start:=16#usize,«end»:=26#usize}=ok s2 := hs2
  have hc1 := copy aspis_core.field.QM31.Insts.CoreMarkerCopy (Array.repeat 16#usize z) s1 hsize1
  have hc2 := copy aspis_core.field.QM31.Insts.CoreMarkerCopy (Array.repeat 10#usize z) s2 hsize2
  obtain ⟨g,hg⟩ := ProverRwP6ArrayRead.read claims 27#usize (by decide)
  obtain ⟨out,ho⟩ := selected
    ((Array.repeat 16#usize z).from_slice s1) ((Array.repeat 10#usize z).from_slice s2) g point
  exact ⟨out,by simp only [host_semantic.claim_mask_value,hz,hi1,hi2,Array.to_slice_mut,
    lift,hc1,hc2,hg,ho,bind_tc_ok,Aeneas.Std.uncurry]⟩

#print axioms copy
#print axioms complete
end R1Z.PV_RunJoin_ClaimMaskTotal69
