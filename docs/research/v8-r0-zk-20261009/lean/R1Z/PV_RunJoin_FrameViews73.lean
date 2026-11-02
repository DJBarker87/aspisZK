import R1Z.PV_RunJoin_FourReader73
set_option autoImplicit false
namespace R1Z.PV_RunJoin_FrameViews73
open Aeneas Aeneas.Std Result
open PV_RunJoin_FlatBytes35 (byte)

theorem read {T : Type} (s : Slice T) (i : Usize) (hi : i.val<s.length) :
    Slice.index_usize s i=ok (s.val[i.val]'hi) := by
  obtain ⟨v,hv,h⟩ := WP.spec_imp_exists (Slice.index_usize_spec s i hi)
  exact hv.trans (congrArg Result.ok h)

theorem tag (s payload : Slice U8) (t : U8) (w : U32)
    (value : s.val=t::(core.num.U32.to_le_bytes w).val++payload.val) :
    Slice.index_usize s 0#usize=ok t := by
  have bound : (0#usize).val<s.length := by
    change 0<s.val.length
    rw [value,List.length_append,List.length_cons]
    omega
  rw [read s 0#usize bound]
  simp only [value,List.cons_append,List.getElem_cons_zero]

theorem word (s payload : Slice U8) (t : U8) (w : U32)
    (value : s.val=t::(core.num.U32.to_le_bytes w).val++payload.val) :
    PV_RunJoin_FourReader73.read s 1#usize 2#usize 3#usize 4#usize=ok w := by
  have bytes := PV_RunJoin_ByteArrayFour72.complete (core.num.U32.to_le_bytes w)
  have view : s.val=t::[byte w ⟨0,by decide⟩,byte w ⟨1,by decide⟩,
      byte w ⟨2,by decide⟩,byte w ⟨3,by decide⟩]++payload.val := by
    rw [value,←bytes]
    rfl
  apply PV_RunJoin_FourReader73.complete
  all_goals
    rw [read s _ (by change _<s.val.length;rw [view];simp only [List.length_append,List.length_cons,List.length_nil,UScalar.ofNatCore_val_eq];omega)]
    simp only [UScalar.ofNatCore_val_eq,view,List.cons_append,List.getElem_cons_succ,List.getElem_cons_zero]

theorem payload (s body : Slice U8) (t : U8) (w : U32)
    (value : s.val=t::(core.num.U32.to_le_bytes w).val++body.val) :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8)
      s {start:=5#usize}=ok body := by
  have len : (core.num.U32.to_le_bytes w).val.length=4 := by
    simpa only [UScalar.ofNatCore_val_eq] using (core.num.U32.to_le_bytes w).property
  have bound : (5#usize).val ≤ s.length := by
    change 5 ≤ s.val.length
    rw [value,List.length_append,List.length_cons,len]
    omega
  obtain ⟨p,hp,hv⟩ := WP.spec_imp_exists
    (core.slice.index.SliceIndexRangeFromUsizeSlice.index.step_spec
      ({start:=5#usize} : core.ops.range.RangeFrom Usize) s bound)
  have eq : p=body := by
    apply Subtype.ext
    have pv : p.val=s.val.drop 5 := by simpa only [UScalar.ofNatCore_val_eq] using hv.1
    rw [pv,value]
    have five : (t::(core.num.U32.to_le_bytes w).val).length=5 := by
      rw [List.length_cons,len]
    rw [←five,List.drop_left]
  exact hp.trans (congrArg Result.ok eq)

#print axioms read
#print axioms tag
#print axioms word
#print axioms payload
end R1Z.PV_RunJoin_FrameViews73
