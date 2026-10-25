import Port4B_CallerViews
import MultiproofConeByteEquality

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4B_Opening
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames
open MultiproofConeCanonical MultiproofConeSlices OraclePortSelectedDraft

/-- The source opening expression, including its release wrapping arithmetic
and checked physical range. -/
def opening (proof : Slice U8) (i : Usize) : Result (Slice U8) := do
  let offset ← lift (Usize.wrapping_mul i 832#usize)
  let start ← lift (Usize.wrapping_add 10055#usize offset)
  let finish ← lift (Usize.wrapping_add start 832#usize)
  core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    proof {start:=start,«end»:=finish}

theorem opening_exact (proof : Slice U8) (len : proof.val.length=57607)
    (i : Usize) (bound : i.val<22) :
    ∃ view, opening proof i=ok view ∧ view.val.length=832 ∧
      bytesOf view.val=OraclePortCompactDraft.slice (bytesOf proof.val) (10055+i.val*832) 832 := by
  let offset := Usize.wrapping_mul i 832#usize
  let start := Usize.wrapping_add 10055#usize offset
  let finish := Usize.wrapping_add start 832#usize
  have capacity : 57607 < UScalar.size .Usize := by rw [UScalar.size_def]; scalar_tac
  have ov : offset.val=i.val*832 := by
    change (Usize.wrapping_mul i 832#usize).val=i.val*832
    rw [Usize.wrapping_mul_val_eq]
    apply Nat.mod_eq_of_lt
    change i.val*832 < UScalar.size .Usize
    omega
  have sv : start.val=10055+i.val*832 := by
    change (Usize.wrapping_add 10055#usize offset).val=_
    rw [Usize.wrapping_add_val_eq]
    apply (Nat.mod_eq_of_lt (show (10055#usize).val+offset.val<UScalar.size .Usize by rw [ov]; change 10055+i.val*832<_ ; omega)).trans
    rw [ov]; rfl
  have fv : finish.val=start.val+832 := by
    change (Usize.wrapping_add start 832#usize).val=_
    rw [Usize.wrapping_add_val_eq]
    apply Nat.mod_eq_of_lt
    change start.val+832 < UScalar.size .Usize
    omega
  have order : start.val≤finish.val := by omega
  have fit : finish.val≤proof.val.length := by omega
  refine ⟨sub proof start finish,range_total proof start finish order fit,?_,?_⟩
  · rw [sub_length proof start finish order fit];omega
  · rw [bytes_sub,sv,fv,sv,Nat.add_sub_cancel_left]

/-- The native opening selected after packed-key rebasing is precisely the
P6 opening. No independent view or digest return is assumed. -/
theorem selected (proof : Slice U8) (len : proof.val.length=57607)
    (parsed : OraclePortCompactDraft.Parsed) (wire : parsed.wire=bytesOf proof.val)
    (q : Fin 22 → Fin 262144) (batch kind pos : Nat)
    (mem : pos∈OraclePortFrozenOrder.sortedPositions q batch kind)
    (i : Usize)
    (rebased : i.val=(if batch=0 then 0 else 10)+
      (MultiproofConeSortOrder.packed q batch kind pos).val%256) :
    ∃ view, opening proof i=ok view ∧ view.val.length=832 ∧
      bytesOf view.val=OraclePortSelectedDraft.opening parsed pos := by
  have member := MultiproofConeKeyAdapters.sorted_member q batch kind pos mem
  have ib := MultiproofConeKeyAdapters.position_bounds batch pos member
  have same : i.val=pos := rebased.trans (MultiproofConeKeyAdapters.packed_opening q batch kind pos member)
  obtain ⟨view,read,len,bytes⟩ := opening_exact proof len i (by omega)
  exact ⟨view,read,len,by simpa only [same,←wire,OraclePortSelectedDraft.opening] using bytes⟩

#print axioms opening_exact
#print axioms selected
end AspisR1.Port4B_Opening
end
