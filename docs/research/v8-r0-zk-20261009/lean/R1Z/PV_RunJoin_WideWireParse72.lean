import R1Z.PV_RunJoin_ByteWordGroups72
import R1Z.PV_RunJoin_WideLimbsParse72
import R1Z.PV_RunJoin_MergeArray35
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WideWireParse72
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_FlatBytes35 (wire)
abbrev Source := ProverRwDictionaryBytesSource.aspis_core.field.wide_exact.WideExact.from_le_bytes

theorem complete (x : aspis_core.field.wide_exact.WideExact)
    (canonical : PV_RunJoin_WideLimbsParse72.Canonical x) :
    Source (Array.to_slice (wire x))=ok (some x) := by
  have size : Slice.len (Array.to_slice (wire x))=32#usize := by
    apply UScalar.eq_of_val_eq
    exact (wire x).property
  unfold Source ProverRwDictionaryBytesSource.aspis_core.field.wide_exact.WideExact.from_le_bytes
    ProverRwDictionaryBytesSource.aspis_core.field.wide_exact.WideExact.BYTE_LEN
  simp only [size,bne_self_eq_false,Bool.false_eq_true,if_false,PV_RunJoin_MergeArray35.slice_read]
  repeat' (rw [ProverCommitArrayIndex25.array_index_usize_ok _ _ (by decide)];simp only [bind_tc_ok,lift])
  simp only [wire,Array.make,UScalar.ofNatCore_val_eq,List.getElem_cons_zero,
    List.getElem_cons_succ]
  have decode (w : U32) : core.num.U32.from_le_bytes
      (⟨[PV_RunJoin_FlatBytes35.byte w ⟨0,by decide⟩,PV_RunJoin_FlatBytes35.byte w ⟨1,by decide⟩,
        PV_RunJoin_FlatBytes35.byte w ⟨2,by decide⟩,PV_RunJoin_FlatBytes35.byte w ⟨3,by decide⟩],
        by simp only [List.length_cons,List.length_nil,UScalar.ofNatCore_val_eq]⟩ : Array U8 4#usize)=w :=
    PV_RunJoin_ByteWordGroups72.word w
  rw [decode]
  repeat' rw [decode]
  exact PV_RunJoin_WideLimbsParse72.complete x canonical

#print axioms complete
end R1Z.PV_RunJoin_WideWireParse72
