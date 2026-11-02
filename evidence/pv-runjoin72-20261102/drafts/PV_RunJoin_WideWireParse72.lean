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
  have d0 := decode x.c0.c0.a
  have d1 := decode x.c0.c0.b
  have d2 := decode x.c0.c1.a
  have d3 := decode x.c0.c1.b
  have d4 := decode x.c1.c0.a
  have d5 := decode x.c1.c0.b
  have d6 := decode x.c1.c1.a
  have d7 := decode x.c1.c1.b
  refine (congrArg ProverRwDictionaryBytesSource.aspis_core.field.wide_exact.WideExact.from_limbs ?_).trans
    (PV_RunJoin_WideLimbsParse72.complete x canonical)
  apply Subtype.ext
  simp only [PV_RunJoin_WideLimbsParse72.limbs,Array.make]
  apply List.ext_getElem
  · rfl
  · intro i hi hi'
    have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 := by
      simp only [List.length_cons,List.length_nil] at hi
      omega
    rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact d0
    · exact d1
    · exact d2
    · exact d3
    · exact d4
    · exact d5
    · exact d6
    · exact d7

#print axioms complete
end R1Z.PV_RunJoin_WideWireParse72
