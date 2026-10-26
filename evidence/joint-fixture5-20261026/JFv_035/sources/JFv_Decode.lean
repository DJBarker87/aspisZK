import JFv_Checked
import JFv_DecodeLoop
set_option autoImplicit false
namespace AspisR1.JFv_Decode
open Aeneas Aeneas.Std Result WP
open AspisR1DecodeKFullV10
open MultiproofConeCanonical OraclePortCompactDraft

theorem success (N : Usize) (self : r1_wire.ValidatedRecord) (offset : Usize)
    (row : 14 ≤ self.row.val)
    (bound : 5+32*(offset.val+N.val) ≤ self.framed.length)
    (small : self.framed.length ≤ 20000)
    (canon : canonical (bytesOf (self.framed.val.drop 5))) :
    ∃ out,r1_wire.ValidatedRecord.decode_k N self offset=ok (.Ok out) := by
  change 5+32*(offset.val+N.val) ≤ self.framed.val.length at bound
  change self.framed.val.length ≤ 20000 at small
  obtain ⟨byte,mul,byteVal⟩ := JFv_Checked.multiply offset 32#usize (by scalar_tac)
  obtain ⟨width,mulN,widthVal⟩ := JFv_Checked.multiply N 32#usize (by scalar_tac)
  obtain ⟨stop,add,stopVal⟩ := JFv_Checked.add byte width (by scalar_tac)
  obtain ⟨out,loop⟩ := JFv_DecodeLoop.success N.val self self.row offset byte
    {start:=0#usize,«end»:=N} (Array.repeat N aspis_core.field.QM31.ZERO) rfl (by simp) (by
      intro value active
      apply JFv_Value.success
      · simp only [show (32#usize).val=32 from rfl] at byteVal
        change 5+byte.val+32*value.val+16 ≤ self.framed.val.length
        omega
      · exact small
      · simp only [show (32#usize).val=32 from rfl] at byteVal
        omega
      · scalar_tac
      · exact canon)
  have total : r1_wire.ValidatedRecord.decode_k N self offset ⦃ result => result=.Ok out ⦄ := by
    unfold r1_wire.ValidatedRecord.decode_k
    simp only [if_neg (by change ¬ self.row.val<14;omega),mul,mulN,add,lift,bind_tc_ok,
      core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch]
    step*
    have fits : byte ≤ stop ∧ stop.val ≤ s.length := by
      simp only [Slice.length,s_post,List.length_drop]
      scalar_tac
    simp only [core.slice.Slice.get,core.slice.index.SliceIndexRangeUsizeSlice,core.slice.index.SliceIndexRangeUsizeSlice.get,
      if_pos fits,bind_tc_ok,core.option.Option.ok_or,
      core.result.Result.Insts.CoreOpsTry.branch,loop]
    rfl
  obtain ⟨result,call,same⟩ := WP.spec_imp_exists total
  exact ⟨out,by rw [same] at call;exact call⟩

#print axioms success
end AspisR1.JFv_Decode
