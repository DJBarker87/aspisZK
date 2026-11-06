import NIX_DispatchCut
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
namespace AspisR1.NIX_ProducerInstall

theorem lookup (pre : AspisR1PrefixAggregateParser.r1_wire.Prefix) (row : U8)
 (bound : row.val<27) :
 ∃ record,r1_wire.Prefix.validated_record (PrefixAdapter.fromOld pre) row=ok (.Ok record) ∧
 record.row=row ∧ record.framed=FJb_TailCell.cell pre.records ⟨row.val,bound⟩ := by
 let index : Usize:=UScalar.cast .Usize row
 have value : index.val=row.val := by scalar_tac
 have read : pre.records.index_usize index=ok (FJb_TailCell.cell pre.records ⟨row.val,bound⟩) := by
  simpa only [FJb_TailCell.cell,value] using
   RawPoseidonExternalRowReads.array_index_usize_ok pre.records index (by change index.val<27;omega)
 have notbad : ¬row≥27#u8 := by scalar_tac
 refine ⟨⟨row,FJb_TailCell.cell pre.records ⟨row.val,bound⟩⟩,?_,rfl,rfl⟩
 simp only [r1_wire.Prefix.validated_record,r1_wire.Prefix.record,PrefixAdapter.fromOld,
  notbad,if_false,lift,index,read,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
 rfl

/-- Installs the repaired producer provenance on the SAME actual validated token. -/
theorem framed (bytes : Slice U8) (pre : AspisR1PrefixAggregateParser.r1_wire.Prefix)
 (parsed : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes=ok (.Ok pre))
 (row : U8) (bound : row.val<27) :
 ∃ record,r1_wire.Prefix.validated_record (PrefixAdapter.fromOld pre) row=ok (.Ok record) ∧
 record.row=row ∧ record.framed.val.length=NGX_PrefixGeometry.width row.val := by
 obtain ⟨record,run,tag,frame⟩:=lookup pre row bound
 exact ⟨record,run,tag,by rw [frame];exact NIX_PredecessorFrames.aggregate bytes pre parsed ⟨row.val,bound⟩⟩

#print axioms lookup
#print axioms framed
end AspisR1.NIX_ProducerInstall
