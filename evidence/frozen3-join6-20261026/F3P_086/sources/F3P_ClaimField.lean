import F3P_RecordParsed
import F3P_TraceArithmetic
import PSem_Slices
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3P_ClaimField
open Aeneas Aeneas.Std Result
open AspisR1CurrentPreparedClaim

theorem parsed (bytes : Slice U8) (i : Usize) (value : ClaimParser.E)
    (success : ClaimParser.field bytes i=ok value) :
    FoldedLeafCodec.decodeWide (OraclePortCompactDraft.slice (MultiproofConeCanonical.bytesOf bytes.val) (32*i.val) 32)=
      some (Concrete.decode value) := by
  unfold ClaimParser.field at success
  obtain ⟨finished,fieldCall,same⟩ := F3P_ResultBind.success _ _ _ success
  unfold AspisR1CurrentWide.Proof.finishField at fieldCall
  obtain ⟨record,recordCall,finishEq⟩ := F3P_ResultBind.success _ _ _ fieldCall
  obtain ⟨start,next,finish,selected,startEq,nextEq,finishPos,selectedCall,decoded⟩ :=
    AspisR1WeightsFieldCurrent.WeightsFieldSuccess.checked_slice_decode _ bytes i record recordCall
  have numeric := F3P_RecordParsed.parsed selected record decoded
  have startVal := F3P_TraceArithmetic.checked_mul i 32#usize start startEq
  have nextVal := F3P_TraceArithmetic.checked_add i 1#usize next nextEq
  have finishVal := F3P_TraceArithmetic.checked_mul next 32#usize finish finishPos
  have data := PSem_Slices.range_bytes bytes selected start finish selectedCall
  have pos : start.val=32*i.val ∧ finish.val-start.val=32 := by
    change start.val=i.val*32 at startVal
    change next.val=i.val+1 at nextVal
    change finish.val=next.val*32 at finishVal
    omega
  rw [data,pos.1,pos.2] at numeric
  have values : ClaimParser.fromFinish (AspisR1CurrentWide.Proof.recordWideToFinish record)=value :=
    (congrArg ClaimParser.fromFinish (Result.ok.inj finishEq)).trans (Result.ok.inj same)
  rw [values] at numeric
  simpa only [MultiproofConeCanonical.bytesOf,List.map_take,List.map_drop,OraclePortCompactDraft.slice] using numeric

#print axioms parsed
end AspisR1.F3P_ClaimField
end
