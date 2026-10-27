import RPz7_F3P_ClaimField
import SAG_DotDecode
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAG_FieldRead
open Aeneas Aeneas.Std Result
open AspisR1CurrentPreparedClaim

theorem from_finish (bytes : Slice U8) (i : Usize)
    (value : AspisR1CurrentWide.Proof.FinishE)
    (success : AspisR1CurrentWide.Proof.finishField bytes i = ok value) :
    FoldedLeafCodec.decodeWide (OraclePortCompactDraft.slice
      (MultiproofConeCanonical.bytesOf bytes.val) (32*i.val) 32) =
      some (AspisR1CurrentWide.Proof.decodeFinish value) := by
  have run : ClaimParser.field bytes i = ok (ClaimParser.fromFinish value) := by
    simp only [ClaimParser.field,success,bind_tc_ok]
  have parsed := F3P_ClaimField.parsed bytes i (ClaimParser.fromFinish value) run
  exact parsed

#print axioms from_finish
end AspisR1.SAG_FieldRead
end
