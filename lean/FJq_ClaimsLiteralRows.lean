import FJq_ReferenceMain
import FJq_CircleArray
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJq_ClaimsLiteralRows
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open FIz_ConcretePack (embed)
/-- Actual installed Claims decoder VALUE on the SAME decoded literal row25.
The reference return supplies all 87 source slots; no per-slot value premise. -/
theorem value (std : ClaimsUnrolledFinish.StdCalls) (pre : r1_wire.Prefix)
    (claims : ClaimsUnrolledFinish.MainClaims)
    (run : ClaimsUnrolledFinish.reference std pre=ok (.Ok claims))
    (record : r1_wire.ValidatedRecord)
    (read : r1_wire.Prefix.validated_record pre 25#u8=ok (.Ok record))
    (payload : CircleRecordCodec.Payload 0)
    (parsed : CircleRecordCodec.decode 0 (record.framed.val.map ExtractedRecordByteValue.rawByte)=some payload) :
    ∀ (j : Fin 3) (l : Fin 29),embed (FJn_MainClaims.claims claims j l)=
      (CircleRecordCodec.pointClaims payload j l).val := by
  obtain ⟨actual,a,b,c,readActual,da,db,dc,shape⟩:=FJq_ReferenceMain.reached std pre claims run
  have same:=core.result.Result.Ok.inj (Result.ok.inj (read.symm.trans readActual))
  subst actual
  subst claims
  intro j l
  fin_cases j
  · exact FJq_CircleArray.value 0 record payload parsed 29#usize 0#usize a da (by decide) l
  · exact FJq_CircleArray.value 0 record payload parsed 29#usize 29#usize b db (by decide) l
  · exact FJq_CircleArray.value 0 record payload parsed 29#usize 58#usize c dc (by decide) l
#print axioms value
end AspisR1.FJq_ClaimsLiteralRows
end
