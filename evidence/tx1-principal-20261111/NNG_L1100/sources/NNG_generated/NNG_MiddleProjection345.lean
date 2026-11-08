import NNG_FinishProjection345
import NNG_ProjectionBind345
import NNG_MiddleFixed345
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_MiddleProjection345
open RSL NNG_Phases345 NNG_Obs345 NNG_Pure345
open NNG_LogicalProjection345 (V C)

theorem source (s : Decoded V C) (env : Env) :
 NNG_MiddleFixed345.middle (NNG_LogicalProjection345.decoded s) env=NNG_MiddleFixed345.middle s env := by
 unfold NNG_MiddleFixed345.middle stepValidate
 change (if h : C.validateStatement s.statement=true then _ else _) =
  (if h : C.validateStatement s.statement=true then _ else _)
 by_cases valid : C.validateStatement s.statement=true
 · rw [dif_pos valid,dif_pos valid]
   unfold stepEncode
   change (match C.encodeCandidate s.statement with | none=>_ | some candidate=>_) =
    (match C.encodeCandidate s.statement with | none=>_ | some candidate=>_)
   cases C.encodeCandidate s.statement with
   | none=>rfl
   | some candidate=>
    unfold stepProofData
    change tryObs (cloned true (s.proofAccount.bytes.map NNG_Cut345.cut)) _=
     tryObs (cloned true s.proofAccount.bytes) _
    rw [NNG_ProjectionBind345.cloned_map]
    apply congrArg (tryObs (cloned true s.proofAccount.bytes))
    funext proof
    exact NNG_FinishProjection345.source ⟨⟨⟨s,valid⟩,candidate⟩,proof⟩ env
 · rw [dif_neg valid,dif_neg valid]
#print axioms source
end AspisR1.NNG_MiddleProjection345
