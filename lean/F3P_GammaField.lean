import F3P_ClaimField
import F3P_LowProjection
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3P_GammaField
open Aeneas Aeneas.Std Result AspisR1CurrentPreparedClaim

theorem cell (bytes : Slice U8) (values : OpeningRecordCodec.Payload .gamma)
    (decoded : OpeningRecordCodec.decode .gamma
      (LengthFrameCodec.frame (MultiproofConeCanonical.bytesOf bytes.val))=some values)
    (l : Usize) (hl : l.val<29) (parsed : ClaimParser.E)
    (source : ClaimParser.field bytes l=ok parsed) :
    LiteralOpeningView.eK (F3L_RhoMeaning.decode (AspisR1ClaimPreparedBridge.fromClaimQ parsed.c0))=
      (values ⟨l.val,hl⟩).val := by
  have model := F3P_GammaCell.decoded _ values decoded ⟨l.val,hl⟩
  have actual := F3P_ClaimField.parsed bytes l parsed source
  change FoldedLeafCodec.decodeWide (((MultiproofConeCanonical.bytesOf bytes.val).drop (32*l.val)).take 32)=
    some (Concrete.decode parsed) at actual
  unfold SemanticCoefficientCodec.decodeLow at model
  rw [actual] at model
  simp only [Option.bind_some] at model
  split at model
  · have same : Concrete.decode parsed=(values ⟨l.val,hl⟩).val := congrArg Subtype.val (Option.some.inj model)
    rw [F3P_LowProjection.lower]
    apply QuadraticAlgebra.ext
    · change (Concrete.decode parsed).re=(values ⟨l.val,hl⟩).val.re
      exact congrArg (fun x : AspisWideTower.WideExact=>x.re) same
    · exact (values ⟨l.val,hl⟩).property.symm
  · cases model

#print axioms cell
end AspisR1.F3P_GammaField
end
