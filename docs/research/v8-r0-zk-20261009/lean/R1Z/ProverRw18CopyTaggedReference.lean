import R1Z.ProverRw18CopyReference
import R1Z.ProverRw18CopyTags
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18CopyTaggedReference
open Aeneas Aeneas.Std Result ProverRw18FieldMeaning

theorem closed (link : R0P.CopyLink) (member : link ∈ R0P.copyLinks)
    (values : Fin 16 → U32) (lambda : Raw) (hlambda : Canonical lambda) :
    PV_RW_CompressClosed.owned (ProverRw18CopyTags.word link member)
      (ProverRw18CopyReference.input values) (full lambda)=
        ok (full (ProverRw18FieldEncode.encode
          ((R0P.compressPoly ((link.tag : K),fun i => ((values i).val : K))).eval (decode lambda)))) := by
  rw [ProverRw18CopyReference.closed _ values lambda
    (ProverRw18CopyTags.word_canonical link member) hlambda]
  rfl

variable [ProverRwFull.ExternalTypes]

theorem context (ops : ProverRwFull.ExternalFuns) (link : R0P.CopyLink)
    (member : link ∈ R0P.copyLinks) (values : Fin 16 → U32)
    (lambda : Raw) (hlambda : Canonical lambda) :
    @ProverRw18ContextCompression.compress _ (PV_CurrentScaleInstall.selected ops)
      (ProverRw18CopyTags.word link member) (ProverRw18CopyReference.input values) (full lambda)=
        ok (full (ProverRw18FieldEncode.encode
          ((R0P.compressPoly ((link.tag : K),fun i => ((values i).val : K))).eval (decode lambda)))) := by
  rw [ProverRw18ContextCompression.owned]
  exact closed link member values lambda hlambda

#print axioms closed
#print axioms context
end R1Z.ProverRw18CopyTaggedReference
