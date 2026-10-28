import NDO_JHn_R_JHe_WriterCommutation
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_PrepareWriterFields
open Aeneas Aeneas.Std Result AspisR1CurrentCaller

theorem logical (ops : Ops) (w : JHe_WriterCommutation.Writer) :
    compact.LOGICAL_SEMANTIC {ops with op16:=w}=compact.LOGICAL_SEMANTIC ops := by
  unfold compact.LOGICAL_SEMANTIC
  rfl
#print axioms logical

theorem semantic (ops : Ops) (w : JHe_WriterCommutation.Writer) :
    compact.OFF_SEMANTIC {ops with op16:=w}=compact.OFF_SEMANTIC ops := by
  unfold compact.OFF_SEMANTIC
  rfl
#print axioms semantic

theorem y1 (ops : Ops) (w : JHe_WriterCommutation.Writer) :
    compact.OFF_Y1 {ops with op16:=w}=compact.OFF_Y1 ops := by
  unfold compact.OFF_Y1
  rw [semantic]
#print axioms y1

theorem inactive (ops : Ops) (w : JHe_WriterCommutation.Writer) :
    compact.OFF_INACTIVE {ops with op16:=w}=compact.OFF_INACTIVE ops := by
  unfold compact.OFF_INACTIVE
  rw [y1]
#print axioms inactive

theorem codec (ops : Ops) (w : JHe_WriterCommutation.Writer) :
    verifier.Error.Insts.CoreConvertFromCodecError {ops with op16:=w}=
      verifier.Error.Insts.CoreConvertFromCodecError ops := by
  unfold verifier.Error.Insts.CoreConvertFromCodecError
  rfl
#print axioms codec
end AspisR1.JHe_PrepareWriterFields
end
