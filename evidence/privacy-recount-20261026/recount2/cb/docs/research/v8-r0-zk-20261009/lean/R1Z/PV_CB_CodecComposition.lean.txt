import R1Z.PV_CB_Composition
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_CodecComposition
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
theorem wide (ops : ExternalFuns) (x : aspis_core.field.wide_exact.WideExact) :
    (PV_CB_Composition.selected ops).op51 x = ProverRwP6FlatSource.wide_bytes_flat x := rfl
theorem parse (ops : ExternalFuns) (s : Slice U8) :
    (PV_CB_Composition.selected ops).op71 s = ProverRwSuccessParser.parse s := rfl
theorem write (ops : ExternalFuns) (x : aspis_core.field.QM31) (s : Slice U8) :
    (PV_CB_Composition.selected ops).op72 x s = ProverRwDictionaryBytes.Src.write x s := rfl
theorem clone (ops : ExternalFuns) {E : Type} (inst : core.clone.Clone E)
    (p : aspis_core.r0.domain.Point E) :
    (PV_CB_Composition.selected ops).op77 inst p = ProverRwSuccessGeneric.pointClone inst p := rfl
theorem clone_fail_first (ops : ExternalFuns) {E : Type} (inst : core.clone.Clone E)
    (p : aspis_core.r0.domain.Point E) (e : Error) (h : inst.clone p.x = .fail e) :
    (PV_CB_Composition.selected ops).op77 inst p = .fail e := by
  rw [clone]
  unfold ProverRwSuccessGeneric.pointClone
  rw [h]
  rfl
#print axioms wide
#print axioms parse
#print axioms write
#print axioms clone
#print axioms clone_fail_first
end R1Z.PV_CB_CodecComposition
