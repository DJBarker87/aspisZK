import R1Z.PV_TraceValueSource
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_TraceValueInstall
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {PV_CurrentDictionary.selected ops with op247 := PV_TraceValueSource.trace.value}

theorem source (ops : ExternalFuns) (tag : U16) (index : Usize)
    (x : aspis_core.field.wide_exact.WideExact) :
    (selected ops).op247 tag index x = ok () := PV_TraceValueSource.exact tag index x

theorem callback_removed (ops : ExternalFuns)
    (callback : U16 → Usize → aspis_core.field.wide_exact.WideExact → Result Unit)
    (tag : U16) (index : Usize) (x : aspis_core.field.wide_exact.WideExact) :
    (selected {ops with op247 := callback}).op247 tag index x =
      (selected ops).op247 tag index x := rfl

theorem clone_preserved (ops : ExternalFuns) (x : ProverRwP7TraceCloneInstall.Trace) :
    (selected ops).op231 x = ok x := by
  change (PV_CurrentDictionary.selected ops).op231 x = ok x
  rw [PV_CurrentDictionary.dictionary_preserved]
  exact PV_ProverRwP7CoefficientsInstall.clone_preserved ops x
#print axioms source
#print axioms callback_removed
#print axioms clone_preserved
end R1Z.PV_TraceValueInstall
