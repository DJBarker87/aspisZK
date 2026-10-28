import RPt_JFn_ArrayBuilder
import Port4C_BasisMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFn_Basis
open Aeneas Aeneas.Std Result

theorem source (seed : Port3_NativeQueryBody.Ops) (node : U32) :
    ∃ basis, Port4C_BasisMeaning.source (JFn_ArrayBuilder.ops seed) node=ok basis ∧
      S7JoinBasisCanonical.Canonical basis ∧
      ∀ i : Fin 64, S7JoinBasisMachine.decode (S7JoinBasisBlock.cell basis i.val)=
        AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode node) i.val :=
  Port4C_BasisMeaning.total _ ⟨rfl,rfl,rfl,rfl,rfl⟩ node

#print axioms source
end AspisR1.JFn_Basis
end
