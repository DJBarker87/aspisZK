import NLR_PrepareExact
import NLR_PrepareTailSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLR_Prepare
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisR1PublicPreparation.PreparedHashCode (run)
/-- Eliminates the predecessor's UNPROVED source-body equation. There is no
native parent or child-domain admission in this theorem. -/
theorem source (cfg : NLJ_Prepare.Configuration) {H : Type}
 (i : NLJ_Prepare.Input H) : NLJ_Prepare.SourceEquality cfg i := by
 exact (exact_source cfg 12 (NLJ_Prepare.initial i) (by decide)).trans
  (NLR_PrepareTails.tail_source cfg i)
#print axioms source
set_option pp.proofs false
#print source
end AspisR1.NLR_Prepare
end
