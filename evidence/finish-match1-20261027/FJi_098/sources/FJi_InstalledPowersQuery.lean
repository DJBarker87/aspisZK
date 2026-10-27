import FJi_InstalledQuery
import FJi_SelectedPowers
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJi_InstalledPowersQuery
open Aeneas Aeneas.Std Result AspisR1Stage2
open Port3_NativeQueryBody
abbrev E := FIp_DotsAdapter.E
/-- The actual installed query call and its SAME actual powers-constructor
return supply the backend value without a canonical-g callback premise. -/
theorem value {C : Type} (err : C) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (r : NP6_StdModel.Reservation) (proof : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator)
    (g : Array E 29#usize) (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
    (answer : core.result.Result (verifier.Accumulator × verifier.BatchedWeights) verifier.Error)
    (canonical : AspisR1LoopPowers.Canonical (Tx2N_Powers.toPowers p.gamma))
    (powers : Tx2N_Powers.powers 29#usize p.gamma=ok g)
    (run : verifier.candidate.query_values (FJi_InstalledQuery.ops err c r) proof p a g none geometry pending=ok answer) :
    FJi_QueryJoin.Meaning (FJi_InstalledQuery.ops err c r) proof a.next g :=
  FJi_InstalledQuery.value err c r proof p a g geometry pending answer
    (FJi_SelectedPowers.value p.gamma g canonical powers).1 run
#print axioms value
end AspisR1.FJi_InstalledPowersQuery
end
