import NIW_AlignFinalCollect
import NIW_AlignPowersReply
import NIT_TailPhases
import NIT_PairControl
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignFinalPhase
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl

structure Log where
 powers : Result Parts
 steps : Option (List NIW_AlignFinalCollect.Event)

def run (parts : Parts) (kappa : E) : Result NR × Log :=
 let powers := FIo_Native.weights.powers 7#usize kappa
 match powers with
 | fail err => (fail err,⟨powers,none⟩)
 | div => (div,⟨powers,none⟩)
 | ok values =>
  let observed := NIW_AlignFinalCollect.collect parts values 8
   ({start:=0#usize,«end»:=7#usize},NHI_Scalar.zero)
  ((do let sum←observed.1;ok (.Ok sum)),⟨powers,some observed.2⟩)

/-- The NIT Final witness is built at the actual observed powers and final-loop
Result. No locally selected powers, sum or packet result is substituted. -/
theorem trace (parts : Parts) (kappa : E) (cp : canonical parts) (ck : canonE kappa) :
 NIT_TailPhases.Final parts kappa (run parts kappa).1 := by
 have powers := NIW_AlignPowersReply.source 7#usize kappa ck
 cases call : FIo_Native.weights.powers 7#usize kappa with
 | fail err => simp only [call,NIW_AlignFieldReply.Produced] at powers
 | div => simp only [call,NIW_AlignFieldReply.Produced] at powers
 | ok values =>
  simp only [call,NIW_AlignFieldReply.Produced] at powers
  have final := NIW_AlignFinalCollect.trace parts values cp powers 8
   ({start:=0#usize,«end»:=7#usize},NHI_Scalar.zero) rfl (by change (0:Nat)≤7;omega)
   NHI_Scalar.zero_canonical (by change (7:Nat)-0<8;omega)
  cases result : (NIW_AlignFinalCollect.collect parts values 8
   ({start:=0#usize,«end»:=7#usize},NHI_Scalar.zero)).1 with
  | fail err => simp only [result,NIW_AlignFieldReply.Produced] at final
  | div => simp only [result,NIW_AlignFieldReply.Produced] at final
  | ok sum =>
   simp only [result,NIW_AlignFieldReply.Produced] at final
   simp only [run,call,result,bind_tc_ok]
   exact .returned values sum (.Ok sum) call final.1 ⟨final.2,rfl⟩

theorem source (parts : Parts) (kappa : E) (cp : canonical parts) (ck : canonE kappa) :
 NIT_TailPhases.final parts kappa=(run parts kappa).1 :=
 NIT_TailPhases.final_interpreted parts kappa _ (trace parts kappa cp ck)

#print axioms trace
#print axioms source
end AspisR1.NIW_AlignFinalPhase
