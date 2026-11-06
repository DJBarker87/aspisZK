import NLJ_Continuation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_Observed
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code run)
theorem run_parse {H : Type} (i : Input H) :
 run (PreparedHashCode.bind (step {input:=i,locals:=.parse}) continuation) =
 run (denote {input:=i,locals:=.parse}) := by
 let F : S1SemanticCode.Finish := S1SemanticCode.finish NJM_RoundJoin.R (IDa_Deployed.boundaries i.reservation)
 calc
  _ = run (NLJ_ObservedDirect.verify F i.digest i.publicValue i.bytes i.hash) := by
   change run (PreparedHashCode.bind (PreparedHashCode.bind (show Code _ from liftM (PrefixAdapter.parseAccepted i.bytes)) _) continuation) =
    run (PreparedHashCode.bind (show Code _ from liftM (PrefixAdapter.parseAccepted i.bytes)) _)
   rw [NLJ_Monad.bind_assoc]
   apply NLJ_RunAlgebra.bind_congr
   intro reply
   cases reply <;> rfl
  _ = _ := NLJ_ObservedDirect.source F i.digest i.publicValue i.bytes i.hash
#print axioms run_parse
end AspisR1.NLJ_Observed
end
