import LIBB_ReturnRun
import LIBB_ObservationValues
import LIBB_ReturnFunctional
set_option autoImplicit false
noncomputable section
namespace LIBB_ReturnObservation
open Aeneas Aeneas.Std AspisR1 NJU_CommonObserved

theorem pieces (env : RSL.Env) (source : List Event) (events : List RSL.Event)
 (safe : ∀ pr p folded err, Event.merkle pr p folded (.fail err) ∉ source)
 (law : LIBB_ObservationPieces.Pieces env source events) :
 events=source.flatMap (LIBB_Tx2EnvTrace.event env) := by
 obtain ⟨parts,related,rfl⟩:=law
 induction related with
 | nil => rfl
 | @cons e part es parts head tail ih =>
  have equal : part=LIBB_Tx2EnvTrace.event env e := by
   rcases head with equal | ⟨pr,p,folded,err,rfl,_⟩
   · exact equal
   · exact False.elim (safe pr p folded err List.mem_cons_self)
  have rest := ih (fun pr p folded err member=>safe pr p folded err (List.mem_cons_of_mem _ member))
  simp only [List.flatten_cons,List.flatMap_cons,equal,rest]

theorem common (env : RSL.Env) (pub proof ck : Slice U8)
 (o : RSL.Obs (Except LIBB_V2Carriers.VErr Unit)) (r : Except LIBB_V2Carriers.VErr Unit)
 (law : LIBB_ObservationModel.Common env pub proof ck o) (returned : o.exit=.ret r) :
 o=LIB_Carriers.resultObs LIBB_ObservationModel.convert (LIBB_Tx2EnvTrace.common env pub proof ck)
  (LIBB_Tx2EnvCode.common env pub proof ck) := by
 rcases law with ⟨exit,events⟩ | ⟨before,pr,p,folded,reply,suffix,prior,inside,_,_,_,rfl⟩
 · have returnedResult := exit.symm.trans returned
   have safe : ∀ pr p folded err, Event.merkle pr p folded (.fail err) ∉
    (LIBB_Tx2EnvCode.observed env pub proof ck).events := by
    cases h : LIBB_Tx2EnvCode.common env pub proof ck with
    | fail e => rw [h] at returnedResult; cases returnedResult
    | div => rw [h] at returnedResult; cases returnedResult
    | ok v =>
     exact LIBB_ReturnRun.run _ _ _ _ _ pub proof ck () v
      ((LIBB_Tx2EnvCode.source_result env pub proof ck).trans h)
   have eventsEqual:=pieces env _ _ safe events
   cases o with
   | mk out ev =>
    change out=_ at exit
    change ev=_ at eventsEqual
    have ex := exit.trans (LIBB_ObservationModel.result_exit (LIBB_Tx2EnvCode.common env pub proof ck) (LIBB_Tx2EnvTrace.common env pub proof ck)).symm
    have evEqual := eventsEqual.trans (LIBB_ObservationModel.result_events (LIBB_Tx2EnvCode.common env pub proof ck) (LIBB_Tx2EnvTrace.common env pub proof ck)).symm
    cases target : LIB_Carriers.resultObs LIBB_ObservationModel.convert (LIBB_Tx2EnvTrace.common env pub proof ck) (LIBB_Tx2EnvCode.common env pub proof ck) with
    | mk out₂ ev₂ =>
     rw [target] at ex evEqual
     cases ex
     cases evEqual
     rfl
 · cases returned

theorem resolved (env : RSL.Env) (pub proof ck : Slice U8)
 (o : RSL.Obs (Except LIBB_V2Carriers.VErr Unit)) (r : Except LIBB_V2Carriers.VErr Unit)
 (law : LIBB_ObservationModel.law pub proof ck env o) (returned : o.exit=.ret r) :
 o=LIBB_Tx2EnvTrace.observation env pub proof ck := by
 unfold LIBB_ObservationModel.law at law
 cases parsed : NLE_ParseInstall.parse proof with
 | fail e => rw [parsed] at law; exact law
 | div => rw [parsed] at law; exact law
 | ok v => cases v with
   | Err e => rw [parsed] at law; exact law
   | Ok v =>
    rw [parsed] at law
    rw [LIBB_ObservationModel.parsed_observation env pub proof ck v parsed]
    exact common env pub proof ck o r law returned

theorem functional (pub proof ck : Slice U8) :
 LIBB_ReturnFunctional.ReturnFunctional (LIBB_ObservationModel.law pub proof ck) := by
 intro env o₁ o₂ r₁ r₂ h₁ h₂ ret₁ ret₂
 exact (resolved env pub proof ck o₁ r₁ h₁ ret₁).trans
  (resolved env pub proof ck o₂ r₂ h₂ ret₂).symm
#print axioms pieces
#print axioms common
#print axioms resolved
#print axioms functional
end LIBB_ReturnObservation
end
