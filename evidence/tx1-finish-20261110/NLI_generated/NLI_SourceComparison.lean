import NLI_Suffix_rounds
import NLI_LiftLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Source
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
/-- Source continuation comparison only. Child calls stay opaque; equations
for repeated pure getters are produced internally by congr_lift. -/
theorem suffix_eq_finish {H : Type} (i : Input H) :
 run (suffix_rounds i) = run (S1SemanticCode.finish NJM_RoundJoin.R
 (IDa_Deployed.boundaries i.reservation) i.digest i.publicValue i.prefix1
 i.transcript i.challenges none) := by
 rw [NKA_FinishTrace.source]
 unfold suffix_rounds
 apply NLI_Notation.congr_bind
 intro r
 cases r with
 | Err error => rfl
 | Ok value =>
  rcases value with ⟨running,alpha,transcript⟩
  unfold NKA_FinishTrace.afterRounds
  unfold suffix_mark2
  simp only [VerifyPrefix.mark,NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
  unfold suffix_claims
  try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok,core.result.Result.Insts.CoreOpsTry.branch]
  apply NLI_LiftLaws.congr_lift
  intro r h_claims
  cases r with
  | Err error => rfl
  | Ok claims =>
   unfold suffix_original
   unfold suffix_terminal
   try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok,core.result.Result.Insts.CoreOpsTry.branch]
   apply NLI_LiftLaws.congr_lift
   intro terminalReply h_terminalReply
   unfold suffix_mapPublic
   try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok,core.result.Result.Insts.CoreOpsTry.branch]
   apply NLI_LiftLaws.congr_lift
   intro r h_terminal
   cases r with
   | Err error => rfl
   | Ok terminal =>
    unfold suffix_mark3
    simp only [VerifyPrefix.mark,NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
    unfold suffix_lowArray
    try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok,core.result.Result.Insts.CoreOpsTry.branch]
    apply NLI_LiftLaws.congr_lift
    intro low h_low
    unfold suffix_highArray
    try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok,core.result.Result.Insts.CoreOpsTry.branch]
    apply NLI_LiftLaws.congr_lift
    intro high h_high
    unfold suffix_blind
    try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok,core.result.Result.Insts.CoreOpsTry.branch]
    apply NLI_LiftLaws.congr_lift
    intro row h_row
    apply NLI_LiftLaws.congr_lift
    intro blind h_blind
    unfold suffix_alpha
    unfold suffix_mask
    try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok,core.result.Result.Insts.CoreOpsTry.branch]
    apply NLI_LiftLaws.congr_lift
    intro mask h_mask
    unfold suffix_record25a
    try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok,core.result.Result.Insts.CoreOpsTry.branch]
    apply NLI_LiftLaws.congr_lift
    intro r h25
    cases r with
    | Err error => rfl
    | Ok record25 =>
     unfold suffix_decode25
     try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok,core.result.Result.Insts.CoreOpsTry.branch]
     apply NLI_LiftLaws.congr_lift
     intro r h_extra
     cases r with
     | Err error => rfl
     | Ok extra =>
      unfold suffix_multiply
      try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok,core.result.Result.Insts.CoreOpsTry.branch]
      apply NLI_LiftLaws.congr_lift
      intro product h_product
      unfold suffix_addMask
      try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok,core.result.Result.Insts.CoreOpsTry.branch]
      apply NLI_LiftLaws.congr_lift
      intro partialValue h_partialValue
      unfold suffix_extra28
      try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok,core.result.Result.Insts.CoreOpsTry.branch]
      apply NLI_LiftLaws.congr_lift
      intro extraCell h_extraCell
      unfold suffix_addExtra
      try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok,core.result.Result.Insts.CoreOpsTry.branch]
      apply NLI_LiftLaws.congr_lift
      intro masked h_masked
      unfold suffix_terminalGuard
      try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok,core.result.Result.Insts.CoreOpsTry.branch]
      apply NLI_LiftLaws.congr_lift
      intro reject h_reject
      cases reject with
      | true => rfl
      | false =>
       unfold suffix_mark4
       simp only [VerifyPrefix.mark,NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
       unfold suffix_stateBefore
       try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok,core.result.Result.Insts.CoreOpsTry.branch]
       apply NLI_LiftLaws.congr_lift
       intro stateBefore h_stateBefore
       unfold suffix_record25b
       simp only [h25,NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
       unfold suffix_circle0
       try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok,core.result.Result.Insts.CoreOpsTry.branch]
       apply NLI_Notation.congr_bind (S1SemanticCode.circleValidated (IDa_Deployed.boundaries i.reservation) i.digest transcript record25)
       rintro ⟨r,transcript1⟩
       cases r with
       | Err error => rfl
       | Ok z0 =>
        unfold suffix_record26a
        try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok,core.result.Result.Insts.CoreOpsTry.branch]
        apply NLI_LiftLaws.congr_lift
        intro r h26
        cases r with
        | Err error => rfl
        | Ok record26 =>
         unfold suffix_decode26
         try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok,core.result.Result.Insts.CoreOpsTry.branch]
         apply NLI_LiftLaws.congr_lift
         intro r h_beforeZ1
         cases r with
         | Err error => rfl
         | Ok beforeZ1 =>
          unfold suffix_record26b
          simp only [h26,NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
          unfold suffix_circle1
          try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok,core.result.Result.Insts.CoreOpsTry.branch]
          apply NLI_Notation.congr_bind (S1SemanticCode.circleValidated (IDa_Deployed.boundaries i.reservation) i.digest transcript1 record26)
          rintro ⟨r,transcript2⟩
          cases r with
          | Err error => rfl
          | Ok z1 =>
           unfold suffix_mark5
           simp only [VerifyPrefix.mark,NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
           unfold suffix_circleGuard
           try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok,core.result.Result.Insts.CoreOpsTry.branch]
           apply NLI_LiftLaws.congr_lift
           intro reject1 h_reject1
           cases reject1 with
           | true => rfl
           | false =>
            unfold suffix_payload2
            try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok,core.result.Result.Insts.CoreOpsTry.branch]
            apply NLI_LiftLaws.congr_lift
            intro r h_payload
            cases r with
            | Err error => rfl
            | Ok payload =>
             unfold suffix_rootCopy
             try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok,core.result.Result.Insts.CoreOpsTry.branch]
             apply NLI_LiftLaws.congr_lift
             intro rootResult h_rootResult
             apply NLI_LiftLaws.congr_lift
             intro root h_root
             unfold tailVerified
             rfl
#print axioms suffix_eq_finish
#print suffix_eq_finish
end AspisR1.NLI_Source
end
