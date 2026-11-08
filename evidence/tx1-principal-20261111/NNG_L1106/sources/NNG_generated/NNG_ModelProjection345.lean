import NNG_PreludeProjection345
import NNG_MiddleProjection345
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ModelProjection345
open RSL NNG_Phases345
open NNG_LogicalProjection345 (V C)

theorem body (s : Parent) (env : Env) :
 bodyRun V C (fun _=>true) NNG_Producer328.producer (NNG_LogicalProjection345.parent s) env=
 bodyRun V C (fun _=>true) NNG_Producer328.producer s env := by
 change NNG_PreludeAssociation345.canonical (NNG_LogicalProjection345.parent s) (fun d=>NNG_MiddleFixed345.middle d env)=
  NNG_PreludeAssociation345.canonical s (fun d=>NNG_MiddleFixed345.middle d env)
 exact NNG_PreludeProjection345.source s (fun d=>NNG_MiddleFixed345.middle d env)
  (fun d=>NNG_MiddleProjection345.source d env)
#print axioms body

theorem source (a : TX1_345.Args) (env : Env) :
 NNG_Model345.interpretation (NNG_ProjectAccounts345.args a) env=NNG_Model345.interpretation a env := by
 unfold NNG_Model345.interpretation NNG_Phases345.run
 rw [NNG_ProjectAccounts345.badRoute]
 by_cases bad : TX1_345.badRoute a=true
 · rw [if_pos bad,if_pos bad]
 · rw [if_neg bad,if_neg bad]
   cases ha : a.accounts with
   | nil=>rfl
   | cons p rest=>
    cases rest with
    | nil=>rfl
    | cons pub rest=>
     cases rest with
     | nil=>rfl
     | cons ck rest=>
      cases rest with
      | nil=>exact body ⟨a,p,pub,ck⟩ env
      | cons fourth rest=>rfl
#print axioms source
end AspisR1.NNG_ModelProjection345
