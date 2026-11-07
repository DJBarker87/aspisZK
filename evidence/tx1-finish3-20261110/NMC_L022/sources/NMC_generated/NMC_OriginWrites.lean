import NMC_Origins
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMC_Origins
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
theorem claims_written {H : Type} (s after : NLC_Finish.State H)
 (atSite : s.next=.claims)
 (head : (PreparedHashCode.run (NLC_Finish.step s)).2=ok (.inr after)) : ClaimsOrigin after := by
 have actual : PreparedHashCode.erase (NLC_Finish.step s)=ok (.inr after) := by
  rw [←PreparedHashCode.run_value];exact head
 simp only [NLC_Finish.step,atSite] at actual
 change (do let result ← (IDa_Deployed.boundaries s.input.reservation).claims s.input.prefix1
            ok (NLC_Finish.returned s .original result (fun value=>{s.locals with claims:=some value})))=ok (.inr after) at actual
 cases child : (IDa_Deployed.boundaries s.input.reservation).claims s.input.prefix1 with
 | fail error=>rw [child] at actual;cases actual
 | div=>rw [child] at actual;cases actual
 | ok result=>
   cases result with
   | Err error=>simp only [child,bind_tc_ok,NLC_Finish.returned] at actual;cases actual
   | Ok value=>
     simp only [child,bind_tc_ok,NLC_Finish.returned] at actual
     have chosen:=Sum.inr.inj (Result.ok.inj actual)
     cases chosen
     intro claims stored
     have same : value=claims := Option.some.inj stored
     cases same
     exact child
theorem alpha_written {H : Type} (s after : NLC_Finish.State H)
 (atSite : s.next=.rounds)
 (head : (PreparedHashCode.run (NLC_Finish.step s)).2=ok (.inr after)) : AlphaOrigin after := by
 have actual : PreparedHashCode.erase (NLC_Finish.step s)=ok (.inr after) := by
  rw [←PreparedHashCode.run_value];exact head
 simp only [NLC_Finish.step,atSite] at actual
 rw [NMC_Code.erase_bind] at actual
 change (do let result ← PreparedHashCode.erase (S1SemanticCode.rounds NJM_RoundJoin.R s.input.digest s.input.prefix1 s.input.transcript)
            ok (NLC_Finish.returned s .mark2 result (fun value=>{s.locals with running:=some value.1,alpha:=some value.2.1,transcript:=some value.2.2})))=ok (.inr after) at actual
 cases child : PreparedHashCode.erase (S1SemanticCode.rounds NJM_RoundJoin.R s.input.digest s.input.prefix1 s.input.transcript) with
 | fail error=>rw [child] at actual;cases actual
 | div=>rw [child] at actual;cases actual
 | ok result=>
   cases result with
   | Err error=>simp only [child,bind_tc_ok,NLC_Finish.returned] at actual;cases actual
   | Ok value=>
     simp only [child,bind_tc_ok,NLC_Finish.returned] at actual
     have chosen:=Sum.inr.inj (Result.ok.inj actual)
     cases chosen
     intro alpha stored
     have same : value.2.1=alpha := Option.some.inj stored
     cases same
     exact ⟨value.1,value.2.2,child⟩
#print axioms claims_written
#print axioms alpha_written
end AspisR1.NMC_Origins
end
