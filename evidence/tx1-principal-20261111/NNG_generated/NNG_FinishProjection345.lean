import NNG_CutGuards345
import NNG_StopProjection345
import NNG_FinishAssociation345
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_FinishProjection345
open Aeneas Aeneas.Std RSL NNG_Phases345 NNG_Obs345
open NNG_LogicalProjection345 (V C)

theorem first (s : ProofData V C) (env : Env) (fit : s.proofData.length≤Usize.max) :
 stepFirst V C NNG_Producer328.producer (NNG_LogicalProjection345.proofData s) env=
 stepFirst V C NNG_Producer328.producer s env := by
 unfold stepFirst
 rw [NNG_LogicalProjection345.firstArgs s fit]
 have domain := NNG_Caller345.domain s.publicData s.proofData s.statement
   (s.original.data.getD 1 0).toNat s.decoded s.validated
 change TX1_328.Domain V (firstArgs V C s) at domain
 generalize hc : NNG_Producer328.producer (firstArgs V C s) env=out
 rcases out with ⟨exit,events⟩
 cases exit with
 | abort=>rfl
 | diverge=>rfl
 | ret result=>
  cases result with
  | error e=>rfl
  | ok bytes=>
   have size := NNG_ReturnSize345.producer (firstArgs V C s) env domain bytes events hc
   change Obs.mk (stepReturn (NNG_Cut345.cut s.checkpointData).length bytes).exit
      (events ++ (stepReturn (NNG_Cut345.cut s.checkpointData).length bytes).events)=
    Obs.mk (stepReturn s.checkpointData.length bytes).exit (events ++ (stepReturn s.checkpointData.length bytes).events)
   rw [NNG_CutGuards345.returned s.checkpointData bytes size]
#print axioms first

theorem source (s : ProofData V C) (env : Env) :
 NNG_FinishAssociation345.finish (NNG_LogicalProjection345.proofData s) env=
 NNG_FinishAssociation345.finish s env := by
 unfold NNG_FinishAssociation345.finish stepProofGuard
 rw [NNG_CutGuards345.frame]
 by_cases fit : s.proofData.length≤Usize.max
 · have next := first s env fit
   exact congrArg (fun next=>tryObs (NNG_Pure345.check (proofBad V C s) .invalidAccountData) (fun _=>next)) next
 · have maximum : 58295≤Usize.max := by scalar_tac
   have wrong : s.proofData.length≠58295 := by omega
   have guard : proofBad V C s=true := by
    unfold proofBad
    rw [show (s.proofData.length !=PROOF_ACCOUNT_BYTES)=true from bne_iff_ne.mpr wrong]
    rfl
   rw [guard]
   rw [NNG_StopProjection345.reject,NNG_StopProjection345.reject]
#print axioms source
end AspisR1.NNG_FinishProjection345
