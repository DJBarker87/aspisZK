import R1Z.PV_RunJoin_WeightMaterialLoop47
import R1Z.PV_RunJoin_WeightPowersSeven47
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightMaterialResult47
open Aeneas Aeneas.Std Result PV_RunJoin_WeightCarrier46
open PV_RunJoin_WeightWide46 (E toWide)
open PV_B2_F_ConstructorCarrier (amap)
open PV_RunJoin_WeightMap46 (mapResult)
abbrev Outcome := PV_B2_F_AllocationTransport.Outcome
abbrev MOut := Array AspisR1ProducerRelease47.field.wide_exact.WideExact 1024#usize
abbrev MResult := core.result.Result MOut PV_B2_251c1.verifier.Error

def mapRust : PV_B2_F_AllocationTransport.RustResult → MResult
  | .Ok out => .Ok (amap toWide out)
  | .Err e => .Err e

def run (request : Result Outcome) (w : W) (x : E) : Result MResult := do
  let event ← request
  match event with
  | .denied => ok (.Err PV_B2_251c1.verifier.Error.Allocation)
  | .supplied => do
    let out ← ProverCommitWeightsMaterialBinding53.run (state w) (toWide x)
    ok (.Ok out)

theorem wrap (r : Result PV_B2_C_MutationStep.Out) :
    mapResult mapRust (do let out ← r;ok (.Ok out))=
      (do let out ← mapResult (amap toWide) r;ok (.Ok out)) := by
  cases r <;> rfl
#print axioms wrap

theorem original (request : Result Outcome) (w : W) (hs : w.variant=.S2) (x : E) :
    mapResult mapRust (PV_B2_F_MaterializeRequest.original request w x)=run request w x := by
  obtain ⟨k,hk,hm⟩ := PV_RunJoin_WeightPowersSeven47.complete x
  cases request with
  | fail e => simp only [PV_B2_F_MaterializeRequest.original,hk,bind_tc_ok,bind_tc_fail,run];rfl
  | div => simp only [PV_B2_F_MaterializeRequest.original,hk,bind_tc_ok,bind_tc_div,run];rfl
  | ok event =>
    cases event with
    | denied => simp only [PV_B2_F_MaterializeRequest.original,hk,bind_tc_ok,run];rfl
    | supplied =>
      simp only [PV_B2_F_MaterializeRequest.original,hk,bind_tc_ok,run,
        ProverCommitWeightsMaterialBinding53.run,hm]
      rw [PV_RunJoin_WeightMaterialLoop47.original w hs k]
      exact wrap _
#print axioms original

theorem copied (request : Result Outcome) (w : W) (hs : w.variant=.S2) (x : E) :
    mapResult mapRust (PV_B2_F_AllocationEffects.copied request w x)=run request w x := by
  rw [PV_B2_F_MaterializeRequest.complete_result]
  exact original request w hs x
#print axioms copied
end R1Z.PV_RunJoin_WeightMaterialResult47
