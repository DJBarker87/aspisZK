import R1Z.PV_RunJoin_ClaimInstalled48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ClaimLength48
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_ClaimThread48 (Column Point W)
open PV_RunJoin_WeightInstalled46
open PV_RunJoin_WeightMap46 (mapResult)

theorem values_length (evaluate : Column → Result W) (columns : List Column)
    (vs : List W) (h : PV_RunJoin_ClaimImage48.values evaluate columns=ok vs) :
    vs.length=columns.length := by
  induction columns generalizing vs with
  | nil => cases Result.ok.inj h;rfl
  | cons c cs ih =>
    cases he : evaluate c with
    | fail e => simp only [PV_RunJoin_ClaimImage48.values,he,bind_tc_fail] at h;cases h
    | div => simp only [PV_RunJoin_ClaimImage48.values,he,bind_tc_div] at h;cases h
    | ok v =>
      cases ht : PV_RunJoin_ClaimImage48.values evaluate cs with
      | fail e => simp only [PV_RunJoin_ClaimImage48.values,he,ht,bind_tc_ok,bind_tc_fail] at h;cases h
      | div => simp only [PV_RunJoin_ClaimImage48.values,he,ht,bind_tc_ok,bind_tc_div] at h;cases h
      | ok tail =>
        simp only [PV_RunJoin_ClaimImage48.values,he,ht,bind_tc_ok] at h
        cases Result.ok.inj h
        simp only [List.length_cons,ih tail ht]

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (columns : Slice Column) (point : Point)
    (small : columns.length≤14336) (out : alloc.vec.Vec U8)
    (h : @prover.opening_claim_bytes (types base) (selected base heap box ops) columns point=ok out) :
    out.length=32*columns.length := by
  have eq := PV_RunJoin_ClaimInstalled48.complete base heap box ops columns point small
  rw [h] at eq
  cases hv : PV_RunJoin_ClaimImage48.values
    (PV_RunJoin_ClaimProducerCell48.evaluate base heap box ops point) columns.val with
  | fail e => simp only [hv,mapResult,PV_B2_E_OrdinaryOriginal.mapResult] at eq;cases eq
  | div => simp only [hv,mapResult,PV_B2_E_OrdinaryOriginal.mapResult] at eq;cases eq
  | ok vs =>
    simp only [hv,mapResult,PV_B2_E_OrdinaryOriginal.mapResult] at eq
    have hb := Result.ok.inj eq
    change out.val.length=32*columns.val.length
    rw [hb,PV_RunJoin_ClaimImage48.length,values_length _ _ _ hv]
#print axioms values_length
#print axioms complete
end R1Z.PV_RunJoin_ClaimLength48
