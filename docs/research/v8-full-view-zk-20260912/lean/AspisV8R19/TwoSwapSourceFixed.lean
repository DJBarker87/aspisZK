import AspisV8R19.TwoSwapSourceG
import AspisV8R19.TwoSwapFixedWeights

/-! The R120 certificate is a specialization of the actual two-swap exact-
field weights, not the old T163 weights. Transport to arbitrary target fields
uses a ring homomorphism. No accepted transcript/challenge law is assumed. -/
set_option autoImplicit false
namespace AspisR19.TwoSwapSourceFixed
open AspisV8R17 TwoSwapSourceTable TwoSwapSourceWeights RootCertificate
open TwoSwapSourceG
noncomputable section
variable {F G : Type*} [CommRing F] [CommRing G]

theorem code_fixed (which : Fin 3) (j : Fin 131) :
    codeWeight (fun r => sourcePointBasis (ResidualModel.point TwoSwapWitness.z which.val) r.val) j=
      TwoSwapWitness.codeValues which.val j.val := by
  simp only [codeWeight,FullPointFunctional.source_tensor,residual_order,residual_inactive]
  exact TwoSwapWitness.code_correct which j

theorem point_fixed (which : Fin 3) (r : Fin 128) :
    pointWeight half (7:M) 5 (-5)
      (fun i => sourcePointBasis (ResidualModel.point TwoSwapWitness.z which.val) i.val) r=
      TwoSwapWitness.pointValues which.val r.val := by
  calc
    _ = sourceChordTranspose half (TwoSwapWitness.codeValues which.val) 7 5 (-5) r.val := by
      rw [transpose_low]
      simp only [pointWeight,code_fixed]
    _ = _ := TwoSwapWitness.weights_correct which r

theorem map_weight (f : F →+* G) (half a b c : F) (w : Fin 1024 → F) (r : Fin 128) :
    f (pointWeight half a b c w r)=
      pointWeight (f half) (f a) (f b) (f c) (fun i => f (w i)) r := by
  simp only [pointWeight,codeWeight,map_sum,map_mul,map_sub,apply_ite,map_zero,
    ResidualModel.map_chordEntry]

theorem map_point_basis (f : F →+* G) (z : Fin 10 → F) (which r : Nat) :
    f (sourcePointBasis (ResidualModel.point z which) r)=
      sourcePointBasis (ResidualModel.point (fun i => f (z i)) which) r := by
  simp only [FullPointFunctional.source_tensor,ResidualModel.tensor,map_prod,apply_ite,
    map_sub,map_one,ResidualModel.map_point]

theorem fixed_point (f : M →+* F) (which : Fin 3) (r : Fin 128) :
    pointWeight (f half) (f 7) (f 5) (f (-5))
      (fun i => sourcePointBasis (ResidualModel.point (fun j => f (TwoSwapWitness.z j)) which.val) i.val) r=
      f (TwoSwapWitness.pointValues which.val r.val) := by
  have h:=congrArg f (point_fixed which r)
  simpa only [map_weight,map_point_basis] using h

theorem fixed_channel (f : M →+* F) (previous : Fin 271 → F) (structured : Bool)
    (r : Fin 128) :
    pointWeight (f half) (f 7) (f 5) (f (-5))
      (sourceOriginalWeight
        (fun which => ResidualModel.point (fun j => f (TwoSwapWitness.z j)) which.val)
        (f 5) inactive (original (SourceGConstant.finishCoins (f half) previous)) structured) r=
      f (TwoSwapWitness.channelValues (if structured then 1 else 0) r.val) := by
  rw [source_point_weight,fixed_point f (1:Fin 3),fixed_point f (2:Fin 3)]
  cases structured
  · simp only [Bool.false_eq_true,if_false]
    rw [fixed_point f (0:Fin 3),← TwoSwapWitness.channel_formula0 r]
    simp only [TwoSwapWitness.channelFormula,Bool.false_eq_true,if_false,add_zero,
      map_add,map_mul,map_ofNat,show (0:Fin 3).val=0 by rfl,
      show (1:Fin 3).val=1 by rfl,show (2:Fin 3).val=2 by rfl]
    ring
  · simp only [Bool.true_eq,if_true]
    rw [source_g_boundary,← TwoSwapWitness.channel_formula1 r]
    simp only [TwoSwapWitness.channelFormula,Bool.true_eq,if_true,zero_add,
      map_add,map_mul,map_pow,map_ofNat,ResidualModel.map_chordEntry,
      show (1:Fin 3).val=1 by rfl,show (2:Fin 3).val=2 by rfl]
    ring

#print axioms code_fixed
#print axioms point_fixed
#print axioms map_weight
#print axioms map_point_basis
#print axioms fixed_point
#print axioms fixed_channel
end
end AspisR19.TwoSwapSourceFixed
