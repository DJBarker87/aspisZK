import AspisV8R19.SparseGScatter

/-! The source's final coin-0 write is independent of all 270 per-round
writes. Their values remain arbitrary here, not assumed to be zero. -/
namespace AspisR19.SourceGConstant
open SparseGScatter FullQuotientWeights
noncomputable section
variable {F : Type*} [CommRing F]

theorem scale_loop {I : Type*} (rows : List I) (half start : F) :
    rows.foldl (fun scale _ => scale*half) start=start*half^rows.length := by
  induction rows generalizing start with
  | nil => simp
  | cons i rows ih => simp [ih,pow_succ]; ring

def finalScale (half : F) : F :=
  (List.range 10).reverse.foldl (fun scale _ => scale*half) 1

theorem finalScale_eq (half : F) : finalScale half=half^10 := by
  rw [finalScale,scale_loop]
  simp

def finishCoins (half : F) (previous : Fin 271 → F) : Fin 271 → F :=
  Function.update previous 0 (finalScale half)

theorem coin_zero (half : F) (previous : Fin 271 → F) :
    finishCoins half previous 0=half^10 := by simp [finishCoins,finalScale_eq]

theorem source_g_boundary (half a b c : F) (previous : Fin 271 → F) (r : Fin 128) :
    pointWeight half a b c (original (finishCoins half previous)) r=
      half^10*ResidualModel.chordEntry half a b c r.val 128 := by
  rw [point_weight,coin_zero]

#print axioms scale_loop
#print axioms finalScale_eq
#print axioms coin_zero
#print axioms source_g_boundary
end
end AspisR19.SourceGConstant
