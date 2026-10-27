import R0P.Value

/-! Field transport for the retained value relation. This connects the exact
QM31 source residual equations to the WideExact residual list through the
already proved ring homomorphism, without normalizing field elements. -/
set_option autoImplicit false
namespace AspisR1.ValueFamilyFieldTransport

variable {K L : Type} [Field K] [Field L]

def mapOpenings (g : K →+* L) (o : R0P.Openings K) : R0P.Openings L :=
  ⟨fun i => g (o.z i), fun i => g (o.succ i), fun i => g (o.xor12 i)⟩

theorem map_reconstruct (g : K →+* L) (view : Fin 16 → K) :
    g (R0P.valueReconstruct10 view) =
      R0P.valueReconstruct10 (fun i => g (view i)) := by
  simp only [R0P.valueReconstruct10, map_add]

theorem map_range (g : K →+* L) (o : R0P.Openings K) :
    (R0P.valueRange o).map g = R0P.valueRange (mapOpenings g o) := by
  simp only [R0P.valueRange, List.map_append, List.map_ofFn,
    List.map_cons, List.map_nil, Function.comp_def, map_sub, map_pow,
    map_add, map_mul, map_ofNat, map_reconstruct, mapOpenings]

/-- The public argument is irrelevant to this family, so any public values
on either side may be used. All selector and opening cells are transported. -/
theorem map_family (g : K →+* L) (pub : R0P.Public K) (pub' : R0P.Public L)
    (o : R0P.Openings K) (sel : R0P.Sel K) :
    ((R0P.valueFamily (K := K)).residuals pub o sel).map g =
      (R0P.valueFamily (K := L)).residuals pub' (mapOpenings g o)
        (fun i => g (sel i)) := by
  simp only [R0P.valueFamily]
  rw [← map_range g o]
  simp [List.map_append, List.map_map, List.map_cons, List.map_nil,
    Function.comp_def, map_mul, map_add, map_zero, map_sub, mapOpenings]

#print axioms map_reconstruct
#print axioms map_range
#print axioms map_family
end AspisR1.ValueFamilyFieldTransport
