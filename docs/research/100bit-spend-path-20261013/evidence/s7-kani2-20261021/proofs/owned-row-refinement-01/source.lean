import S7Kani2OwnedRow
import Mathlib.Tactic.FinCases

/-! Value refinement of the actual emitted owned row on its four-word carrier.
The canonical/phase invariant is explicit; arithmetic callees are proved. -/
set_option autoImplicit false
namespace S7Kani2OwnedRowRefinement
open Aeneas Aeneas.Std Result
open S7Kani2OwnedRow

def makeRow (x : Fin 4 → U64) : Row := Array.make 4#usize [x 0,x 1,x 2,x 3]
def powerLimb (power : K) (j : Fin 4) : U32 :=
  if j=0 then power.c0.1 else if j=1 then power.c0.2
  else if j=2 then power.c1.1 else power.c1.2

theorem literal_row_refines_model (x : Fin 4 → U64) (power : K)
    (basis : U32) (terms : Nat)
    (hcanon : ∀ j, (powerLimb power j).val<2^31-1)
    (hbasis : basis.val<2^31-1)
    (hphase : ∀ j, (x j).val<2^34+(terms%4)*(2^31-2)^2) :
    ∃ y : Fin 4 → U64,
      residue_owned (makeRow x) power basis (decide (terms%4=3)) = ok (makeRow y) ∧
      ∀ j, (y j).val = AspisR1BatchedFoldSourceStep.sourcePush terms (x j).val
        ((powerLimb power j).val*basis.val) := by
  obtain ⟨y0,hy0,hv0⟩ := S7OwnedP6ScalarProof.scalar_eq_source_push (x 0) power.c0.1 basis terms
    (by simpa [powerLimb] using hcanon 0) hbasis (hphase 0)
  obtain ⟨y1,hy1,hv1⟩ := S7OwnedP6ScalarProof.scalar_eq_source_push (x 1) power.c0.2 basis terms
    (by simpa [powerLimb] using hcanon 1) hbasis (hphase 1)
  obtain ⟨y2,hy2,hv2⟩ := S7OwnedP6ScalarProof.scalar_eq_source_push (x 2) power.c1.1 basis terms
    (by simpa [powerLimb] using hcanon 2) hbasis (hphase 2)
  obtain ⟨y3,hy3,hv3⟩ := S7OwnedP6ScalarProof.scalar_eq_source_push (x 3) power.c1.2 basis terms
    (by simpa [powerLimb] using hcanon 3) hbasis (hphase 3)
  let y : Fin 4 → U64 := fun j => if j=0 then y0 else if j=1 then y1 else if j=2 then y2 else y3
  refine ⟨y,?_,?_⟩
  · simp [makeRow,residue_owned,Array.index_usize,Array.make,hy0,hy1,hy2,hy3,y]
  · intro j
    fin_cases j <;> simpa [y,powerLimb] using (by first | exact hv0 | exact hv1 | exact hv2 | exact hv3)

#print axioms literal_row_refines_model
end S7Kani2OwnedRowRefinement
