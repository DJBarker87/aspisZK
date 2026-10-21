import FourDotsActualSevenBatchLimbBoundV2
import CurrentClaimPowerReads

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1FastDotsClaimPowerCoordinateBridgeV1

abbrev ClaimE := AspisR1CurrentPreparedClaim.Concrete.E
abbrev FastWide := AspisR1FastDotsActualSevenBatchLimbBoundV2.Wide
abbrev ClaimCanonical := AspisR1CurrentPreparedClaim.Concrete.Canonical
abbrev CoordBound := AspisR1FastDotsWideLimbCanonical.CoordinateBound

/-- Explicit fieldwise carrier map: the Claim parser and FastDots extraction
    use distinct generated nominal types, but both retain these eight U32
    coordinates in the same c0/c1, QM31/CM31 order. -/
def claimToFast (x : ClaimE) : FastWide :=
  ⟨⟨⟨x.c0.c0.a, x.c0.c0.b⟩, ⟨x.c0.c1.a, x.c0.c1.b⟩⟩,
   ⟨⟨x.c1.c0.a, x.c1.c0.b⟩, ⟨x.c1.c1.a, x.c1.c1.b⟩⟩⟩

def claimArrayToFast (xs : Array ClaimE 29#usize) : Array FastWide 29#usize :=
  ⟨xs.val.map claimToFast, by simpa only [List.length_map] using xs.property⟩

/-- Canonicality in the S1 Claim owner implies the eight exact coordinate
    bounds consumed by the S4 actual reducer proof. -/
theorem canonical_to_coordinate_bound (x : ClaimE) (hx : ClaimCanonical x) :
    CoordBound (claimToFast x) := by
  cases x with
  | mk c0 c1 =>
    cases c0 with
    | mk c00 c01 =>
      cases c00 with
      | mk x00a x00b =>
        cases c01 with
        | mk x01a x01b =>
          cases c1 with
          | mk c10 c11 =>
            cases c10 with
            | mk x10a x10b =>
              cases c11 with
              | mk x11a x11b =>
                dsimp only [ClaimCanonical,
                  AspisR1CurrentPreparedClaim.Concrete.Canonical,
                  AspisR1CurrentPreparedClaim.Concrete.toFull,
                  AspisR1CurrentPreparedClaim.Concrete.toQM,
                  AspisR1CurrentPreparedClaim.Concrete.toCM] at hx
                rcases hx with ⟨h0, h1⟩
                rcases h0 with ⟨h00, h01⟩
                rcases h00 with ⟨h00a, h00b⟩
                rcases h01 with ⟨h01a, h01b⟩
                rcases h1 with ⟨h10, h11⟩
                rcases h10 with ⟨h10a, h10b⟩
                rcases h11 with ⟨h11a, h11b⟩
                exact ⟨h00a, h00b, h01a, h01b,
                  h10a, h10b, h11a, h11b⟩

/-- A successful concrete ClaimPowers call gives all 29 mapped FastDots
    entries the coordinate bounds needed by `actual_outer_startBy_success_seven_bound`.
    The caller-to-`a1` array identity remains a separate explicit premise. -/
theorem claim_powers_array_coordinate_bounds
    (gamma : ClaimE) (g : Array ClaimE 29#usize)
    (hgamma : ClaimCanonical gamma)
    (hpowers : AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize gamma = .ok g) :
    ∀ i : Fin 29,
      CoordBound ((claimArrayToFast g).val[i.val]'(by scalar_tac)) := by
  obtain ⟨computed, hcomputed, hcanonical⟩ :=
    AspisR1CurrentPreparedClaim.ClaimPowers.powers_total_exact 29#usize gamma hgamma
  have heq : computed = g := Result.ok.inj (hcomputed.symm.trans hpowers)
  subst g
  intro i
  have hcell := (hcanonical i).1
  simpa only [claimArrayToFast, List.getElem_map] using
    canonical_to_coordinate_bound _ hcell

/-- The exact S4 premise follows when its independently supplied `a1` array
    is identified with the fieldwise map of the successful ClaimPowers output.
    This lemma does not prove that caller identity. -/
theorem actual_fastdots_coordinate_bounds_of_claim_powers
    (a1 : Array FastWide 29#usize) (gamma : ClaimE) (g : Array ClaimE 29#usize)
    (hgamma : ClaimCanonical gamma)
    (hpowers : AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize gamma = .ok g)
    (hcaller : a1 = claimArrayToFast g) :
    ∀ i : Fin 29,
      CoordBound (a1.val[i.val]'(by scalar_tac)) := by
  rw [hcaller]
  exact claim_powers_array_coordinate_bounds gamma g hgamma hpowers

#print axioms canonical_to_coordinate_bound
#print axioms claim_powers_array_coordinate_bounds
#print axioms actual_fastdots_coordinate_bounds_of_claim_powers

end AspisR1FastDotsClaimPowerCoordinateBridgeV1
