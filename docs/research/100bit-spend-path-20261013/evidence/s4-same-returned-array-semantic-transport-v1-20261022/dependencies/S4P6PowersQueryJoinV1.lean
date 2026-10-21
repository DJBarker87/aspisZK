import S4Tx2PowersQuerySourceCutV1
import S4FullQueryValuesPrefixV1
import PowersP6GeneratedErasureV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S4P6PowersQueryJoinV1

abbrev Stage2Wide := AspisR1FastDotsTx2PowersQuerySourceCutV1.Wide
abbrev ClaimE := AspisR1CurrentPreparedClaim.Concrete.E
abbrev ClaimOps := AspisR1FastDotsTx2PowersQuerySourceCutV1.Ops
abbrev ClaimArray := Array ClaimE 29#usize
abbrev Stage2Array := Array Stage2Wide 29#usize

def stage2ToClaim (x : Stage2Wide) : ClaimE :=
  ⟨⟨⟨x.c0.c0.a, x.c0.c0.b⟩, ⟨x.c0.c1.a, x.c0.c1.b⟩⟩,
   ⟨⟨x.c1.c0.a, x.c1.c0.b⟩, ⟨x.c1.c1.a, x.c1.c1.b⟩⟩⟩

def claimToStage2 (x : ClaimE) : Stage2Wide :=
  ⟨⟨⟨x.c0.c0.a, x.c0.c0.b⟩, ⟨x.c0.c1.a, x.c0.c1.b⟩⟩,
   ⟨⟨x.c1.c0.a, x.c1.c0.b⟩, ⟨x.c1.c1.a, x.c1.c1.b⟩⟩⟩

theorem stage2_claim_roundtrip (x : Stage2Wide) : claimToStage2 (stage2ToClaim x) = x := by
  cases x <;> rfl

def claimArrayToStage2 (xs : ClaimArray) : Stage2Array :=
  ⟨xs.val.map claimToStage2, by simpa only [List.length_map] using xs.property⟩

def sourceP6WeightsPowers (N : Usize) (x : Stage2Wide) : Result Stage2Array := do
  let values ← AspisR1PowersP6GeneratedErasureV1.sourceArrayPowers 29#usize (stage2ToClaim x)
  .ok (claimArrayToStage2 values)

def withSourceP6WeightsPowers {H : Type} (ops : ClaimOps H) : ClaimOps H :=
  {ops with weightsPowers := sourceP6WeightsPowers}

private theorem bind_ok_inv {A B : Type} {r : Result A} {k : A → Result B} {out : B}
    (h : (do let x ← r; k x) = .ok out) : ∃ x, r = .ok x ∧ k x = .ok out := by
  cases r with
  | fail e => simp at h
  | div => simp at h
  | ok x => exact ⟨x, rfl, h⟩

/-- The successful tx2 source cut's exact powers result is the mapped array
from the checked stateful P6 powers model, and that same source input has a
successful ClaimPowers result. The intervening query call remains the exact
same-g operation exposed by the tx2 cut. -/
theorem tx2_prefix_p6_powers_same_g {H : Type}
    (ops : ClaimOps H) (call : AspisR1FastDotsTx2PowersQuerySourceCutV1.QueryCall)
    (proof : Slice U8) (p : AspisR1Stage2.verifier.Prepared)
    (a : AspisR1Stage2.verifier.Accumulator) (hash : H)
    (obs : Option (AspisR1Stage2.verifier.Phase → Result Unit))
    (out : AspisR1FastDotsTx2PowersQuerySourceCutV1.QueryState)
    (hgamma : AspisR1CurrentPreparedClaim.Concrete.Canonical (stage2ToClaim p.gamma))
    (h : AspisR1FastDotsTx2PowersQuerySourceCutV1.tx2QueryPrefix
      (withSourceP6WeightsPowers ops) call proof p a hash obs = .ok out) :
    ∃ g : Stage2Array,
      sourceP6WeightsPowers 29#usize p.gamma = .ok g ∧
      ∃ geometry : AspisR1FastDotsTx2PowersQuerySourceCutV1.QueryGeometry,
        (withSourceP6WeightsPowers ops).makeGeometry p.queries a.next 22#usize = .ok geometry ∧
      ∃ pending : AspisR1FastDotsTx2PowersQuerySourceCutV1.BatchedWeights,
        (withSourceP6WeightsPowers ops).makePending
          (alloc.vec.Vec.deref a.weights) = .ok pending ∧
        AspisR1Stage2.verifier.candidate.query_loop call proof p a g obs geometry pending 22#usize = .ok out ∧
      ∃ claimPowers : ClaimArray,
        AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize
          (stage2ToClaim p.gamma) = .ok claimPowers ∧
        AspisR1S4FullQueryValuesPrefixV1.fullArrayToCurrent g =
          AspisR1FastDotsClaimPowerCoordinateBridgeV1.claimArrayToFast claimPowers := by
  obtain ⟨g, hg, geometry, hgeometry, pending, hpending, hloop⟩ :=
    AspisR1FastDotsTx2PowersQuerySourceCutV1.tx2_query_prefix_success_same_g
      (withSourceP6WeightsPowers ops) call proof p a hash obs h
  have hsame : sourceP6WeightsPowers 29#usize p.gamma = .ok g := by
    simpa only [withSourceP6WeightsPowers] using hg
  unfold sourceP6WeightsPowers at hsame
  obtain ⟨claimValues, hvalues, hmap⟩ := bind_ok_inv hsame
  have hclaim := AspisR1PowersP6GeneratedErasureV1.sourceArrayPowers_success_claim
    (stage2ToClaim p.gamma) hgamma claimValues hvalues
  have hcaller : AspisR1S4FullQueryValuesPrefixV1.fullArrayToCurrent g =
      AspisR1FastDotsClaimPowerCoordinateBridgeV1.claimArrayToFast claimValues := by
    have hgmap : claimArrayToStage2 claimValues = g := Result.ok.inj hmap
    rw [← hgmap]
    apply Subtype.ext
    change
      (claimValues.val.map claimToStage2).map
          AspisR1S4FullQueryValuesPrefixV1.fullWideToCurrent =
        claimValues.val.map
          AspisR1FastDotsClaimPowerCoordinateBridgeV1.claimToFast
    rw [List.map_map]
    apply List.map_congr_left
    intro x hx
    cases x <;> rfl
  exact ⟨g, hsame, geometry, hgeometry, pending, hpending, hloop,
    claimValues, hclaim, hcaller⟩

#print axioms stage2_claim_roundtrip
#print axioms tx2_prefix_p6_powers_same_g

end AspisR1S4P6PowersQueryJoinV1
