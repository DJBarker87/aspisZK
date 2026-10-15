import R1LiteralOpeningCoherence
import R1LiteralMatchingFacts
import R1LiteralStageFacts

/-! Successful terminal reading fixes the exact data used by each preceding
opening bad event. These equivalences identify existing events; they do not
assert acceptance, small bad-event probability, or a source refinement. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.LiteralOpeningBinding

open LiteralTranscript LiteralOpeningCoherence
abbrev E := LiteralTranscript.E

theorem gamma_bad_iff (P : Prefix) (m : Message) (c : Challenge)
    (tail : List (Message × Challenge)) (d : MatchingSupport.Data E)
    (hround : P.round = 27)
    (hread : LiteralMatchingData.read (full P m c tail) = some d) (x : E) :
    LiteralOpeningEvents.gammaBad P m x ↔
      x ∈ ConcreteBinding.gammaBad d.W d.F d.Y := by
  obtain ⟨common, staged, row31, word, gamma, kappa, alpha0, alpha1,
    hc, hs, hr31, hw, hg, hk, ha0, ha1, hd⟩ :=
    LiteralMatchingFacts.read_success_components (full P m c tail) d hread
  subst d
  have hp := LiteralStageFacts.readSecond_gamma (full P m c tail) staged hs
  unfold LiteralOpeningEvents.gammaBad
  rw [readGamma_full P m c tail hround]
  simp only [hc, hp, hw, hg, hk, ha0,
    Option.bind_eq_bind, Option.bind_some, pure, Pure.pure]
  rfl

theorem kappa_bad_iff (P : Prefix) (m : Message) (c : Challenge)
    (tail : List (Message × Challenge)) (d : MatchingSupport.Data E)
    (hround : P.round = 28)
    (hread : LiteralMatchingData.read (full P m c tail) = some d) (x : E) :
    LiteralOpeningEvents.kappaBad P m x ↔
      x ∈ ConcreteBinding.kappaBad d.W d.F d.F0 d.Y d.c0 d.gamma := by
  obtain ⟨common, staged, row31, word, gamma, kappa, alpha0, alpha1,
    hc, hs, hr31, hw, hg, hk, ha0, ha1, hd⟩ :=
    LiteralMatchingFacts.read_success_components (full P m c tail) d hread
  subst d
  have hp := LiteralStageFacts.readSecond_kappa (full P m c tail) staged hs
  unfold LiteralOpeningEvents.kappaBad
  rw [readKappa_full P m c tail hround]
  simp only [hc, hp, hw, hg, hk, ha0,
    Option.bind_eq_bind, Option.bind_some, pure, Pure.pure]
  rfl

theorem first_bad_iff (P : Prefix) (m : Message) (c : Challenge)
    (tail : List (Message × Challenge)) (d : MatchingSupport.Data E)
    (hround : P.round = 29)
    (hread : LiteralMatchingData.read (full P m c tail) = some d) (x : E) :
    LiteralOpeningEvents.firstBad P m x ↔
      x ∈ ConcreteBinding.firstBad d.W d.gamma (FunctionalWeights.weights d.F d.F0 d.kappa) d.p0 := by
  obtain ⟨common, staged, row31, word, gamma, kappa, alpha0, alpha1,
    hc, hs, hr31, hw, hg, hk, ha0, ha1, hd⟩ :=
    LiteralMatchingFacts.read_success_components (full P m c tail) d hread
  subst d
  have hp := LiteralStageFacts.readSecond_first (full P m c tail) staged hs
  unfold LiteralOpeningEvents.firstBad
  rw [readFirst_full P m c tail hround]
  simp only [hc, hp, hw, hg, hk, ha0,
    Option.bind_eq_bind, Option.bind_some, pure, Pure.pure]
  rfl

theorem second_bad_iff (P : Prefix) (m : Message) (c : Challenge)
    (tail : List (Message × Challenge)) (d : MatchingSupport.Data E)
    (hround : P.round = 30)
    (hread : LiteralMatchingData.read (full P m c tail) = some d) (x : E) :
    LiteralOpeningEvents.secondBad P m x ↔
      x ∈ ConcreteBinding.secondBad d.W d.V d.gamma d.alpha0 (FunctionalWeights.weights d.F d.F0 d.kappa) d.p1 := by
  obtain ⟨common, staged, row31, word, gamma, kappa, alpha0, alpha1,
    hc, hs, hr31, hw, hg, hk, ha0, ha1, hd⟩ :=
    LiteralMatchingFacts.read_success_components (full P m c tail) d hread
  subst d
  unfold LiteralOpeningEvents.secondBad
  rw [readSecond_full P m c tail hround]
  simp only [hc, hs, hw, hg, hk, ha0,
    Option.bind_eq_bind, Option.bind_some, pure, Pure.pure]
  rfl

#print axioms gamma_bad_iff
#print axioms kappa_bad_iff
#print axioms first_bad_iff
#print axioms second_bad_iff

end AspisR1.LiteralOpeningBinding
end
