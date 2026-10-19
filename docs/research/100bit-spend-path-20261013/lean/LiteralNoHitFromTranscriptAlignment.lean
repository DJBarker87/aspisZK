import LiteralAdaptiveClassifierHitToDecodedChain

set_option autoImplicit false
noncomputable section
namespace AspisR1.LiteralNoHitFromTranscriptAlignment

open FS FS2 R0C.V3 AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open AspisR1.AcceptedAdaptiveFiatShamir
open AspisR1.LiteralAdaptiveClassifierHitToDecodedChain
open AspisR1.GenericNoHit

variable {X M C W Pf I A Y : Type}
variable [DecidableEq I] [Inhabited A] [Fintype A]

theorem hitFrom_of_rounds_eq
    (bad : Prefix X M C → M → C → Prop) (x : X) (prev : List (M × C))
    {rs ss : List (M × C)} (h : rs = ss) : hitFrom bad x prev rs → hitFrom bad x prev ss := by
  cases h
  intro hh
  exact hh

/-- If the raw recorded protocol rounds equal those in the accepted adaptive
execution, then no collision plus no decoded classifier chain rules out a raw
classifier hit. This is the deterministic bridge needed by
`CleanAcceptedModel`; the round equality remains an explicit input. -/
theorem no_raw_hit_of_no_chain
    (pr : FS2.Protocol X M C W Pf I A)
    (bad : Prefix X M C → M → C → Prop)
    (dec : R0C.V3.Dec X M C I A Y)
    (P : Program I A (X × Pf)) (V : X → Pf → Program I A Bool)
    (κ : Nat → ℚ) (Qtot : Nat)
    (inj : AcceptedAdaptiveFiatShamir.LazyInj pr dec P V κ Qtot)
    (hreads : ChainsRead pr) (hV : ReadsChains pr V)
    (H : I → A) (rawProof : Pf)
    (hcoll : ¬ inj.Coll (eval H (AcceptedAdaptiveFiatShamir.experiment P V)))
    (hacc : FS2.accepts (eval H (AcceptedAdaptiveFiatShamir.experiment P V)))
    (hchain : ¬ hitsChain3 dec (fun P m _T c => bad P m c) emptyTable
      (eval H (AcceptedAdaptiveFiatShamir.experiment P V)).1)
    (halign : (pr.transcript H
      (eval H (AcceptedAdaptiveFiatShamir.experiment P V)).2.1.1
      (eval H (AcceptedAdaptiveFiatShamir.experiment P V)).2.1.2 pr.r).rounds =
      (pr.transcript H (eval H (AcceptedAdaptiveFiatShamir.experiment P V)).2.1.1
        rawProof pr.r).rounds) :
    ¬ hitFrom bad (eval H (AcceptedAdaptiveFiatShamir.experiment P V)).2.1.1 []
      (pr.transcript H (eval H (AcceptedAdaptiveFiatShamir.experiment P V)).2.1.1
        rawProof pr.r).rounds := by
  intro hraw
  have hcurrent := hitFrom_of_rounds_eq bad
    (eval H (AcceptedAdaptiveFiatShamir.experiment P V)).2.1.1 [] halign.symm hraw
  have hc := accepted_hit_implies_decoded_chain pr bad dec P V κ Qtot inj hreads hV
    H hcoll hacc hcurrent
  exact hchain hc

#print axioms no_raw_hit_of_no_chain
end AspisR1.LiteralNoHitFromTranscriptAlignment
end
