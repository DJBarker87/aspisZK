import LiteralAdaptiveClassifierHitToDecodedChainV21
import RawAdaptiveClassifierHitDensity

set_option autoImplicit false
noncomputable section
namespace AspisR1.LiteralAdaptiveClassifierHitMassComposition

open FS FS2 R0C.V3 AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound
open AspisR1.AcceptedAdaptiveFiatShamir
open AspisR1.RawAdaptiveClassifierHitDensity
open AspisR1.LiteralAdaptiveClassifierHitToDecodedChain
open AspisR1.GenericNoHit
open AspisR1.AllAddressFiatShamir

variable {X M C W Pf I A Y : Type}
variable [DecidableEq I] [Inhabited A] [Fintype I] [Fintype A]

/-- A deterministic accepted-execution classifier hit is either an adaptive
lazy-table collision or a first-read chain hit. The actual decoder density
then charges the chain event with the explicit first-read budget `Q`; no
33-round count is inferred here. -/
theorem accepted_classifier_hit_mass_le
    (pr : FS2.Protocol X M C W Pf I A)
    (bad : Prefix X M C → M → C → Prop)
    (dec : R0C.V3.Dec X M C I A Y)
    (P : Program I A (X × Pf)) (V : X → Pf → Program I A Bool)
    (κ : Nat → ℚ) (Qtot Q : Nat)
    (inj : AcceptedAdaptiveFiatShamir.LazyInj pr dec P V κ Qtot)
    (hreads : ChainsRead pr) (hV : ReadsChains pr V)
    (hCD : ∀ a T own pend g, dec a T = some (own, pend, g) →
      blaw g (fun out => indicator (bad out.1 out.2.1 out.2.2)) own pend ≤
        PerAttemptEnvelope.B)
    (Hbound : ∀ H : I → A, firstReads emptyTable
      (eval H (AcceptedAdaptiveFiatShamir.experiment P V)).1 ≤ Q)
    (Hit : View I A ((X × Pf) × Bool) → Prop)
    (hhit : ∀ H : I → A,
      accepts (eval H (AcceptedAdaptiveFiatShamir.experiment P V)) →
      Hit (eval H (AcceptedAdaptiveFiatShamir.experiment P V)) →
      hitFrom bad (eval H (AcceptedAdaptiveFiatShamir.experiment P V)).2.1.1 []
        (pr.transcript H (eval H (AcceptedAdaptiveFiatShamir.experiment P V)).2.1.1
          (eval H (AcceptedAdaptiveFiatShamir.experiment P V)).2.1.2 pr.r).rounds) :
    lazyMean (AcceptedAdaptiveFiatShamir.experiment P V) emptyTable
      (fun v => indicator (accepts v ∧ Hit v)) ≤
      κ Qtot + (Q : ℚ) * PerAttemptEnvelope.B := by
  let exp := AcceptedAdaptiveFiatShamir.experiment P V
  have hpoint : ∀ H : I → A,
      indicator (accepts (eval H exp) ∧ Hit (eval H exp)) ≤
        indicator (inj.Coll (eval H exp)) +
          indicator (hitsChain3 dec (fun P m _T c => bad P m c)
            emptyTable (eval H exp).1) := by
    intro H
    refine le_trans (indicator_mono ?_) (indicator_or_le _ _)
    rintro ⟨hacc, hhit'⟩
    by_cases hc : inj.Coll (eval H exp)
    · exact Or.inl hc
    · exact Or.inr
        (accepted_hit_implies_decoded_chain pr bad dec P V κ Qtot inj hreads hV
          H hc hacc (hhit H hacc hhit'))
  have hchain : lazyMean exp emptyTable
      (fun v => indicator (hitsChain3 dec (fun P m _T c => bad P m c)
        emptyTable v.1)) ≤ (Q : ℚ) * PerAttemptEnvelope.B := by
    exact lemmaA3 dec (fun P m _T c => bad P m c) PerAttemptEnvelope.B
      exp emptyTable Q (by unfold PerAttemptEnvelope.B; positivity)
      (by
        intro a T own pend g hd
        exact hCD a T own pend g hd) (by
        apply firstReadsBound_of_traces
        exact Hbound)
  calc
    lazyMean exp emptyTable (fun v => indicator (accepts v ∧ Hit v)) ≤
        lazyMean exp emptyTable (fun v => indicator (inj.Coll v) +
          indicator (hitsChain3 dec (fun P m _T c => bad P m c) emptyTable v.1)) :=
      AllAddressFiatShamir.lazyMean_mono_of_eval exp _ _ hpoint
    _ = lazyMean exp emptyTable (fun v => indicator (inj.Coll v)) +
        lazyMean exp emptyTable (fun v => indicator (hitsChain3 dec
          (fun P m _T c => bad P m c) emptyTable v.1)) := lazyMean_add _ _ _ _
    _ ≤ κ Qtot + (Q : ℚ) * PerAttemptEnvelope.B := add_le_add inj.mass hchain

#print axioms accepted_classifier_hit_mass_le
end AspisR1.LiteralAdaptiveClassifierHitMassComposition
end
