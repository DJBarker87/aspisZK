import R1CombinedMerkleTargets
import R1UnifiedCollision

/-! Combine the existing duplex collision event with the ten recorded
Merkle-target hits. The event bound is a single union bound; this module does
not instantiate any knowledge or source-correspondence claim. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.CombinedMerkleCollision

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

variable {M Cv Pf : Type} {L : Nat}

def Coll (p : Params M Cv L) (Qtot : Nat)
    (v : View (Addr L) State (Pf × Bool)) : Prop :=
  FS2.Duplex.Coll p Qtot v ∨
    hitsBad (ParsedTargetsCollision.bad AspisR1.CombinedMerkleTargets.pred Qtot)
      emptyTable v.1

def budget (Qtot : Nat) : ℚ := 12 * (Qtot : ℚ)^2 / (256^32 : ℚ)

theorem hits_equiv (Qtot : Nat) (T : Table (Addr L) State)
    (tr : List (Addr L × State)) :
    hitsBad (ParsedTargetsCollision.bad AspisR1.CombinedMerkleTargets.pred Qtot) T tr ↔
      (hitsBad (ParsedTargetsCollision.bad AspisR1.MerkleChildTargets.pred Qtot) T tr ∨
       hitsBad (ParsedTargetsCollision.bad AspisR1.CommitmentRootTargets.pred Qtot) T tr) := by
  induction tr generalizing T with
  | nil => simp [hitsBad]
  | cons q rest ih =>
      rcases q with ⟨a, f⟩
      simp only [hitsBad]
      constructor
      · rintro (⟨hmiss, hbad⟩ | htail)
        · rcases (AspisR1.CombinedMerkleTargets.bad_equiv Qtot a T f).mp hbad with hc | hr
          · exact Or.inl (Or.inl ⟨hmiss, hc⟩)
          · exact Or.inr (Or.inl ⟨hmiss, hr⟩)
        · rcases ih (T := put T a f) |>.mp htail with hc | hr
          · exact Or.inl (Or.inr hc)
          · exact Or.inr (Or.inr hr)
      · rintro (⟨hmiss, hc⟩ | ⟨hmiss, hr⟩ | htail)
        · exact Or.inl ⟨hmiss,
            (AspisR1.CombinedMerkleTargets.bad_equiv Qtot a T f).mpr (Or.inl hc)⟩
        · exact Or.inl ⟨hmiss,
            (AspisR1.CombinedMerkleTargets.bad_equiv Qtot a T f).mpr (Or.inr hr)⟩
        · rcases htail with hc | hr
          · exact Or.inr (ih (T := put T a f) |>.mpr (Or.inl hc))
          · exact Or.inr (ih (T := put T a f) |>.mpr (Or.inr hr))

theorem hitsBad_mono {bad₁ bad₂ : Addr L → Table (Addr L) State → State → Prop}
    (hbad : ∀ a T f, bad₁ a T f → bad₂ a T f) :
    ∀ (T : Table (Addr L) State) (tr : List (Addr L × State)),
      hitsBad bad₁ T tr → hitsBad bad₂ T tr := by
  intro T tr
  induction tr generalizing T with
  | nil => simp [hitsBad]
  | cons q rest ih =>
      rcases q with ⟨a, f⟩
      simp only [hitsBad]
      rintro (⟨hmiss, hb⟩ | ht)
      · exact Or.inl ⟨hmiss, hbad a T f hb⟩
      · exact Or.inr (ih (T := put T a f) ht)

theorem outside (p : Params M Cv L) (Qtot : Nat)
    (v : View (Addr L) State (Pf × Bool)) (h : ¬ Coll p Qtot v) :
    ¬ hitsBad (badColl p Qtot) emptyTable v.1 ∧
      ¬ hitsBad (ParsedTargetsCollision.bad AspisR1.MerkleChildTargets.pred Qtot)
        emptyTable v.1 ∧
      ¬ hitsBad (ParsedTargetsCollision.bad AspisR1.CommitmentRootTargets.pred Qtot)
        emptyTable v.1 := by
  have hduplex : ¬ hitsBad (badColl p Qtot) emptyTable v.1 :=
    fun hc => h (Or.inl hc)
  have hcombined : ¬ hitsBad
      (ParsedTargetsCollision.bad AspisR1.CombinedMerkleTargets.pred Qtot)
        emptyTable v.1 := fun hc => h (Or.inr hc)
  rcases (hits_equiv Qtot emptyTable v.1).mp hcombined with hc | hr
  · exact ⟨hduplex, fun h' => hcombined ((hits_equiv Qtot emptyTable v.1).mpr (Or.inl h')),
      fun h' => hcombined ((hits_equiv Qtot emptyTable v.1).mpr (Or.inr h'))⟩
  · exact ⟨hduplex, fun h' => hcombined ((hits_equiv Qtot emptyTable v.1).mpr (Or.inl h')),
      fun h' => hcombined ((hits_equiv Qtot emptyTable v.1).mpr (Or.inr h'))⟩

theorem old_included (p : Params M Cv L) (Qtot : Nat)
    (v : View (Addr L) State (Pf × Bool)) :
    AspisR1.UnifiedCollision.Coll p Qtot v → Coll p Qtot v := by
  rintro (hduplex | htail)
  · exact Or.inl hduplex
  · apply Or.inr
    apply hitsBad_mono
    intro a T f hbad
    have hroot : ParsedTargetsCollision.bad
        AspisR1.CommitmentRootTargets.pred Qtot a T f := by
      refine ⟨⟨0, by omega⟩, ?_⟩
      simpa [AspisR1.CommitmentRootTargets.pred, ParsedStateCollision.bad] using hbad
    exact (AspisR1.CombinedMerkleTargets.bad_equiv Qtot a T f).mpr (Or.inr hroot)
    exact htail

theorem mass {X : Type} (p : Params M Cv L) (Qtot : Nat)
    (prover : Program (Addr L) State Pf)
    (verifier : X → Pf → Program (Addr L) State Bool) (x : X)
    (hQ : ∀ H, FS2.distinctFirstReads (eval H (FS2.experiment prover verifier x)) ≤ Qtot) :
    mean (fun H : Addr L → State =>
      indicator (Coll p Qtot (eval H (FS2.experiment prover verifier x)))) ≤ budget Qtot := by
  have hbase := FS2.Duplex.coll_mass p Qtot prover verifier x hQ
  have htargets := AspisR1.CombinedMerkleTargets.mass Qtot prover verifier x hQ
  calc
    _ ≤ mean (fun H : Addr L → State =>
        indicator (FS2.Duplex.Coll p Qtot (eval H (FS2.experiment prover verifier x))) +
        indicator (hitsBad
          (ParsedTargetsCollision.bad AspisR1.CombinedMerkleTargets.pred Qtot)
          emptyTable (eval H (FS2.experiment prover verifier x)).1)) :=
      mean_mono (fun _ => indicator_or_le _ _)
    _ = mean (fun H : Addr L → State =>
        indicator (FS2.Duplex.Coll p Qtot (eval H (FS2.experiment prover verifier x)))) +
      mean (fun H : Addr L → State =>
        indicator (hitsBad
          (ParsedTargetsCollision.bad AspisR1.CombinedMerkleTargets.pred Qtot)
          emptyTable (eval H (FS2.experiment prover verifier x)).1)) := mean_add _ _
    _ ≤ FS2.Duplex.κ Qtot +
      (10 : ℚ) * (Qtot : ℚ)^2 / (256^32 : ℚ) := add_le_add hbase htargets
    _ = budget Qtot := by
      unfold FS2.Duplex.κ budget
      ring

#print axioms hits_equiv
#print axioms hitsBad_mono
#print axioms outside
#print axioms old_included
#print axioms mass

end AspisR1.CombinedMerkleCollision
end
