import R1ParsedStateCollision
import R1TrailingStateFrame

/-! The two collision exclusions used by unified transcript recovery,
combined on the same experiment trace. This charges both events; it does
not supply the decoder cases or the round-by-round soundness obligations. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedCollision

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
    hitsBad (ParsedStateCollision.bad TrailingStateFrame.tailState Qtot) emptyTable v.1

def budget (Qtot : Nat) : ℚ := 3 * (Qtot : ℚ)^2 / (256^32 : ℚ)

theorem outside (p : Params M Cv L) (Qtot : Nat)
    (v : View (Addr L) State (Pf × Bool)) (h : ¬ Coll p Qtot v) :
    ¬ hitsBad (badColl p Qtot) emptyTable v.1 ∧
    ¬ hitsBad (ParsedStateCollision.bad TrailingStateFrame.tailState Qtot) emptyTable v.1 := by
  exact ⟨fun hb => h (Or.inl hb), fun hb => h (Or.inr hb)⟩

theorem mass {X : Type} (p : Params M Cv L) (Qtot : Nat)
    (prover : Program (Addr L) State Pf)
    (verifier : X → Pf → Program (Addr L) State Bool) (x : X)
    (hQ : ∀ H, distinctFirstReads (eval H (FS2.experiment prover verifier x)) ≤ Qtot) :
    mean (fun H : Addr L → State =>
      indicator (Coll p Qtot (eval H (FS2.experiment prover verifier x)))) ≤ budget Qtot := by
  have hbase := FS2.Duplex.coll_mass p Qtot prover verifier x hQ
  have htail := ParsedStateCollision.mass TrailingStateFrame.tailState Qtot
    prover verifier x hQ
  calc
    _ ≤ mean (fun H : Addr L → State =>
        indicator (FS2.Duplex.Coll p Qtot (eval H (FS2.experiment prover verifier x))) +
        indicator (hitsBad (ParsedStateCollision.bad TrailingStateFrame.tailState Qtot)
          emptyTable (eval H (FS2.experiment prover verifier x)).1)) :=
      mean_mono (fun _ => indicator_or_le _ _)
    _ = mean (fun H : Addr L → State =>
        indicator (FS2.Duplex.Coll p Qtot (eval H (FS2.experiment prover verifier x)))) +
      mean (fun H : Addr L → State =>
        indicator (hitsBad (ParsedStateCollision.bad TrailingStateFrame.tailState Qtot)
          emptyTable (eval H (FS2.experiment prover verifier x)).1)) := mean_add _ _
    _ ≤ FS2.Duplex.κ Qtot + (Qtot : ℚ) * ((Qtot : ℚ) / (256^32 : ℚ)) :=
      add_le_add hbase htail
    _ = budget Qtot := by unfold FS2.Duplex.κ budget; ring

#print axioms outside
#print axioms mass

end AspisR1.UnifiedCollision
end
