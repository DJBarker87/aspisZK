import AspisV8R19.R454RefillProgramShape
import AspisV8R19.R453SourceFirstLimbLaw

set_option autoImplicit false
namespace AspisV8R19.R455SourceRefillLaw
open QM31SamplerProgram MemoizedProgramLaw OracleProgramOps
open R445InitialBlockRejectionLaw AspisV8PairedCommitment
abbrev State := SourceDuplexStep.State
abbrev Bytes := DuplexFrames.Bytes
noncomputable section

theorem refill_eq_first_limb (c : Cursor) (hc : c.index.val = 8) :
    limbProgram 8 c = R453SourceFirstLimbLaw.firstLimbProgram c.state := by
  rw [R454RefillProgramShape.limbProgram_refill_shape c 7 hc (by omega)]
  unfold R453SourceFirstLimbLaw.firstLimbProgram
  congr 1
  funext p
  exact (R452NoRefillProgram.limbProgram_no_refill (fun _ => p.2) 8
    ⟨p.2,p.1,0⟩ (by change (0 : Nat) + 8 ≤ 8; omega)).symm

theorem refill_lazy_mean (c : Cursor) (hc : c.index.val = 8) (t : Table Bytes State)
    (hs : t (DuplexFrames.squeeze (SourceDuplexStep.bytes c.state)) = none)
    (ha : t (DuplexFrames.advance (SourceDuplexStep.bytes c.state)) = none)
    (f : Option Nat → ℚ) :
    lazyMean (limbProgram 8 c) t (fun v => f v.2.1) =
      OracleResampling.mean (fun block : State =>
        f (Option.map Fin.val (initialBlockResult block))) := by
  rw [refill_eq_first_limb c hc]
  exact R453SourceFirstLimbLaw.first_limb_lazy_mean c.state t hs ha f

theorem refill_lazy_failure (c : Cursor) (hc : c.index.val = 8) (t : Table Bytes State)
    (hs : t (DuplexFrames.squeeze (SourceDuplexStep.bytes c.state)) = none)
    (ha : t (DuplexFrames.advance (SourceDuplexStep.bytes c.state)) = none) :
    lazyMean (limbProgram 8 c) t (fun v => if v.2.1 = none then (1 : ℚ) else 0) =
      (1 / (2147483648 : ℚ)) ^ 8 := by
  rw [refill_eq_first_limb c hc]
  exact R453SourceFirstLimbLaw.first_limb_lazy_failure c.state t hs ha

theorem refill_lazy_value (c : Cursor) (hc : c.index.val = 8) (t : Table Bytes State)
    (hs : t (DuplexFrames.squeeze (SourceDuplexStep.bytes c.state)) = none)
    (ha : t (DuplexFrames.advance (SourceDuplexStep.bytes c.state)) = none)
    (a : Fin modulus) :
    lazyMean (limbProgram 8 c) t
      (fun v => if v.2.1 = some a.val then (1 : ℚ) else 0) =
      (1 - (1 / (2147483648 : ℚ)) ^ 8) / 2147483647 := by
  rw [refill_eq_first_limb c hc]
  exact R453SourceFirstLimbLaw.first_limb_lazy_value c.state t hs ha a

#print axioms refill_eq_first_limb
#print axioms refill_lazy_mean
#print axioms refill_lazy_failure
#print axioms refill_lazy_value
end
end AspisV8R19.R455SourceRefillLaw
