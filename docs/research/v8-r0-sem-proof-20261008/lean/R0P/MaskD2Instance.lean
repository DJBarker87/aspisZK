import R0P.MaskOpeningDensity

/-! Assembly after every semantic, circle and opening sub-bound was checked. -/
set_option autoImplicit false
namespace R0P.Mask
open FS FS2 FS2.Duplex R0C.SemStatement R0P.SemSource R0P.SemD3Glue AspisWideTower
open AspisV8R19.MemoizedProgramLaw AspisV8R19.AdaptiveFirstReadLaw
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8PairedCommitment
noncomputable section
attribute [local instance] Classical.propDecidable

theorem combinedProtocolZ_D2 {Sfield : Fin 29 → Subfield WideExact} {Pf : Type} {L : Nat}
    (maskClaims : (Fin 29 → WideExact) → (Fin 29 → WideExact) → (Fin 10 → WideExact) → WideExact) (B : PackBasis (Sfield 0))
    (p : Duplex.Params (MsgZ WideExact) (ChalZ WideExact) L)
    (msg : Pf → Nat → MsgZ WideExact)
    (decode : R0P.MaskDuplex.CombinedDecode (SemMsgZ WideExact) Sfield L)
    (hσsem : ∀ (i : Nat) (_hi : i < 25) (s : State), p.σ i s = .semantic (semChal s))
    (hσz0 : ∀ s : State, p.σ 25 s = .circle (circleSample0 s))
    (hσz1 : ∀ s : State, p.σ 26 s = .circle (circleSample1 s))
    (hσopen : ∀ (j : Fin 4) (s : State), p.σ (27 + j.val) s = .opening (R0C.V3.DQ.σQ j.val s)) :
    FS2.D2 (combinedProtocolZ B p msg decode) (duplexRowsZ maskClaims B combinedD2BudgetZ) := by
  intro i P m T' T hround hi hd
  have hi32 : i < 32 := hi
  change independentMean (combinedSamplerAt 31 p i P m).toProgram
    (fun w => indicator (¬ (duplexRowsZ maskClaims B combinedD2BudgetZ).doomed (P.ext m w.2) T)) ≤
    combinedD2BudgetZ i
  by_cases h25 : i < 25
  · rw [combinedSamplerAt, if_pos (show i < 31 by omega)]
    exact semantic_rowZ_D2 maskClaims B combinedD2BudgetZ p i P m T' T hround h25 hd (hσsem i h25)
  · by_cases h27 : i < 27
    · have hcases : i = 25 ∨ i = 26 := by omega
      rcases hcases with rfl | rfl
      · rw [combinedSamplerAt, if_pos (show 25 < 31 by omega)]
        simpa only [combinedD2BudgetZ, show ¬ (25 : Nat) < 14 by omega,
          show (25 : Nat) ≠ 14 by omega, show ¬ (25 : Nat) < 25 by omega,
          show (25 : Nat) < 27 by omega, if_false, if_true] using
          circle_row25_D2 maskClaims B combinedD2BudgetZ p P m T' T hround hd hσz0
      · rw [combinedSamplerAt, if_pos (show 26 < 31 by omega)]
        simpa only [combinedD2BudgetZ, show ¬ (26 : Nat) < 14 by omega,
          show (26 : Nat) ≠ 14 by omega, show ¬ (26 : Nat) < 25 by omega,
          show (26 : Nat) < 27 by omega, if_false, if_true] using
          circle_row26_D2 maskClaims B combinedD2BudgetZ p P m T' T hround hd hσz1
    · by_cases h31 : i < 31
      · let j : Fin 4 := ⟨i-27, by omega⟩
        have hij : i = 27 + j.val := by dsimp [j]; omega
        rw [hij, combinedSamplerAt, if_pos (show 27+j.val < 31 by omega)]
        simpa only [combinedD2BudgetZ, show ¬ 27+j.val < 14 by omega,
          show 27+j.val ≠ 14 by omega, show ¬ 27+j.val < 25 by omega,
          show ¬ 27+j.val < 27 by omega, show 27+j.val < 31 by omega,
          if_false, if_true, Nat.add_sub_cancel_left] using
          opening_fieldZ_D2 maskClaims B combinedD2BudgetZ p j P m T' T (hround.trans hij) hd (hσopen j)
      · have hij : i = 31 := by omega
        rw [hij]
        simpa only [combinedD2BudgetZ, show ¬ (31 : Nat) < 14 by omega,
          show (31 : Nat) ≠ 14 by omega, show ¬ (31 : Nat) < 25 by omega,
          show ¬ (31 : Nat) < 27 by omega, show ¬ (31 : Nat) < 31 by omega,
          if_false] using
          opening_q22Z_D2 maskClaims B combinedD2BudgetZ p P m T' T (hround.trans hij) hd

#print axioms combinedProtocolZ_D2
end
end R0P.Mask
