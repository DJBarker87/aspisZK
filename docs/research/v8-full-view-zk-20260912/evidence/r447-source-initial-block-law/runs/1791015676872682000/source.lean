import AspisV8R19.R444InitialSourceLimb
import AspisV8R19.R446RejectionListExecution

set_option autoImplicit false
namespace AspisV8R19.R447SourceInitialBlockLaw
open QM31SamplerProgram SamplerWords
open R444InitialSourceLimb R442RejectionAlphabet R443BoundedRejectionMass
open R445InitialBlockRejectionLaw R446RejectionListExecution
open R421UniformMasked31Block OracleResampling
noncomputable section

theorem sourceScan_sentinel (ws : List Nat) :
    (sourceScan ws).1 = sentinelScan modulus ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
      by_cases h : w = modulus <;>
        simp [sourceScan, sentinelScan, h, ih, modulus] at *

theorem initial_scan_value (block : State) :
    (scanAt block 0 8 (by omega)).1 = Option.map Fin.val (initialBlockResult block) := by
  rw [scanAt, sourceScan_sentinel, blockSuffix_full]
  rw [words31_value]
  have hm : List.ofFn (fun j => ((splitBlock31Equiv block).2 j).val) =
      (List.ofFn ((splitBlock31Equiv block).2)).map Fin.val := by
    simpa only [Function.comp_def] using
      (List.map_ofFn (f := (splitBlock31Equiv block).2) (g := Fin.val)).symm
  rw [hm, sentinel_list]
  unfold initialBlockResult
  rw [run_list]
  rfl

theorem actual_initial_limb_value (H : Bytes → State) (s block : State) :
    (limbRun H 8 ⟨s,block,0⟩).2.1 = Option.map Fin.val (initialBlockResult block) := by
  have h := limbRun_scanAt H 8 (⟨s,block,0⟩ : Cursor) (by change (0 : Nat) + 8 ≤ 8; omega)
  exact h.2.1.trans (initial_scan_value block)

theorem actual_initial_limb_failure (H : Bytes → State) (s : State) :
    mean (fun block : State =>
      if (limbRun H 8 ⟨s,block,0⟩).2.1 = none then (1 : ℚ) else 0) =
      (1 / (2147483648 : ℚ)) ^ 8 := by
  simp_rw [actual_initial_limb_value]
  simpa only [Option.map_eq_none_iff] using initial_block_failure

theorem mapped_eq_some (o : Option (Fin modulus)) (a : Fin modulus) :
    Option.map Fin.val o = some a.val ↔ o = some a := by
  cases o with
  | none => simp
  | some b => simp only [Option.map_some, Option.some.injEq, Fin.val_inj]

theorem actual_initial_limb_mass (H : Bytes → State) (s : State) (a : Fin modulus) :
    mean (fun block : State =>
      if (limbRun H 8 ⟨s,block,0⟩).2.1 = some a.val then (1 : ℚ) else 0) =
      (1 - (1 / (2147483648 : ℚ)) ^ 8) / 2147483647 := by
  simp_rw [actual_initial_limb_value, mapped_eq_some]
  exact initial_block_value a

#print axioms sourceScan_sentinel
#print axioms initial_scan_value
#print axioms actual_initial_limb_value
#print axioms actual_initial_limb_failure
#print axioms mapped_eq_some
#print axioms actual_initial_limb_mass
end
end AspisV8R19.R447SourceInitialBlockLaw
