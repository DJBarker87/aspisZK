import EmptyRootTableFacts
import AspisR1TerminalDigestBindingCandidate.R0PBridge

/-! Actual empty-root source target, canonical word bounds and agreement with
the frozen right-tweaked R0P target. All arithmetic here is symbolic Nat data. -/
set_option autoImplicit false
namespace AspisR1.EmptyRootBindingModel
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.EmptyRootExecution
open AspisR1.EmptyRootTableFacts
open AspisR1TerminalDigestBindingCandidate.LoopExact
abbrev P := AspisR1.ExtractedMaskTowerAdd.P

theorem add_mod_once (n t p : Nat) (hn : n < p) (ht : t < p) :
    (n+t)%p = if n+t ≥ p then n+t-p else n+t := by
  by_cases h : n+t ≥ p
  · rw [if_pos h, Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
  · rw [if_neg h, Nat.mod_eq_of_lt (by omega)]

theorem source_root_canonical (level : Usize) (hlevel : level.val < 21) :
    ∃ root : Array field.M31 8#usize,
      source level = .ok root ∧
      (∀ lane : Fin 8, (root.val[lane.val]'(by simpa [root.property] using lane.isLt)).val < P) ∧
      ∀ lane : Fin 8, (root.val[lane.val]'(by simpa [root.property] using lane.isLt)).val =
        R0P.emptyRootsNat ⟨level.val, hlevel⟩ lane := by
  refine ⟨row level hlevel, source_success level hlevel, ?_, ?_⟩
  · intro lane
    exact table_canonical ⟨level.val, hlevel⟩ lane
  · intro lane
    exact table_values ⟨level.val, hlevel⟩ lane

theorem right_target_matches {K : Type} [Field K]
    (expected : Array field.M31 8#usize) (level : Fin 20)
    (hvalues : ∀ lane : Fin 8,
      (expected.val[lane.val]'(by simpa [expected.property] using lane.isLt)).val =
        R0P.emptyRootsNat level.castSucc lane) (lane : Fin 8) :
    (targetValue expected true lane.val : K) = R0P.emptyRootRightTarget level lane := by
  have htweak : AspisR1TerminalDigestBindingCandidate.poseidon2.MERKLE_NODE_COMPRESSION_V3_TWEAK.val =
      0x4153_1005 := by
    norm_num [AspisR1TerminalDigestBindingCandidate.poseidon2.MERKLE_NODE_COMPRESSION_V3_TWEAK]
  have htweakBound : 0x4153_1005 < P := by
    norm_num [P, AspisR1.ExtractedMaskTowerAdd.P, AspisR1.ExtractedMaskM31AddSub.P]
  have hP : P = 0x7fff_ffff := by
    norm_num [P, AspisR1.ExtractedMaskTowerAdd.P, AspisR1.ExtractedMaskM31AddSub.P]
  have hmod := add_mod_once (R0P.emptyRootsNat level.castSucc lane) 0x4153_1005 P
    (old_table_bound level.castSucc lane) htweakBound
  simp only [targetValue, dif_pos lane.isLt, eq_self_iff_true, true_and, hvalues lane, htweak]
  unfold R0P.emptyRootRightTarget
  by_cases h7 : lane.val = 7
  · have hlast : lane.val + 1 = 8 := by omega
    simp only [if_pos h7, if_pos hlast]
    rw [hmod, hP]
  · have hlast : lane.val + 1 ≠ 8 := by omega
    simp only [if_neg h7, if_neg hlast]

theorem source_right_target (level : Usize) (hlevel : level.val < 20) :
    ∃ root : Array field.M31 8#usize,
      source level = .ok root ∧
      (∀ lane : Fin 8, (root.val[lane.val]'(by simpa [root.property] using lane.isLt)).val < P) ∧
      ∀ lane : Fin 8, (targetValue root true lane.val : AspisV8R15.ExactTowerBase.QM31Exact) =
        R0P.emptyRootRightTarget ⟨level.val, hlevel⟩ lane := by
  obtain ⟨root, hsource, hc, hv⟩ := source_root_canonical level (by omega)
  refine ⟨root, hsource, hc, ?_⟩
  intro lane
  exact right_target_matches root ⟨level.val, hlevel⟩ hv lane

#print axioms add_mod_once
#print axioms source_root_canonical
#print axioms right_target_matches
#print axioms source_right_target
end AspisR1.EmptyRootBindingModel
