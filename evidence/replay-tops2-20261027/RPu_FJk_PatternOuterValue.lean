import RPu_FJk_PatternInnerValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJk_PatternOuterValue
open Aeneas Aeneas.Std Result FIq_Native
open pool_v1.pair_forest_copy_terminal
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical decoded)
def model (a powers : Array field.QM31 16#usize) (j : Fin 14) : K :=
  FJk_PatternInnerValue.model a powers
    (FJk_CopyPatternDescriptor.model (FJh_Base.cell constants.COPY_PATTERNS j)) 0 0
/-- All14 source-compressed patterns, preserving actual descriptor reads. -/
theorem value (n : Nat) (i limb : Usize) (a powers : Array field.QM31 16#usize)
    (before out : Array field.QM31 14#usize) (span : i.val+n=14)
    (ha : canonical a) (hp : canonical powers) (hb : canonical before)
    (prior : ∀ j : Fin 14,j.val < i.val → decoded before j=model a powers j)
    (run : pattern_values_literal_loop1 a powers limb before i=ok out) :
    canonical out ∧ decoded out=model a powers := by
  induction n generalizing i limb before with
  | zero =>
    have stop : ¬i<14#usize := by scalar_tac
    rw [pattern_values_literal_loop1,POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1,if_neg stop] at run
    cases Result.ok.inj run
    refine ⟨hb,?_⟩
    funext j
    exact prior j (by omega)
  | succ n ih =>
    have active : i<14#usize := by scalar_tac
    have hi : i.val<14 := by omega
    rw [pattern_values_literal_loop1,POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1,if_pos active] at run
    obtain ⟨p,rp,run⟩ := FIv_Map.bind_success _ _ _ run
    obtain ⟨⟨last,word⟩,ri,run⟩ := FIv_Map.bind_success _ _ _ run
    obtain ⟨next,rn,run⟩ := FIv_Map.bind_success _ _ _ run
    obtain ⟨i',rinc,tail⟩ := FIv_Map.bind_success _ _ _ run
    have hg := JGa_PatternBounds.all p (FIr_ArrayRead.member constants.COPY_PATTERNS i p rp)
    have one := FJk_PatternInnerValue.value 16 0#usize last a powers p field.QM31.ZERO word
      rfl ha hp FIv_NativeValue.zero.1 hg ri
    have pc := FJk_CarrierRead.value constants.COPY_PATTERNS i p hi rp
    have wordValue : decode word=model a powers ⟨i.val,hi⟩ := by
      have eq := one.2.2
      rw [FIv_NativeValue.zero.2] at eq
      exact eq.trans (congrArg (fun p=>FJk_PatternInnerValue.model a powers
        (FJk_CopyPatternDescriptor.model p) 0 0) pc).symm
    have av := FIw_ArrayValue.update before next i word hi hb one.1 rn
    have inc : i'.val=i.val+1 := FIw_WordValue.add i 1#usize i' rinc
    apply ih i' last next (by omega) av.1
    · intro j hj
      rw [av.2]
      by_cases he : j.val=i.val
      · have je : j=(⟨i.val,hi⟩ : Fin (14#usize).val) := Fin.ext he
        rw [je,Function.update_self]
        exact wordValue
      · rw [Function.update_of_ne (fun h=>he (congrArg Fin.val h))]
        exact prior j (by omega)
    · exact tail
#print axioms value
end AspisR1.FJk_PatternOuterValue
end
