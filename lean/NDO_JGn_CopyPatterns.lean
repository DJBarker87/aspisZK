import NDO_JGn_PatternMath
import NDO_JGn_CopyCanonical
import NDO_JGa_ChallengeCanonical
import RPv_JGa_CopyPowers
import NDO_JGl_ArrayIdentity
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGn_CopyPatterns
open Aeneas Aeneas.Std Result WP FIq_Native
open pool_v1.pair_forest_copy_terminal
open FIw_ArrayValue (canonical decoded)

theorem powersCanonical : canonical JGn_CopyPowers.powers := by
  obtain ⟨out,run,hc⟩ := JGa_CopyPowers.source 16 0#usize
    JFu_TerminalPrefix.challenges.lambda JFu_TerminalPrefix.challenges.lambda
    (Array.repeat 16#usize field.QM31.ZERO) rfl JGa_ChallengeCanonical.lambda
    JGa_ChallengeCanonical.lambda (JFy_ZeroArrays.source 16#usize)
  have same := Result.ok.inj (run.symm.trans JGn_CopyPowers.source)
  have equal : out=JGn_CopyPowers.powers := congrArg Prod.fst same
  exact equal ▸ hc
#print axioms powersCanonical

theorem identified (out : Array field.QM31 14#usize)
    (run : pattern_values JGl_NumericData.a JFu_TerminalPrefix.challenges.lambda=ok out) :
    out=JGn_CopyData.patterns := by
  unfold pattern_values pattern_values_literal at run
  dsimp only at run
  erw [JGn_CopyPowers.source,bind_tc_ok] at run
  have v := FJk_PatternOuterValue.value 14 0#usize 16#usize JGl_NumericData.a
    JGn_CopyPowers.powers (Array.repeat 14#usize field.QM31.ZERO) out rfl
    JGl_NumericCanonical.a powersCanonical (JFy_ZeroArrays.source 14#usize)
    (by intro j hj;change j.val<0 at hj;omega) run
  exact JGl_ArrayIdentity.value out JGn_CopyData.patterns v.1 JGn_CopyCanonical.patterns
    (v.2.trans JGn_PatternMath.value)
#print axioms identified

theorem source : pattern_values JGl_NumericData.a JFu_TerminalPrefix.challenges.lambda=
    ok JGn_CopyData.patterns := by
  obtain ⟨out,run,_⟩ := WP.spec_imp_exists (JGa_CopyPatterns.source JGl_NumericData.a
    JFu_TerminalPrefix.challenges.lambda JGl_NumericCanonical.a JGa_ChallengeCanonical.lambda)
  exact identified out run ▸ run
#print axioms source
end AspisR1.JGn_CopyPatterns
end
