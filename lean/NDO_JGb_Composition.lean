import NDO_JGb_CompositionSuffix
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGb_Composition
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon decode)
open FIw_ArrayValue (canonical)
open pool_v1.pair_forest_semantic_terminal

theorem tail (selected : Array field.QM31 84#usize) (a b c : Array field.QM31 16#usize)
    (m : Array field.QM31 10#usize) (s : pool_v1.pair_forest_copy_terminal.Selectors)
    (ps : state_only_poseidon.StateOnlyPoseidonSelectors) (leading full internal : field.QM31)
    (path sem : Array field.QM31 24#usize) (pos : Array field.QM31 4#usize)
    (h1 : field.QM31) (copy : pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledCopyTerminalV1)
    (hpos : JFy_PoseidonPrefix.tail ⟨a,b,c⟩ ps leading full internal=ok pos)
    (hsem : JFy_SemanticPrefix.tail JFu_PublicSemantic.value ⟨a,b,c⟩ s path=ok sem)
    (hh1 : selected_claim selected 0#usize 26#usize=ok h1)
    (hcopy : pool_v1.pair_forest_copy_terminal.evaluate_with_selectors a h1 s
      JFu_TerminalPrefix.challenges.lambda JFu_TerminalPrefix.challenges.chi
      JFu_PublicSemantic.value.transition.live_snapshot.next_pair_index .PrivateTransfer=ok copy) :
    JFy_CompositionTail.tail selected a b c m s ps leading full internal path=
      JGb_CompositionSuffix.run selected a m sem pos h1 copy := by
  unfold JFy_CompositionTail.tail
  dsimp only
  rw [hpos,bind_tc_ok]
  have hcol : SELECTED_H1_COLUMN=ok 26#usize := by
    unfold SELECTED_H1_COLUMN POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1
      state_only_hiding.STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS
    have spec : (16#usize+10#usize : Result Usize) ⦃ out => out.val=26 ⦄ := by
      step*
    obtain ⟨out,call,value⟩ := WP.spec_imp_exists spec
    have same : out=26#usize := UScalar.eq_of_val_eq value
    exact same ▸ call
  have samepublic : {JFu_PublicSemantic.value with withdrawal_amount := (none : Option U32)}=JFu_PublicSemantic.value := by rfl
  rw [samepublic,hsem,bind_tc_ok,hcol,bind_tc_ok,hh1,bind_tc_ok]
  have variant : copy_variant JFu_PublicSemantic.value.variant=ok
      pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1.PrivateTransfer := by rfl
  rw [variant,bind_tc_ok,hcopy,bind_tc_ok]
  simp only [JGb_CompositionSuffix.run,JGb_Horner.run,bind_assoc_eq,bind_tc_ok]
#print axioms tail

/-- Forward composition from the SAME source results. Poseidon success is
still explicit; no accepted-fixture claim follows from this conditional lemma. -/
theorem source (selected : Array field.QM31 84#usize) (a b c : Array field.QM31 16#usize)
    (m : Array field.QM31 10#usize) (s : pool_v1.pair_forest_copy_terminal.Selectors)
    (ps : state_only_poseidon.StateOnlyPoseidonSelectors) (leading full internal : field.QM31)
    (path sem : Array field.QM31 24#usize) (pos : Array field.QM31 4#usize)
    (h1 : field.QM31) (copy : pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledCopyTerminalV1)
    (hprefix : composition_parts JFu_PublicSemantic.value selected JFu_TerminalPrefix.alpha
      JFu_TerminalPrefix.challenges.lambda JFu_TerminalPrefix.challenges.chi
      JFu_TerminalPrefix.challenges.theta=JFy_CompositionTail.tail selected a b c m s ps leading full internal path)
    (hpos : JFy_PoseidonPrefix.tail ⟨a,b,c⟩ ps leading full internal=ok pos)
    (hsem : JFy_SemanticPrefix.tail JFu_PublicSemantic.value ⟨a,b,c⟩ s path=ok sem)
    (hh1 : selected_claim selected 0#usize 26#usize=ok h1)
    (hcopy : pool_v1.pair_forest_copy_terminal.evaluate_with_selectors a h1 s
      JFu_TerminalPrefix.challenges.lambda JFu_TerminalPrefix.challenges.chi
      JFu_PublicSemantic.value.transition.live_snapshot.next_pair_index .PrivateTransfer=ok copy)
    (hselected : canonical selected) (hsc : canonical sem) (hpc : canonical pos)
    (hcc : Canon copy.residual) :
    ∃ comp g,composition_parts JFu_PublicSemantic.value selected JFu_TerminalPrefix.alpha
      JFu_TerminalPrefix.challenges.lambda JFu_TerminalPrefix.challenges.chi
      JFu_TerminalPrefix.challenges.theta=ok (.Ok (comp,a,m,g,h1,copy.active)) ∧
      Canon comp ∧ Canon g ∧
      decode comp=FIv_CompositionValue.polynomial
        (decode JFu_TerminalPrefix.challenges.theta) sem pos copy.residual := by
  rw [hprefix,tail selected a b c m s ps leading full internal path sem pos h1 copy hpos hsem hh1 hcopy]
  exact JGb_CompositionSuffix.source selected a m sem pos h1 copy hselected hsc hpc hcc
#print axioms source
end AspisR1.JGb_Composition
end
