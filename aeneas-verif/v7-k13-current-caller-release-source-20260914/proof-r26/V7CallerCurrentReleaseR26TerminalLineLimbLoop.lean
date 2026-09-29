import V7CallerCurrentReleaseR26TerminalLineRawLoop

/-!
# Four-limb update for one terminal line

The generated outer loop adds all four scale limbs to the constant
coefficient and feeds each limb through the verified three-factor raw loop.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26TerminalLineLimbLoop

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26Qm31DotRawArithmetic
open V7CallerCurrentReleaseR26TerminalLineAccumulator
open V7CallerCurrentReleaseR26TerminalLineRawLoop

abbrev RawM31 := field.M31
abbrev ExactM31 := V7CallerCurrentReleaseR26FieldBridge.ExactM31

local instance : Inhabited RawM31 := ⟨field.M31.ZERO⟩

def constantCell (values : Array RawM31 4#usize) (limb : Nat) : RawM31 :=
  values.val[limb]!

def CanonicalConstantLimbs (values : Array RawM31 4#usize) : Prop :=
  ∀ limb, limb < 4 → GeneratedCanonicalM31 (constantCell values limb)

def LineLimbUpdateInvariant
    (baseConstant currentConstant : Array RawM31 4#usize)
    (baseRaw currentRaw : Array (Array Std.U64 4#usize) 3#usize)
    (factors : Array RawM31 3#usize) (limbs : Array Std.U32 4#usize)
    (processed : Nat) : Prop :=
  CanonicalConstantLimbs currentConstant ∧
  (∀ limb, limb < 4 →
    generatedM31ToExact (constantCell currentConstant limb) =
      if limb < processed then
        generatedM31ToExact (constantCell baseConstant limb) +
          generatedM31ToExact (limbAt limbs limb)
      else generatedM31ToExact (constantCell baseConstant limb)) ∧
  (∀ slot, slot < 3 → ∀ limb, limb < 4 →
    (rawCell currentRaw slot limb).val =
      if limb < processed then
        (rawCell baseRaw slot limb).val +
          rawM31Product (limbAt limbs limb) (factorAt factors slot)
      else (rawCell baseRaw slot limb).val)

private theorem arrayIndexRun
    {T : Type} [Inhabited T] {N : Std.Usize}
    (values : Array T N) (index : Std.Usize) (hindex : index.val < N.val) :
    Array.index_usize values index = ok values.val[index.val]! := by
  obtain ⟨value, run, valueEq⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.index_usize_spec values index (by
      simpa [Array.length_eq] using hindex))
  have hbound : index.val < values.val.length := by
    simpa [Array.length_eq] using hindex
  have hbang : values.val[index.val]! = values.val[index.val] := by
    apply List.getElem!_of_getElem?
    simp
  simpa [valueEq, hbang] using run

private theorem arrayUpdateRun
    {T : Type} [Inhabited T] {N : Std.Usize}
    (values : Array T N) (index : Std.Usize) (value : T)
    (hindex : index.val < N.val) :
    Array.update values index value = ok (values.set index value) := by
  obtain ⟨out, run, outEq⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.update_spec values index value (by
      simpa [Array.length_eq] using hindex))
  simpa [outEq] using run

private theorem constantCellSetSame
    (values : Array RawM31 4#usize) (limb : Std.Usize) (value : RawM31)
    (bound : limb.val < 4) :
    constantCell (values.set limb value) limb.val = value := by
  unfold constantCell
  simp only [Array.set_val_eq]
  rw [List.set_getElem!_eq _ _ _ _ (by
    exact ⟨by simpa [Array.length_eq] using bound, rfl⟩)]

private theorem constantCellSetFrame
    (values : Array RawM31 4#usize) (limb : Std.Usize) (value : RawM31)
    (column : Nat) (_columnBound : column < 4)
    (different : column ≠ limb.val) :
    constantCell (values.set limb value) column =
      constantCell values column := by
  unfold constantCell
  simp only [Array.set_val_eq]
  rw [List.set_getElem!_ne _ _ _ _ (by omega)]

private theorem lineLimbInvariantStep
    (baseConstant currentConstant nextConstant : Array RawM31 4#usize)
    (baseRaw currentRaw nextRaw : Array (Array Std.U64 4#usize) 3#usize)
    (factors : Array RawM31 3#usize) (limbs : Array Std.U32 4#usize)
    (limb : Std.Usize) (limbBound : limb.val < 4)
    (nextValue : RawM31)
    (nextConstantEq : nextConstant = currentConstant.set limb nextValue)
    (nextValueCanonical : GeneratedCanonicalM31 nextValue)
    (nextValueExact : generatedM31ToExact nextValue =
      generatedM31ToExact (constantCell currentConstant limb.val) +
        generatedM31ToExact (limbAt limbs limb.val))
    (invariant : LineLimbUpdateInvariant baseConstant currentConstant
      baseRaw currentRaw factors limbs limb.val)
    (rawPost : RawSlotUpdateInvariant currentRaw nextRaw factors limbs
      limb.val 3) :
    LineLimbUpdateInvariant baseConstant nextConstant baseRaw nextRaw
      factors limbs (limb.val + 1) := by
  rcases invariant with ⟨constantCanonical, constantExact, rawExact⟩
  subst nextConstant
  refine ⟨?_, ?_, ?_⟩
  · intro column columnBound
    by_cases same : column = limb.val
    · subst column
      rw [constantCellSetSame currentConstant limb nextValue limbBound]
      exact nextValueCanonical
    · rw [constantCellSetFrame currentConstant limb nextValue column
        columnBound same]
      exact constantCanonical column columnBound
  · intro column columnBound
    by_cases same : column = limb.val
    · subst column
      rw [constantCellSetSame currentConstant limb nextValue limbBound]
      rw [nextValueExact]
      have old := constantExact limb.val limbBound
      rw [if_neg (by omega)] at old
      rw [old]
      simp
    · rw [constantCellSetFrame currentConstant limb nextValue column
        columnBound same]
      have old := constantExact column columnBound
      rw [old]
      by_cases before : column < limb.val
      · rw [if_pos before, if_pos (by omega)]
      · rw [if_neg before, if_neg (by omega)]
  · intro slot slotBound column columnBound
    have post := rawPost slot slotBound column columnBound
    have old := rawExact slot slotBound column columnBound
    by_cases same : column = limb.val
    · subst column
      simp only [show slot < 3 from slotBound] at post
      rw [post, old]
      simp
    · have frame : (rawCell nextRaw slot column).val =
          (rawCell currentRaw slot column).val := by
        simpa [same] using post
      rw [frame, old]
      by_cases before : column < limb.val
      · rw [if_pos before, if_pos (by omega)]
      · rw [if_neg before, if_neg (by omega)]

private theorem generatedLineLimbBodyActive
    (baseConstant : Array RawM31 4#usize)
    (baseRaw : Array (Array Std.U64 4#usize) 3#usize)
    (factors : Array RawM31 3#usize) (limbs : Array Std.U32 4#usize)
    (iter : core.ops.range.Range Std.Usize)
    (currentConstant : Array RawM31 4#usize)
    (currentRaw : Array (Array Std.U64 4#usize) 3#usize)
    (factorsCanonical : CanonicalLineFactors factors)
    (limbsCanonical : CanonicalLimbs limbs)
    (active : iter.start.val < iter.end.val) (endExact : iter.end.val = 4)
    (invariant : LineLimbUpdateInvariant baseConstant currentConstant
      baseRaw currentRaw factors limbs iter.start.val)
    (noOverflow : ∀ slot, slot < 3 →
      (rawCell baseRaw slot iter.start.val).val +
        rawM31Product (limbAt limbs iter.start.val) (factorAt factors slot) <
          2 ^ 64) :
    ∃ iter' nextConstant nextRaw,
      sumcheck.WeightAccumulator.impl.accumulate_line_dot_loop1.body
          factors limbs iter currentConstant currentRaw =
        ok (cont (iter', nextConstant, nextRaw)) ∧
      iter'.start.val = iter.start.val + 1 ∧
      iter'.end.val = iter.end.val ∧
      LineLimbUpdateInvariant baseConstant nextConstant baseRaw nextRaw
        factors limbs (iter.start.val + 1) := by
  have nextSpec := core.iter.range.IteratorRange.next_Usize_some_spec
    iter active
  obtain ⟨⟨option, iter'⟩, nextRun, optionEq, startEq, endEq⟩ :=
    Aeneas.Std.WP.spec_imp_exists nextSpec
  rw [optionEq] at nextRun
  have limbBound : iter.start.val < 4 := by omega
  have currentRead := arrayIndexRun currentConstant iter.start limbBound
  have limbRead := arrayIndexRun limbs iter.start limbBound
  have currentCanonical := invariant.1 iter.start.val limbBound
  have sourceLimbCanonical := limbsCanonical iter.start.val limbBound
  obtain ⟨nextValue, addRun, nextValueCanonical, nextValueExact⟩ :=
    generated_m31_add_corresponds
      (constantCell currentConstant iter.start.val)
      (limbAt limbs iter.start.val) currentCanonical sourceLimbCanonical
  have constantUpdate := arrayUpdateRun currentConstant iter.start nextValue
    limbBound
  have currentRawAtLimb : ∀ slot, slot < 3 →
      (rawCell currentRaw slot iter.start.val).val =
        (rawCell baseRaw slot iter.start.val).val := by
    intro slot slotBound
    have exact := invariant.2.2 slot slotBound iter.start.val limbBound
    rw [if_neg (by omega)] at exact
    exact exact
  have innerNoOverflow : ∀ slot, slot < 3 →
      (rawCell currentRaw slot iter.start.val).val +
        rawM31Product (limbAt limbs iter.start.val) (factorAt factors slot) <
          2 ^ 64 := by
    intro slot slotBound
    rw [currentRawAtLimb slot slotBound]
    exact noOverflow slot slotBound
  have innerSpec := generated_line_raw_slot_loop_corresponds currentRaw
    factors limbs iter.start limbBound factorsCanonical limbsCanonical
      innerNoOverflow
  obtain ⟨nextRaw, innerRun, innerPost⟩ :=
    Aeneas.Std.WP.spec_imp_exists innerSpec
  let nextConstant := currentConstant.set iter.start nextValue
  refine ⟨iter', nextConstant, nextRaw, ?_, startEq,
    congrArg UScalar.val endEq, ?_⟩
  · unfold sumcheck.WeightAccumulator.impl.accumulate_line_dot_loop1.body
    rw [nextRun]
    simp only [bind_tc_ok]
    rw [currentRead]
    simp only [bind_tc_ok]
    rw [limbRead]
    simp only [bind_tc_ok]
    change
      (do
        let m1 ← field.M31.add
          (constantCell currentConstant iter.start.val)
          (limbAt limbs iter.start.val)
        let a ← Array.update currentConstant iter.start m1
        let lineRaw ←
          sumcheck.WeightAccumulator.impl.accumulate_line_dot_loop1_loop0
            { start := 0#usize, «end» := 3#usize } currentRaw factors limbs
              iter.start
        ok (cont (iter', a, lineRaw))) = _
    rw [addRun]
    simp only [bind_tc_ok]
    rw [constantUpdate]
    simp only [bind_tc_ok]
    rw [innerRun]
    rfl
  · exact lineLimbInvariantStep baseConstant currentConstant nextConstant
      baseRaw currentRaw nextRaw factors limbs iter.start limbBound nextValue
      rfl nextValueCanonical nextValueExact invariant innerPost

theorem generated_line_limb_loop_corresponds
    (baseConstant : Array RawM31 4#usize)
    (baseRaw : Array (Array Std.U64 4#usize) 3#usize)
    (factors : Array RawM31 3#usize) (limbs : Array Std.U32 4#usize)
    (baseConstantCanonical : CanonicalConstantLimbs baseConstant)
    (factorsCanonical : CanonicalLineFactors factors)
    (limbsCanonical : CanonicalLimbs limbs)
    (noOverflow : ∀ slot, slot < 3 → ∀ limb, limb < 4 →
      (rawCell baseRaw slot limb).val +
        rawM31Product (limbAt limbs limb) (factorAt factors slot) <
          2 ^ 64) :
    sumcheck.WeightAccumulator.impl.accumulate_line_dot_loop1
        { start := 0#usize, «end» := 4#usize } baseConstant baseRaw
          factors limbs
      ⦃ out => LineLimbUpdateInvariant baseConstant out.1 baseRaw out.2
        factors limbs 4 ⦄ := by
  simp only [sumcheck.WeightAccumulator.impl.accumulate_line_dot_loop1]
  apply loop.spec_decr_nat
    (fun state : core.ops.range.Range Std.Usize ×
      (Array RawM31 4#usize × Array (Array Std.U64 4#usize) 3#usize) =>
        4 - state.1.start.val)
    (fun state => state.1.end.val = 4 ∧ state.1.start.val ≤ 4 ∧
      LineLimbUpdateInvariant baseConstant state.2.1 baseRaw state.2.2
        factors limbs state.1.start.val)
    (fun out : Array RawM31 4#usize ×
        Array (Array Std.U64 4#usize) 3#usize =>
      LineLimbUpdateInvariant baseConstant out.1 baseRaw out.2 factors limbs 4)
  · rintro ⟨iter, currentConstant, currentRaw⟩
      ⟨endExact, startBound, invariant⟩
    dsimp only at endExact startBound invariant ⊢
    by_cases active : iter.start.val < iter.end.val
    · have limbBound : iter.start.val < 4 := by omega
      obtain ⟨iter', nextConstant, nextRaw, bodyRun, nextStart, nextEnd,
          nextInvariant⟩ :=
        generatedLineLimbBodyActive baseConstant baseRaw factors limbs iter
          currentConstant currentRaw factorsCanonical limbsCanonical active
          endExact invariant (fun slot slotBound =>
            noOverflow slot slotBound iter.start.val limbBound)
      rw [bodyRun]
      simp only [Aeneas.Std.WP.spec_ok]
      have nextInvariant' :
          LineLimbUpdateInvariant baseConstant nextConstant baseRaw nextRaw
            factors limbs iter'.start.val := by
        rw [nextStart]
        exact nextInvariant
      refine ⟨⟨?_, ?_, nextInvariant'⟩, ?_⟩
      · rw [nextEnd]
        exact endExact
      · rw [nextStart]
        omega
      · rw [nextStart]
        omega
    · have done : iter.start.val = 4 := by omega
      have nextSpec := core.iter.range.IteratorRange.next_Usize_none_spec
        iter (by omega)
      obtain ⟨⟨option, iter'⟩, nextRun, optionEq, iterEq⟩ :=
        Aeneas.Std.WP.spec_imp_exists nextSpec
      rw [optionEq, iterEq] at nextRun
      unfold sumcheck.WeightAccumulator.impl.accumulate_line_dot_loop1.body
      rw [nextRun]
      simpa [done] using invariant
  · refine ⟨by norm_num, by norm_num, ?_, ?_, ?_⟩
    · exact baseConstantCanonical
    · intro limb limbBound
      simp
    · intro slot slotBound limb limbBound
      simp

#print axioms generated_line_limb_loop_corresponds

end V7CallerCurrentReleaseR26TerminalLineLimbLoop
