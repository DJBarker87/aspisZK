import V7CallerCurrentReleaseR26GroupedLowSemantics

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26
open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26HalfBridge
open V7CallerCurrentReleaseR26K1QueryWeightBridge
open V7CallerCurrentReleaseR26K1StructuredWeightBridge

namespace V7CallerCurrentReleaseR26GroupedAllSame

abbrev RawQM31 := field.QM31
abbrev ExactQM31 := AspisV5ComponentCQM31TowerExact.QM31Exact

@[simp] private theorem sourceQm31ToModel_generated (x : RawQM31) :
    sourceQm31ToModel (generatedQm31ToExact x) = exactRaw x := rfl

private theorem oneCanonical : GeneratedCanonicalQM31 field.QM31.ONE := by
  norm_num [GeneratedCanonicalQM31, GeneratedCanonicalCM31,
    AspisAeneasCM31Multiplicative.CanonicalRawM31, field.QM31.ONE,
    AspisAeneasCM31Multiplicative.m31Modulus]

private theorem zeroCanonical : GeneratedCanonicalQM31 field.QM31.ZERO := by
  norm_num [GeneratedCanonicalQM31, GeneratedCanonicalCM31,
    AspisAeneasCM31Multiplicative.CanonicalRawM31, field.QM31.ZERO,
    AspisAeneasCM31Multiplicative.m31Modulus]

def allSameProgram
    (group : Std.U8) (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 : RawQM31) : Result RawQM31 := do
  let coefficient1 ← field.QM31.add field.QM31.ONE alpha3
  let coefficient2 ← field.QM31.add coefficient1 alpha2
  let coefficient3 ← field.QM31.add coefficient2 alpha
  let value ← Slice.index_usize groupValues (UScalar.cast .Usize group)
  let contribution ← field.QM31.mul value coefficient3
  let folded ← field.QM31.add field.QM31.ZERO contribution
  let half1 ← field.QM31.half folded
  field.QM31.half half1

def groupsAllSame (group : Std.U8) : Array Std.U8 4#usize :=
  Array.make 4#usize [group, group, group, group]

private def powers
    (alpha alpha2 alpha3 : RawQM31) : Array RawQM31 4#usize :=
  Array.make 4#usize [field.QM31.ONE, alpha3, alpha2, alpha]

private def unique0 : Array Std.U8 4#usize :=
  Array.repeat 4#usize 0#u8

private def unique1 (group : Std.U8) : Array Std.U8 4#usize :=
  Array.make 4#usize [group, 0#u8, 0#u8, 0#u8]

private def coefficients0 : Array RawQM31 4#usize :=
  Array.repeat 4#usize field.QM31.ZERO

private def coefficients1 : Array RawQM31 4#usize :=
  Array.make 4#usize
    [field.QM31.ONE, field.QM31.ZERO, field.QM31.ZERO, field.QM31.ZERO]

private def coefficientsAt (coefficient : RawQM31) : Array RawQM31 4#usize :=
  Array.make 4#usize
    [coefficient, field.QM31.ZERO, field.QM31.ZERO, field.QM31.ZERO]

private def countsAt (count : Std.U8) : Array Std.U8 4#usize :=
  Array.make 4#usize [count, 0#u8, 0#u8, 0#u8]

private def slots0 : Array Std.U8 4#usize :=
  Array.repeat 4#usize 0#u8

private def rangeFrom (start : Std.Usize) : core.ops.range.Range Std.Usize :=
  { start, «end» := 4#usize }

private theorem arrayIndexRun
    {T : Type} [Inhabited T] {N : Std.Usize}
    (values : Array T N) (index : Std.Usize) (hindex : index.val < N.val) :
    Array.index_usize values index = ok values.val[index.val]! := by
  obtain ⟨value, run, valueEq⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.index_usize_spec values index (by
      simpa [Array.length_eq] using hindex))
  have hbound : index.val < values.val.length := by
    simpa [Array.length_eq] using hindex
  have getExact : values.val[index.val] = values.val[index.val]! := by
    symm
    apply List.getElem!_of_getElem?
    simp [hbound]
  simpa [valueEq, getExact] using run

private theorem arrayMake4Index0
    {T : Type} [Inhabited T] (a b c d : T) :
    Array.index_usize (Array.make 4#usize [a, b, c, d]) 0#usize = ok a := by
  have run := arrayIndexRun (Array.make 4#usize [a, b, c, d]) 0#usize
    (by decide)
  change Array.index_usize (Array.make 4#usize [a, b, c, d]) 0#usize =
    ok (([a, b, c, d] : List T)[0]!) at run
  exact run

private theorem arrayMake4Index1
    {T : Type} [Inhabited T] (a b c d : T) :
    Array.index_usize (Array.make 4#usize [a, b, c, d]) 1#usize = ok b := by
  have run := arrayIndexRun (Array.make 4#usize [a, b, c, d]) 1#usize
    (by decide)
  change Array.index_usize (Array.make 4#usize [a, b, c, d]) 1#usize =
    ok (([a, b, c, d] : List T)[1]!) at run
  exact run

private theorem arrayMake4Index2
    {T : Type} [Inhabited T] (a b c d : T) :
    Array.index_usize (Array.make 4#usize [a, b, c, d]) 2#usize = ok c := by
  have run := arrayIndexRun (Array.make 4#usize [a, b, c, d]) 2#usize
    (by decide)
  change Array.index_usize (Array.make 4#usize [a, b, c, d]) 2#usize =
    ok (([a, b, c, d] : List T)[2]!) at run
  exact run

private theorem arrayMake4Index3
    {T : Type} [Inhabited T] (a b c d : T) :
    Array.index_usize (Array.make 4#usize [a, b, c, d]) 3#usize = ok d := by
  have run := arrayIndexRun (Array.make 4#usize [a, b, c, d]) 3#usize
    (by decide)
  change Array.index_usize (Array.make 4#usize [a, b, c, d]) 3#usize =
    ok (([a, b, c, d] : List T)[3]!) at run
  exact run

private theorem arrayUpdateExact {T : Type} {N : Std.Usize}
    (values : Array T N) (index : Std.Usize)
    (hindex : index.val < N.val) (value : T) :
    Array.update values index value = ok (values.set index value) := by
  unfold Array.update
  rw [Array.getElem?_Usize_eq]
  rw [List.getElem?_eq_getElem (by rw [values.property]; exact hindex)]
  apply congrArg Result.ok
  apply Subtype.ext
  rfl

private theorem rangeNext0 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        { start := 0#usize, «end» := 4#usize } =
      ok (some 0#usize, { start := 1#usize, «end» := 4#usize }) := by
  have hmax : 0 < UScalar.max .Usize := by
    have h := (1#usize).hBounds
    scalar_tac
  simp [core.iter.range.IteratorRange.next,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.forward_checked,
    core.cmp.impls.PartialOrdUsize.lt, hmax]

private theorem rangeNext1 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        { start := 1#usize, «end» := 4#usize } =
      ok (some 1#usize, { start := 2#usize, «end» := 4#usize }) := by
  have hmax : 1 < UScalar.max .Usize := by
    have h := (2#usize).hBounds
    scalar_tac
  simp [core.iter.range.IteratorRange.next,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.forward_checked,
    core.cmp.impls.PartialOrdUsize.lt, hmax]

private theorem rangeNext2 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        { start := 2#usize, «end» := 4#usize } =
      ok (some 2#usize, { start := 3#usize, «end» := 4#usize }) := by
  have hmax : 2 < UScalar.max .Usize := by
    have h := (3#usize).hBounds
    scalar_tac
  simp [core.iter.range.IteratorRange.next,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.forward_checked,
    core.cmp.impls.PartialOrdUsize.lt, hmax]

private theorem rangeNext3 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        { start := 3#usize, «end» := 4#usize } =
      ok (some 3#usize, { start := 4#usize, «end» := 4#usize }) := by
  have hmax : 3 < UScalar.max .Usize := by
    have h := (4#usize).hBounds
    scalar_tac
  simp [core.iter.range.IteratorRange.next,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.forward_checked,
    core.cmp.impls.PartialOrdUsize.lt, hmax]

private theorem rangeDone4 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        { start := 4#usize, «end» := 4#usize } =
      ok (none, { start := 4#usize, «end» := 4#usize }) := by
  simp [core.iter.range.IteratorRange.next,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.cmp.impls.PartialOrdUsize.lt]

private theorem rangeNext0End1 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        { start := 0#usize, «end» := 1#usize } =
      ok (some 0#usize, { start := 1#usize, «end» := 1#usize }) := by
  have hmax : 0 < UScalar.max .Usize := by
    have h := (1#usize).hBounds
    scalar_tac
  simp [core.iter.range.IteratorRange.next,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.forward_checked,
    core.cmp.impls.PartialOrdUsize.lt, hmax]

private theorem rangeDone1 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        { start := 1#usize, «end» := 1#usize } =
      ok (none, { start := 1#usize, «end» := 1#usize }) := by
  simp [core.iter.range.IteratorRange.next,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.cmp.impls.PartialOrdUsize.lt]

private theorem usizeZeroSucc :
    Std.Usize.wrapping_add 0#usize 1#usize = 1#usize := by
  apply UScalar.val_eq_imp
  rw [Std.Usize.wrapping_add_val_eq,
    Nat.mod_eq_of_lt (by have h := (1#usize).hSize; scalar_tac)]
  norm_num

private theorem u8OneSucc : Std.U8.wrapping_add 1#u8 1#u8 = 2#u8 := by
  apply UScalar.val_eq_imp
  rw [Std.U8.wrapping_add_val_eq,
    Nat.mod_eq_of_lt (by have h := (2#u8).hSize; scalar_tac)]
  norm_num

private theorem u8TwoSucc : Std.U8.wrapping_add 2#u8 1#u8 = 3#u8 := by
  apply UScalar.val_eq_imp
  rw [Std.U8.wrapping_add_val_eq,
    Nat.mod_eq_of_lt (by have h := (3#u8).hSize; scalar_tac)]
  norm_num

private theorem u8ThreeSucc : Std.U8.wrapping_add 3#u8 1#u8 = 4#u8 := by
  apply UScalar.val_eq_imp
  rw [Std.U8.wrapping_add_val_eq,
    Nat.mod_eq_of_lt (by have h := (4#u8).hSize; scalar_tac)]
  norm_num

private theorem castUsizeZeroU8 :
    UScalar.cast .U8 0#usize = 0#u8 := by
  apply UScalar.val_eq_imp
  rw [UScalar.cast_val_eq]
  rfl

private theorem fromU8ToUsizeExact (value : Std.U8) :
    core.convert.num.FromUsizeU8.from value = UScalar.cast .Usize value := by
  apply UScalar.val_eq_imp
  rw [core.convert.num.FromUsizeU8.from_val_eq, UScalar.cast_val_eq]
  rw [Nat.mod_eq_of_lt]
  have h := value.hBounds
  rcases System.Platform.numBits_eq with hbits | hbits <;>
    norm_num [UScalarTy.numBits, hbits] at h ⊢ <;> omega

private theorem findEmpty (group : Std.U8) :
    sumcheck.fold_group_tuple_loop0_loop0 unique0 0#usize group 0#usize =
      ok 0#usize := by
  unfold sumcheck.fold_group_tuple_loop0_loop0
  rw [loop.eq_1]
  simp [sumcheck.fold_group_tuple_loop0_loop0.body]

private theorem findExisting (group : Std.U8) :
    sumcheck.fold_group_tuple_loop0_loop0 (unique1 group) 1#usize group
        0#usize = ok 0#usize := by
  have read : Array.index_usize (unique1 group) 0#usize = ok group := by
    simpa [unique1] using arrayMake4Index0 group 0#u8 0#u8 0#u8
  unfold sumcheck.fold_group_tuple_loop0_loop0
  rw [loop.eq_1]
  unfold sumcheck.fold_group_tuple_loop0_loop0.body
  rw [if_pos (by decide), read]
  simp

private theorem phaseStep0
    (group : Std.U8) (alpha alpha2 alpha3 : RawQM31) :
    sumcheck.fold_group_tuple_loop0.body
        (groupsAllSame group) (powers alpha alpha2 alpha3)
        (rangeFrom 0#usize) unique0 coefficients0 unique0 slots0 0#usize =
      ok (cont (rangeFrom 1#usize, unique1 group, coefficients1,
        countsAt 1#u8, slots0, 1#usize)) := by
  have groupRun : Array.index_usize (groupsAllSame group) 0#usize =
      ok group := by
    simpa [groupsAllSame] using arrayMake4Index0 group group group group
  have uniqueRun : Array.update unique0 0#usize group =
      ok (unique1 group) := by
    have setExact : unique0.set 0#usize group = unique1 group := by
      apply Subtype.ext
      rfl
    rw [← setExact]
    exact arrayUpdateExact unique0 0#usize (by decide) group
  have powerRun : Array.index_usize (powers alpha alpha2 alpha3) 0#usize =
      ok field.QM31.ONE := by
    simpa [powers] using
      arrayMake4Index0 field.QM31.ONE alpha3 alpha2 alpha
  have coefficientRun : Array.update coefficients0 0#usize field.QM31.ONE =
      ok coefficients1 := by
    have setExact : coefficients0.set 0#usize field.QM31.ONE =
        coefficients1 := by
      apply Subtype.ext
      rfl
    rw [← setExact]
    exact arrayUpdateExact coefficients0 0#usize (by decide) field.QM31.ONE
  have countRun : Array.update unique0 0#usize 1#u8 =
      ok (countsAt 1#u8) := by
    have setExact : unique0.set 0#usize 1#u8 = countsAt 1#u8 := by
      apply Subtype.ext
      rfl
    rw [← setExact]
    exact arrayUpdateExact unique0 0#usize (by decide) 1#u8
  have slotRun : Array.update slots0 0#usize (UScalar.cast .U8 0#usize) =
      ok slots0 := by
    rw [castUsizeZeroU8]
    have setExact : slots0.set 0#usize 0#u8 = slots0 := by
      apply Subtype.ext
      rfl
    rw [← setExact]
    exact arrayUpdateExact slots0 0#usize (by decide) 0#u8
  unfold sumcheck.fold_group_tuple_loop0.body
  simp only [rangeFrom]
  rw [rangeNext0]
  simp only [bind_tc_ok]
  rw [groupRun]
  simp only [bind_tc_ok]
  rw [findEmpty]
  simp only [bind_tc_ok]
  rw [if_neg (by decide), uniqueRun]
  simp only [bind_tc_ok]
  rw [powerRun]
  simp only [bind_tc_ok]
  rw [coefficientRun]
  simp only [bind_tc_ok]
  rw [countRun]
  simp only [bind_tc_ok, Std.lift]
  rw [slotRun]
  simp only [bind_tc_ok, usizeZeroSucc]

private theorem phaseExistingStep
    (group : Std.U8) (alpha alpha2 alpha3 : RawQM31)
    (iter iterNext : core.ops.range.Range Std.Usize) (slot : Std.Usize)
    (coefficient power coefficientOut : RawQM31)
    (count countOut : Std.U8)
    (rangeRun : core.iter.range.IteratorRange.next
      core.iter.range.StepUsize iter = ok (some slot, iterNext))
    (groupRun : Array.index_usize (groupsAllSame group) slot = ok group)
    (coefficientRead : Array.index_usize (coefficientsAt coefficient)
      0#usize = ok coefficient)
    (powerRun : Array.index_usize (powers alpha alpha2 alpha3) slot =
      ok power)
    (addRun : field.QM31.add coefficient power = ok coefficientOut)
    (coefficientUpdate : Array.update (coefficientsAt coefficient) 0#usize
      coefficientOut = ok (coefficientsAt coefficientOut))
    (countRead : Array.index_usize (countsAt count) 0#usize = ok count)
    (countSucc : Std.U8.wrapping_add count 1#u8 = countOut)
    (countUpdate : Array.update (countsAt count) 0#usize countOut =
      ok (countsAt countOut)) :
    sumcheck.fold_group_tuple_loop0.body
        (groupsAllSame group) (powers alpha alpha2 alpha3) iter
        (unique1 group) (coefficientsAt coefficient) (countsAt count)
        slots0 1#usize =
      ok (cont (iterNext, unique1 group, coefficientsAt coefficientOut,
        countsAt countOut, slots0, 1#usize)) := by
  unfold sumcheck.fold_group_tuple_loop0.body
  rw [rangeRun]
  simp only [bind_tc_ok]
  rw [groupRun]
  simp only [bind_tc_ok]
  rw [findExisting]
  simp only [bind_tc_ok]
  rw [if_pos (by decide), coefficientRead]
  simp only [bind_tc_ok]
  rw [powerRun]
  simp only [bind_tc_ok]
  rw [addRun]
  simp only [bind_tc_ok]
  rw [coefficientUpdate]
  simp only [bind_tc_ok]
  rw [countRead]
  simp only [bind_tc_ok, Std.lift]
  rw [countSucc, countUpdate]
  simp only [bind_tc_ok]

private theorem phaseStep1
    (group : Std.U8) (alpha alpha2 alpha3 coefficient1 : RawQM31)
    (coefficient1Run : field.QM31.add field.QM31.ONE alpha3 =
      ok coefficient1) :
    sumcheck.fold_group_tuple_loop0.body
        (groupsAllSame group) (powers alpha alpha2 alpha3)
        (rangeFrom 1#usize) (unique1 group) coefficients1 (countsAt 1#u8)
        slots0 1#usize =
      ok (cont (rangeFrom 2#usize, unique1 group,
        coefficientsAt coefficient1, countsAt 2#u8, slots0, 1#usize)) := by
  apply phaseExistingStep group alpha alpha2 alpha3
    (rangeFrom 1#usize) (rangeFrom 2#usize) 1#usize field.QM31.ONE
    alpha3 coefficient1 1#u8 2#u8
  · simpa [rangeFrom] using rangeNext1
  · simpa [groupsAllSame] using arrayMake4Index1 group group group group
  · simpa [coefficientsAt] using arrayMake4Index0 field.QM31.ONE
      field.QM31.ZERO field.QM31.ZERO field.QM31.ZERO
  · simpa [powers] using arrayMake4Index1 field.QM31.ONE alpha3 alpha2 alpha
  · exact coefficient1Run
  · have setExact : (coefficientsAt field.QM31.ONE).set 0#usize coefficient1 =
        coefficientsAt coefficient1 := by apply Subtype.ext; rfl
    rw [← setExact]
    exact arrayUpdateExact (coefficientsAt field.QM31.ONE) 0#usize
      (by decide) coefficient1
  · simpa [countsAt] using arrayMake4Index0 1#u8 0#u8 0#u8 0#u8
  · exact u8OneSucc
  · have setExact : (countsAt 1#u8).set 0#usize 2#u8 = countsAt 2#u8 := by
      apply Subtype.ext; rfl
    rw [← setExact]
    exact arrayUpdateExact (countsAt 1#u8) 0#usize (by decide) 2#u8

private theorem phaseStep2
    (group : Std.U8) (alpha alpha2 alpha3 coefficient1 coefficient2 : RawQM31)
    (coefficient2Run : field.QM31.add coefficient1 alpha2 = ok coefficient2) :
    sumcheck.fold_group_tuple_loop0.body
        (groupsAllSame group) (powers alpha alpha2 alpha3)
        (rangeFrom 2#usize) (unique1 group) (coefficientsAt coefficient1)
        (countsAt 2#u8) slots0 1#usize =
      ok (cont (rangeFrom 3#usize, unique1 group,
        coefficientsAt coefficient2, countsAt 3#u8, slots0, 1#usize)) := by
  apply phaseExistingStep group alpha alpha2 alpha3
    (rangeFrom 2#usize) (rangeFrom 3#usize) 2#usize coefficient1
    alpha2 coefficient2 2#u8 3#u8
  · simpa [rangeFrom] using rangeNext2
  · simpa [groupsAllSame] using arrayMake4Index2 group group group group
  · simpa [coefficientsAt] using arrayMake4Index0 coefficient1
      field.QM31.ZERO field.QM31.ZERO field.QM31.ZERO
  · simpa [powers] using arrayMake4Index2 field.QM31.ONE alpha3 alpha2 alpha
  · exact coefficient2Run
  · have setExact : (coefficientsAt coefficient1).set 0#usize coefficient2 =
        coefficientsAt coefficient2 := by apply Subtype.ext; rfl
    rw [← setExact]
    exact arrayUpdateExact (coefficientsAt coefficient1) 0#usize
      (by decide) coefficient2
  · simpa [countsAt] using arrayMake4Index0 2#u8 0#u8 0#u8 0#u8
  · exact u8TwoSucc
  · have setExact : (countsAt 2#u8).set 0#usize 3#u8 = countsAt 3#u8 := by
      apply Subtype.ext; rfl
    rw [← setExact]
    exact arrayUpdateExact (countsAt 2#u8) 0#usize (by decide) 3#u8

private theorem phaseStep3
    (group : Std.U8) (alpha alpha2 alpha3 coefficient2 coefficient3 : RawQM31)
    (coefficient3Run : field.QM31.add coefficient2 alpha = ok coefficient3) :
    sumcheck.fold_group_tuple_loop0.body
        (groupsAllSame group) (powers alpha alpha2 alpha3)
        (rangeFrom 3#usize) (unique1 group) (coefficientsAt coefficient2)
        (countsAt 3#u8) slots0 1#usize =
      ok (cont (rangeFrom 4#usize, unique1 group,
        coefficientsAt coefficient3, countsAt 4#u8, slots0, 1#usize)) := by
  apply phaseExistingStep group alpha alpha2 alpha3
    (rangeFrom 3#usize) (rangeFrom 4#usize) 3#usize coefficient2
    alpha coefficient3 3#u8 4#u8
  · simpa [rangeFrom] using rangeNext3
  · simpa [groupsAllSame] using arrayMake4Index3 group group group group
  · simpa [coefficientsAt] using arrayMake4Index0 coefficient2
      field.QM31.ZERO field.QM31.ZERO field.QM31.ZERO
  · simpa [powers] using arrayMake4Index3 field.QM31.ONE alpha3 alpha2 alpha
  · exact coefficient3Run
  · have setExact : (coefficientsAt coefficient2).set 0#usize coefficient3 =
        coefficientsAt coefficient3 := by apply Subtype.ext; rfl
    rw [← setExact]
    exact arrayUpdateExact (coefficientsAt coefficient2) 0#usize
      (by decide) coefficient3
  · simpa [countsAt] using arrayMake4Index0 3#u8 0#u8 0#u8 0#u8
  · exact u8ThreeSucc
  · have setExact : (countsAt 3#u8).set 0#usize 4#u8 = countsAt 4#u8 := by
      apply Subtype.ext; rfl
    rw [← setExact]
    exact arrayUpdateExact (countsAt 3#u8) 0#usize (by decide) 4#u8

private theorem phaseDone
    (group : Std.U8) (alpha alpha2 alpha3 coefficient3 : RawQM31) :
    sumcheck.fold_group_tuple_loop0.body
        (groupsAllSame group) (powers alpha alpha2 alpha3)
        (rangeFrom 4#usize) (unique1 group) (coefficientsAt coefficient3)
        (countsAt 4#u8) slots0 1#usize =
      ok (done (unique1 group, coefficientsAt coefficient3,
        countsAt 4#u8, slots0, 1#usize)) := by
  unfold sumcheck.fold_group_tuple_loop0.body
  simp only [rangeFrom]
  rw [rangeDone4]
  rfl

private theorem phaseExact
    (group : Std.U8) (alpha alpha2 alpha3 coefficient1 coefficient2
      coefficient3 : RawQM31)
    (coefficient1Run : field.QM31.add field.QM31.ONE alpha3 = ok coefficient1)
    (coefficient2Run : field.QM31.add coefficient1 alpha2 = ok coefficient2)
    (coefficient3Run : field.QM31.add coefficient2 alpha = ok coefficient3) :
    sumcheck.fold_group_tuple_loop0 (rangeFrom 0#usize)
        (groupsAllSame group) (powers alpha alpha2 alpha3) unique0
        coefficients0 unique0 slots0 0#usize =
      ok (unique1 group, coefficientsAt coefficient3, countsAt 4#u8,
        slots0, 1#usize) := by
  unfold sumcheck.fold_group_tuple_loop0
  rw [loop.eq_1]
  dsimp only
  rw [phaseStep0]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [phaseStep1 group alpha alpha2 alpha3 coefficient1 coefficient1Run]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [phaseStep2 group alpha alpha2 alpha3 coefficient1 coefficient2
    coefficient2Run]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [phaseStep3 group alpha alpha2 alpha3 coefficient2 coefficient3
    coefficient3Run]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [phaseDone]

private theorem contributionStep
    (group : Std.U8) (groupValues : Slice RawQM31)
    (coefficient3 value contribution folded : RawQM31)
    (valueRun : Slice.index_usize groupValues (UScalar.cast .Usize group) =
      ok value)
    (contributionRun : field.QM31.mul value coefficient3 = ok contribution)
    (foldedRun : field.QM31.add field.QM31.ZERO contribution = ok folded) :
    sumcheck.fold_group_tuple_loop1.body groupValues (unique1 group)
        (coefficientsAt coefficient3) (countsAt 4#u8) slots0
        { start := 0#usize, «end» := 1#usize } field.QM31.ZERO =
      ok (cont ({ start := 1#usize, «end» := 1#usize }, folded)) := by
  have uniqueRead : Array.index_usize (unique1 group) 0#usize = ok group := by
    simpa [unique1] using arrayMake4Index0 group 0#u8 0#u8 0#u8
  have firstSlotRead : Array.index_usize slots0 0#usize = ok 0#u8 := by
    have run := arrayIndexRun slots0 0#usize (by decide)
    have valueExact : slots0.val[(0#usize).val]! = 0#u8 := by rfl
    rw [valueExact] at run
    exact run
  have countRead : Array.index_usize (countsAt 4#u8) 0#usize = ok 4#u8 := by
    simpa [countsAt] using arrayMake4Index0 4#u8 0#u8 0#u8 0#u8
  have coefficientRead : Array.index_usize (coefficientsAt coefficient3)
      0#usize = ok coefficient3 := by
    simpa [coefficientsAt] using arrayMake4Index0 coefficient3
      field.QM31.ZERO field.QM31.ZERO field.QM31.ZERO
  unfold sumcheck.fold_group_tuple_loop1.body
  rw [rangeNext0End1]
  simp only [bind_tc_ok]
  rw [uniqueRead]
  simp only [bind_tc_ok, Std.lift, fromU8ToUsizeExact, valueRun]
  rw [firstSlotRead]
  simp only [bind_tc_ok, ↓reduceIte]
  rw [countRead]
  simp only [bind_tc_ok, ↓reduceIte]
  rw [coefficientRead]
  simp only [bind_tc_ok]
  rw [contributionRun]
  simp only [bind_tc_ok]
  rw [foldedRun]
  rfl

private theorem contributionDone
    (group : Std.U8) (groupValues : Slice RawQM31)
    (coefficient3 folded : RawQM31) :
    sumcheck.fold_group_tuple_loop1.body groupValues (unique1 group)
        (coefficientsAt coefficient3) (countsAt 4#u8) slots0
        { start := 1#usize, «end» := 1#usize } folded =
      ok (done folded) := by
  unfold sumcheck.fold_group_tuple_loop1.body
  rw [rangeDone1]
  rfl

private theorem contributionExact
    (group : Std.U8) (groupValues : Slice RawQM31)
    (coefficient3 value contribution folded : RawQM31)
    (valueRun : Slice.index_usize groupValues (UScalar.cast .Usize group) =
      ok value)
    (contributionRun : field.QM31.mul value coefficient3 = ok contribution)
    (foldedRun : field.QM31.add field.QM31.ZERO contribution = ok folded) :
    sumcheck.fold_group_tuple_loop1
        { start := 0#usize, «end» := 1#usize } groupValues (unique1 group)
        (coefficientsAt coefficient3) (countsAt 4#u8) slots0
        field.QM31.ZERO = ok folded := by
  unfold sumcheck.fold_group_tuple_loop1
  rw [loop.eq_1]
  dsimp only
  rw [contributionStep group groupValues coefficient3 value contribution
    folded valueRun contributionRun foldedRun]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [contributionDone]

theorem allSameSourceExact
    (group : Std.U8) (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient1 coefficient2 coefficient3 value
      contribution folded half1 out : RawQM31)
    (coefficient1Run : field.QM31.add field.QM31.ONE alpha3 = ok coefficient1)
    (coefficient2Run : field.QM31.add coefficient1 alpha2 = ok coefficient2)
    (coefficient3Run : field.QM31.add coefficient2 alpha = ok coefficient3)
    (valueRun : Slice.index_usize groupValues (UScalar.cast .Usize group) =
      ok value)
    (contributionRun : field.QM31.mul value coefficient3 = ok contribution)
    (foldedRun : field.QM31.add field.QM31.ZERO contribution = ok folded)
    (half1Run : field.QM31.half folded = ok half1)
    (outRun : field.QM31.half half1 = ok out) :
    sumcheck.fold_group_tuple (groupsAllSame group) groupValues
      alpha alpha2 alpha3 = ok out := by
  have phaseRun := phaseExact group alpha alpha2 alpha3 coefficient1
    coefficient2 coefficient3 coefficient1Run coefficient2Run coefficient3Run
  have phaseRunExpanded :
      sumcheck.fold_group_tuple_loop0
          { start := 0#usize, «end» := 4#usize }
          (groupsAllSame group)
          (Array.make 4#usize [field.QM31.ONE, alpha3, alpha2, alpha])
          (Array.repeat 4#usize 0#u8)
          (Array.repeat 4#usize field.QM31.ZERO)
          (Array.repeat 4#usize 0#u8) (Array.repeat 4#usize 0#u8) 0#usize =
        ok (unique1 group, coefficientsAt coefficient3, countsAt 4#u8,
          slots0, 1#usize) := by
    simpa only [rangeFrom, powers, unique0, coefficients0, slots0] using
      phaseRun
  have contributionRunExact := contributionExact group groupValues coefficient3
    value contribution folded valueRun contributionRun foldedRun
  unfold sumcheck.fold_group_tuple
  dsimp only
  rw [phaseRunExpanded]
  simp only [bind_tc_ok]
  rw [contributionRunExact]
  simp only [bind_tc_ok]
  rw [half1Run]
  simp only [bind_tc_ok]
  exact outRun

theorem allSameProgramCorresponds
    (group : Std.U8) (groupValues : Slice RawQM31)
    (value alpha alpha2 alpha3 : RawQM31)
    (valueRun : Slice.index_usize groupValues (UScalar.cast .Usize group) =
      ok value)
    (hvalue : GeneratedCanonicalQM31 value)
    (halpha : GeneratedCanonicalQM31 alpha)
    (halpha2 : GeneratedCanonicalQM31 alpha2)
    (halpha3 : GeneratedCanonicalQM31 alpha3)
    (alpha2Exact : exactRaw alpha2 = exactRaw alpha ^ 2)
    (alpha3Exact : exactRaw alpha3 = exactRaw alpha ^ 3) :
    ∃ out,
      allSameProgram group groupValues alpha alpha2 alpha3 = ok out ∧
      GeneratedCanonicalQM31 out ∧
      exactRaw out =
        AspisV5FriRelationCandidateBridge.dualWeightFoldValue
          (exactRaw alpha) (fun _ => exactRaw value) := by
  obtain ⟨coefficient1, coefficient1Run, coefficient1Canonical,
      coefficient1Exact⟩ :=
    generated_qm31_add_corresponds field.QM31.ONE alpha3 oneCanonical halpha3
  obtain ⟨coefficient2, coefficient2Run, coefficient2Canonical,
      coefficient2Exact⟩ :=
    generated_qm31_add_corresponds coefficient1 alpha2 coefficient1Canonical
      halpha2
  obtain ⟨coefficient3, coefficient3Run, coefficient3Canonical,
      coefficient3Exact⟩ :=
    generated_qm31_add_corresponds coefficient2 alpha coefficient2Canonical
      halpha
  obtain ⟨contribution, contributionRun, contributionCanonical,
      contributionExact⟩ :=
    generated_qm31_mul_corresponds value coefficient3 hvalue
      coefficient3Canonical
  obtain ⟨folded, foldedRun, foldedCanonical, foldedExact⟩ :=
    generated_qm31_add_corresponds field.QM31.ZERO contribution
      zeroCanonical contributionCanonical
  obtain ⟨half1, half1Run, half1Canonical, half1Exact⟩ :=
    generated_qm31_half_corresponds folded foldedCanonical
  obtain ⟨out, outRun, outCanonical, outExact⟩ :=
    generated_qm31_half_corresponds half1 half1Canonical
  refine ⟨out, ?_, outCanonical, ?_⟩
  · simp [allSameProgram, coefficient1Run, coefficient2Run, coefficient3Run,
      valueRun, contributionRun, foldedRun, half1Run, outRun]
  · have coefficient1ExactM := congrArg sourceQm31ToModel coefficient1Exact
    have coefficient2ExactM := congrArg sourceQm31ToModel coefficient2Exact
    have coefficient3ExactM := congrArg sourceQm31ToModel coefficient3Exact
    have contributionExactM := congrArg sourceQm31ToModel contributionExact
    have foldedExactM := congrArg sourceQm31ToModel foldedExact
    have half1ExactM := congrArg sourceQm31ToModel half1Exact
    have outExactM := congrArg sourceQm31ToModel outExact
    simp only [sourceQm31ToModel_generated, sourceQm31ToModel_add,
      sourceQm31ToModel_mul] at coefficient1ExactM
    simp only [sourceQm31ToModel_generated, sourceQm31ToModel_add,
      sourceQm31ToModel_mul] at coefficient2ExactM
    simp only [sourceQm31ToModel_generated, sourceQm31ToModel_add,
      sourceQm31ToModel_mul] at coefficient3ExactM
    simp only [sourceQm31ToModel_generated, sourceQm31ToModel_add,
      sourceQm31ToModel_mul] at contributionExactM
    simp only [sourceQm31ToModel_generated, sourceQm31ToModel_add,
      sourceQm31ToModel_mul] at foldedExactM
    simp only [sourceQm31ToModel_generated, sourceQm31ToModel_add,
      sourceQm31ToModel_mul] at half1ExactM
    simp only [sourceQm31ToModel_generated, sourceQm31ToModel_add,
      sourceQm31ToModel_mul] at outExactM
    have oneExact : exactRaw field.QM31.ONE = 1 := by
      rw [field.QM31.ONE]
      rfl
    have zeroExact : exactRaw field.QM31.ZERO = 0 := by
      rw [field.QM31.ZERO]
      rfl
    have fourNonzero : (4 : ExactQM31) ≠ 0 := by decide
    apply (eq_div_iff fourNonzero).2
    simp
    calc
      exactRaw out * 4 =
          (exactRaw out + exactRaw out) +
            (exactRaw out + exactRaw out) := by ring
      _ = exactRaw half1 + exactRaw half1 := by rw [outExactM]
      _ = exactRaw folded := half1ExactM
      _ = exactRaw field.QM31.ZERO + exactRaw contribution := foldedExactM
      _ = exactRaw value * exactRaw coefficient3 := by
        rw [zeroExact, contributionExactM]
        ring
      _ = exactRaw value *
          (((1 : ExactQM31) + exactRaw alpha ^ 3) +
            exactRaw alpha ^ 2 + exactRaw alpha) := by
        rw [coefficient3ExactM, coefficient2ExactM, coefficient1ExactM,
          oneExact, alpha2Exact, alpha3Exact]
      _ = exactRaw value + exactRaw alpha ^ 3 * exactRaw value +
          exactRaw alpha ^ 2 * exactRaw value +
          exactRaw alpha * exactRaw value := by ring

theorem allSameSourceCorresponds
    (group : Std.U8) (groupValues : Slice RawQM31)
    (value alpha alpha2 alpha3 : RawQM31)
    (valueRun : Slice.index_usize groupValues (UScalar.cast .Usize group) =
      ok value)
    (hvalue : GeneratedCanonicalQM31 value)
    (halpha : GeneratedCanonicalQM31 alpha)
    (halpha2 : GeneratedCanonicalQM31 alpha2)
    (halpha3 : GeneratedCanonicalQM31 alpha3)
    (alpha2Exact : exactRaw alpha2 = exactRaw alpha ^ 2)
    (alpha3Exact : exactRaw alpha3 = exactRaw alpha ^ 3) :
    ∃ out,
      sumcheck.fold_group_tuple (groupsAllSame group) groupValues
          alpha alpha2 alpha3 = ok out ∧
      GeneratedCanonicalQM31 out ∧
      exactRaw out =
        AspisV5FriRelationCandidateBridge.dualWeightFoldValue
          (exactRaw alpha) (fun _ => exactRaw value) := by
  obtain ⟨coefficient1, coefficient1Run, coefficient1Canonical, _⟩ :=
    generated_qm31_add_corresponds field.QM31.ONE alpha3 oneCanonical halpha3
  obtain ⟨coefficient2, coefficient2Run, coefficient2Canonical, _⟩ :=
    generated_qm31_add_corresponds coefficient1 alpha2 coefficient1Canonical
      halpha2
  obtain ⟨coefficient3, coefficient3Run, coefficient3Canonical, _⟩ :=
    generated_qm31_add_corresponds coefficient2 alpha coefficient2Canonical
      halpha
  obtain ⟨contribution, contributionRun, contributionCanonical, _⟩ :=
    generated_qm31_mul_corresponds value coefficient3 hvalue
      coefficient3Canonical
  obtain ⟨folded, foldedRun, foldedCanonical, _⟩ :=
    generated_qm31_add_corresponds field.QM31.ZERO contribution
      zeroCanonical contributionCanonical
  obtain ⟨half1, half1Run, half1Canonical, _⟩ :=
    generated_qm31_half_corresponds folded foldedCanonical
  obtain ⟨out, outRun, _, _⟩ :=
    generated_qm31_half_corresponds half1 half1Canonical
  have sourceRun := allSameSourceExact group groupValues alpha alpha2 alpha3
    coefficient1 coefficient2 coefficient3 value contribution folded half1 out
    coefficient1Run coefficient2Run coefficient3Run valueRun contributionRun
    foldedRun half1Run outRun
  have programRun : allSameProgram group groupValues alpha alpha2 alpha3 =
      ok out := by
    simp [allSameProgram, coefficient1Run, coefficient2Run, coefficient3Run,
      valueRun, contributionRun, foldedRun, half1Run, outRun]
  obtain ⟨programOut, programOutRun, programOutCanonical, programOutExact⟩ :=
    allSameProgramCorresponds group groupValues value alpha alpha2 alpha3
      valueRun hvalue halpha halpha2 halpha3 alpha2Exact alpha3Exact
  rw [programRun] at programOutRun
  have outEq : out = programOut := by injection programOutRun
  subst programOut
  exact ⟨out, sourceRun, programOutCanonical, programOutExact⟩

#print axioms findEmpty
#print axioms findExisting
#print axioms phaseStep0
#print axioms allSameSourceExact
#print axioms allSameSourceCorresponds
end V7CallerCurrentReleaseR26GroupedAllSame
