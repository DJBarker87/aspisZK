import V7CallerCurrentReleaseR26FieldBridge

/-!
# Exact reconstruction for the current optimized QM31 dot product

The optimized source accumulates nine M31 Karatsuba channels.  This file
proves the final source reconstruction independently of the accumulation
loops, keeping the later loop invariants small.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26Qm31DotReconstruction

open V7CallerCurrentReleaseR26FieldBridge

abbrev M31 := field.M31
abbrev CM31 := field.CM31
abbrev QM31 := field.QM31
abbrev ExactM31 := V7CallerCurrentReleaseR26FieldBridge.ExactM31
abbrev ExactCM31 := V7CallerCurrentReleaseR26FieldBridge.ExactCM31
abbrev ExactQM31 := V7CallerCurrentReleaseR26FieldBridge.ExactQM31

local instance : Inhabited M31 := ⟨field.M31.ZERO⟩

def CanonicalDotChannels (sums : Array M31 9#usize) : Prop :=
  ∀ channel, channel < 9 → GeneratedCanonicalM31 sums.val[channel]!

def exactDotComponent (sums : Array M31 9#usize) (offset : Nat) : ExactCM31 :=
  ⟨generatedM31ToExact sums.val[offset]! -
      generatedM31ToExact sums.val[offset + 1]!,
    generatedM31ToExact sums.val[offset + 2]! -
      generatedM31ToExact sums.val[offset]! -
      generatedM31ToExact sums.val[offset + 1]!⟩

def exactQm31FromDotChannels (sums : Array M31 9#usize) : ExactQM31 :=
  ⟨exactDotComponent sums 0 +
      exactDotComponent sums 3 * exactQm31R,
    exactDotComponent sums 6 - exactDotComponent sums 0 -
      exactDotComponent sums 3⟩

private theorem array_index_run {T : Type} [Inhabited T]
    {n : Std.Usize} (values : Array T n) (index : Std.Usize)
    (bound : index.val < values.length) :
    Array.index_usize values index = ok values.val[index.val]! := by
  obtain ⟨value, run, exact⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.index_usize_spec values index (by
      exact bound))
  have listExact : values.val[index.val] = values.val[index.val]! := by
    symm
    apply List.getElem!_of_getElem?
    simpa using bound
  simpa [exact, listExact] using run

private theorem wrapping_add_small
    (offset delta : Std.Usize)
    (bound : offset.val + delta.val < Usize.size) :
    (Std.Usize.wrapping_add offset delta).val = offset.val + delta.val := by
  rw [Std.Usize.wrapping_add_val_eq]
  norm_num
  exact Nat.mod_eq_of_lt bound

/-- Calling the generated closure at any valid three-channel offset returns
the exact CM31 Karatsuba reconstruction. -/
theorem generated_dot_component_corresponds
    (sums : Array M31 9#usize) (offset : Std.Usize)
    (offsetBound : offset.val + 2 < 9)
    (canonical : CanonicalDotChannels sums) :
    ∃ out : CM31,
      field.qm31_dot.closure.Insts.CoreOpsFunctionFnTupleUsizeCM31.call
          sums offset = ok out ∧
      GeneratedCanonicalCM31 out ∧
      generatedCm31ToExact out = exactDotComponent sums offset.val := by
  have offsetOneBound : offset.val + 1 < 9 := by omega
  have offsetTwoBound : offset.val + 2 < 9 := offsetBound
  have nineSize : 9 < Usize.size := by
    have literalBound := UScalar.hSize (9#usize)
    simpa [UScalar.size_UScalarTyUsize] using literalBound
  have offsetSize : offset.val + 1 < Usize.size := by
    omega
  have offsetTwoSize : offset.val + 2 < Usize.size := by
    omega
  let offsetOne := Std.Usize.wrapping_add offset 1#usize
  let offsetTwo := Std.Usize.wrapping_add offset 2#usize
  have offsetOneVal : offsetOne.val = offset.val + 1 := by
    exact wrapping_add_small offset 1#usize (by simpa using offsetSize)
  have offsetTwoVal : offsetTwo.val = offset.val + 2 := by
    exact wrapping_add_small offset 2#usize (by simpa using offsetTwoSize)
  have readZero := array_index_run sums offset (by
    simpa [Array.length_eq] using (show offset.val < 9 by omega))
  have readOne := array_index_run sums offsetOne (by
    rw [offsetOneVal]
    simpa [Array.length_eq] using offsetOneBound)
  have readTwo := array_index_run sums offsetTwo (by
    rw [offsetTwoVal]
    simpa [Array.length_eq] using offsetTwoBound)
  let zero := sums.val[offset.val]!
  let one := sums.val[offset.val + 1]!
  let two := sums.val[offset.val + 2]!
  have readOneExact : Array.index_usize sums offsetOne = ok one := by
    simpa [one, offsetOneVal] using readOne
  have readTwoExact : Array.index_usize sums offsetTwo = ok two := by
    simpa [two, offsetTwoVal] using readTwo
  have zeroCanonical : GeneratedCanonicalM31 zero :=
    canonical offset.val (by omega)
  have oneCanonical : GeneratedCanonicalM31 one :=
    canonical (offset.val + 1) offsetOneBound
  have twoCanonical : GeneratedCanonicalM31 two :=
    canonical (offset.val + 2) offsetTwoBound
  obtain ⟨real, realRun, realCanonical, realExact⟩ :=
    generated_m31_sub_corresponds zero one zeroCanonical oneCanonical
  obtain ⟨imagPartial, imagPartialRun, imagPartialCanonical,
      imagPartialExact⟩ :=
    generated_m31_sub_corresponds two zero twoCanonical zeroCanonical
  obtain ⟨imag, imagRun, imagCanonical, imagExact⟩ :=
    generated_m31_sub_corresponds imagPartial one
      imagPartialCanonical oneCanonical
  refine ⟨⟨real, imag⟩, ?_, ⟨realCanonical, imagCanonical⟩, ?_⟩
  · unfold field.qm31_dot.closure.Insts.CoreOpsFunctionFnTupleUsizeCM31.call
    rw [readZero]
    simp only [bind_tc_ok, Std.lift]
    change
      (do
        let m1 ← Array.index_usize sums offsetOne
        let m2 ← field.M31.sub zero m1
        let m3 ← Array.index_usize sums offsetTwo
        let m4 ← field.M31.sub m3 zero
        let m5 ← Array.index_usize sums offsetOne
        let m6 ← field.M31.sub m4 m5
        ok ({ a := m2, b := m6 } : CM31)) = _
    rw [readOneExact]
    simp only [bind_tc_ok]
    rw [realRun, readTwoExact]
    simp only [bind_tc_ok]
    rw [imagPartialRun]
    simp only [bind_tc_ok]
    rw [imagRun]
    simp
  · apply QuadraticAlgebra.ext
    · change generatedM31ToExact real =
        generatedM31ToExact zero - generatedM31ToExact one
      simpa [generatedM31ToExact] using realExact
    · change generatedM31ToExact imag =
        generatedM31ToExact two - generatedM31ToExact zero -
          generatedM31ToExact one
      calc
        generatedM31ToExact imag =
            generatedM31ToExact imagPartial - generatedM31ToExact one := by
          simpa [generatedM31ToExact] using imagExact
        _ = (generatedM31ToExact two - generatedM31ToExact zero) -
              generatedM31ToExact one := by
          rw [show generatedM31ToExact imagPartial =
              generatedM31ToExact two - generatedM31ToExact zero by
            simpa [generatedM31ToExact] using imagPartialExact]

/-- The literal final sequence in `qm31_dot` reconstructs the exact QM31
value represented by its nine canonical channels. -/
theorem generated_dot_reconstruction_corresponds
    (sums : Array M31 9#usize) (canonical : CanonicalDotChannels sums) :
    (do
      let m0 ←
        field.qm31_dot.closure.Insts.CoreOpsFunctionFnTupleUsizeCM31.call
          sums 0#usize
      let m1 ←
        field.qm31_dot.closure.Insts.CoreOpsFunctionFnTupleUsizeCM31.call
          sums 3#usize
      let m2 ←
        field.qm31_dot.closure.Insts.CoreOpsFunctionFnTupleUsizeCM31.call
          sums 6#usize
      let c ← field.mul_by_r m1
      let c1 ← field.CM31.add m0 c
      let c2 ← field.CM31.sub m2 m0
      let c3 ← field.CM31.sub c2 m1
      ok ({ c0 := c1, c1 := c3 } : QM31))
      ⦃ out => GeneratedCanonicalQM31 out ∧
        generatedQm31ToExact out = exactQm31FromDotChannels sums ⦄ := by
  obtain ⟨m0, m0Run, m0Canonical, m0Exact⟩ :=
    generated_dot_component_corresponds sums 0#usize (by norm_num) canonical
  obtain ⟨m1, m1Run, m1Canonical, m1Exact⟩ :=
    generated_dot_component_corresponds sums 3#usize (by norm_num) canonical
  obtain ⟨m2, m2Run, m2Canonical, m2Exact⟩ :=
    generated_dot_component_corresponds sums 6#usize (by norm_num) canonical
  obtain ⟨rm1, rm1Run, rm1Canonical, rm1Exact⟩ :=
    generated_mul_by_r_corresponds m1 m1Canonical
  obtain ⟨low, lowRun, lowCanonical, lowExact⟩ :=
    generated_cm31_add_corresponds m0 rm1 m0Canonical rm1Canonical
  obtain ⟨highPartial, highPartialRun, highPartialCanonical,
      highPartialExact⟩ :=
    generated_cm31_sub_corresponds m2 m0 m2Canonical m0Canonical
  obtain ⟨high, highRun, highCanonical, highExact⟩ :=
    generated_cm31_sub_corresponds highPartial m1
      highPartialCanonical m1Canonical
  rw [m0Run]
  simp only [bind_tc_ok]
  rw [m1Run]
  simp only [bind_tc_ok]
  rw [m2Run]
  simp only [bind_tc_ok]
  rw [rm1Run]
  simp only [bind_tc_ok]
  rw [lowRun]
  simp only [bind_tc_ok]
  rw [highPartialRun]
  simp only [bind_tc_ok]
  rw [highRun]
  simp only [bind_tc_ok, Aeneas.Std.WP.spec_ok]
  refine ⟨⟨lowCanonical, highCanonical⟩, ?_⟩
  unfold exactQm31FromDotChannels
  apply QuadraticAlgebra.ext
  · change generatedCm31ToExact low = _
    rw [lowExact, rm1Exact, m0Exact, m1Exact]
    rfl
  · change generatedCm31ToExact high = _
    rw [highExact, highPartialExact, m2Exact, m0Exact, m1Exact]
    rfl

#print axioms generated_dot_component_corresponds
#print axioms generated_dot_reconstruction_corresponds

end V7CallerCurrentReleaseR26Qm31DotReconstruction
