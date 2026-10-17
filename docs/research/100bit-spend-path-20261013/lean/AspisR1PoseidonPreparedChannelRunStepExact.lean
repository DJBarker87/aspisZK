import PoseidonPreparedChannelLoopStep
import ExtractedMaskM31AddSub

set_option autoImplicit false
namespace AspisR1PoseidonPreparedChannelRunStepExact
open Aeneas Aeneas.Std Result WP
open AspisR1SelectedMaskProbe

abbrev U64 := UScalar UScalarTy.U64
abbrev P : Nat := 2147483647
abbrev Sums := Array (Array U64 3#usize) 3#usize
abbrev PreparedArray := Array field.PreparedQm31Multiplier 3#usize
abbrev ComponentArray := Array (Array field.M31 3#usize) 3#usize


private def commit (sumRow : Array U64 3#usize) (channel : Std.Usize)
    (mutBack : Array U64 3#usize → Sums) (value : U64) : Result Sums := do
  let rowOut ← Array.update sumRow channel value
  .ok (mutBack rowOut)

private theorem inlineScalar_bind
    (leftWord rightWord : field.M31) (acc : U64)
    (sumRow : Array U64 3#usize) (channel : Std.Usize)
    (mutBack : Array U64 3#usize → Sums) :
    (do
      let i ← lift (UScalar.cast .U64 leftWord)
      let i1 ← lift (UScalar.cast .U64 rightWord)
      let i2 ← i * i1
      let updated ← acc + i2
      commit sumRow channel mutBack updated) =
    (do
      let updated ← AspisR1PoseidonPreparedChannelGeneratedStep.generatedChannelUpdate
        leftWord rightWord acc
      commit sumRow channel mutBack updated) := by
  simp [AspisR1PoseidonPreparedChannelGeneratedStep.generatedChannelUpdate,
    commit, bind_assoc_eq]

/-- Exact execution of one generated channel-loop body, parameterized only by
its checked array reads. The later traversal theorem discharges these reads
from the fixed-size arrays and the iterator's channel index. -/
theorem runStep_success
    (left : PreparedArray) (sums : Sums) (index : Std.Usize)
    (right : ComponentArray) (component channel : Std.Usize)
    (pqm : field.PreparedQm31Multiplier)
    (leftRow rightRow : Array field.M31 3#usize)
    (leftWord rightWord : field.M31)
    (sumRow : Array U64 3#usize) (acc : U64)
    (mutBack : Array U64 3#usize → Sums)
    (hleft0 : Array.index_usize left index = .ok pqm)
    (hleft1 : Array.index_usize pqm.components component = .ok leftRow)
    (hleft2 : Array.index_usize leftRow channel = .ok leftWord)
    (hright0 : Array.index_usize right component = .ok rightRow)
    (hright1 : Array.index_usize rightRow channel = .ok rightWord)
    (hsums0 : Array.index_usize sums component = .ok sumRow)
    (hsums1 : Array.index_usize sumRow channel = .ok acc)
    (hmut : Array.index_mut_usize sums component = .ok (sumRow, mutBack))
    (hleftCanonical : leftWord.val < P) (hrightCanonical : rightWord.val < P)
    (hacc : acc.val ≤ 2 * (P - 1) ^ 2)
    (hchannel : channel.val < 3) :
    ∃ updated : U64, ∃ out : Sums,
      AspisR1PoseidonPreparedChannelGeneratedStep.generatedChannelUpdate leftWord rightWord acc = .ok updated ∧
      AspisR1PoseidonPreparedChannelLoopStep.runStep left sums index right component channel = .ok out ∧
      updated.val = acc.val + leftWord.val * rightWord.val ∧
      out = mutBack (sumRow.set channel updated) := by
  obtain ⟨updated, hupd, hvalue⟩ :=
    AspisR1PoseidonPreparedChannelGeneratedStep.generatedChannelUpdate_success
      leftWord rightWord acc hleftCanonical hrightCanonical hacc
  have hgen : (do
      let i ← lift (UScalar.cast .U64 leftWord)
      let i1 ← lift (UScalar.cast .U64 rightWord)
      let i2 ← i * i1
      acc + i2) = .ok updated := by
    change AspisR1PoseidonPreparedChannelGeneratedStep.generatedChannelUpdate
      leftWord rightWord acc = .ok updated at hupd
    simpa [AspisR1PoseidonPreparedChannelGeneratedStep.generatedChannelUpdate] using hupd
  have harray : ∃ rowOut : Array U64 3#usize,
      Array.update sumRow channel updated = .ok rowOut ∧
      rowOut = sumRow.set channel updated := by
    apply WP.spec_imp_exists
    apply Array.update_spec
    simpa [sumRow.property] using hchannel
  obtain ⟨rowOut, harrayRun, harraySet⟩ := harray
  refine ⟨updated, mutBack rowOut, hupd, ?_, hvalue, ?_⟩
  · rw [AspisR1PoseidonPreparedChannelLoopStep.runStep]
    simp only [hleft0, hleft1, hleft2, hright0, hright1, hsums0, hsums1, hmut, bind_tc_ok]
    change (do
      let i ← lift (UScalar.cast .U64 leftWord)
      let i1 ← lift (UScalar.cast .U64 rightWord)
      let i2 ← i * i1
      let updated ← acc + i2
      commit sumRow channel mutBack updated) = .ok (mutBack rowOut)
    rw [inlineScalar_bind, hupd]
    simp [commit, harrayRun]

  · rw [harraySet]

#print axioms runStep_success
end AspisR1PoseidonPreparedChannelRunStepExact
