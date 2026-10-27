import RPu_AspisR1PoseidonPreparedChannelArraySpecs
import RPu_AspisR1PoseidonPreparedChannelRunStepExact

set_option autoImplicit false
namespace AspisR1PoseidonPreparedChannelRunStepArrays
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe

abbrev U64 := UScalar UScalarTy.U64
abbrev P : Nat := 2147483647
abbrev Sums := Array (Array U64 3#usize) 3#usize
abbrev PreparedArray := Array field.PreparedQm31Multiplier 3#usize
abbrev ComponentArray := Array (Array field.M31 3#usize) 3#usize

/-- The generated one-channel body with the real mutable-index setter obtained
from the Aeneas array spec. The remaining checked reads are explicit so the
traversal induction can supply their exact finite-index witnesses. -/
theorem runStep_success
    (left : PreparedArray) (sums : Sums) (index : Std.Usize)
    (right : ComponentArray) (component channel : Std.Usize)
    (pqm : field.PreparedQm31Multiplier)
    (leftRow rightRow : Array field.M31 3#usize)
    (leftWord rightWord : field.M31)
    (sumRow : Array U64 3#usize) (acc : U64)
    (hleft0 : Array.index_usize left index = .ok pqm)
    (hleft1 : Array.index_usize pqm.components component = .ok leftRow)
    (hleft2 : Array.index_usize leftRow channel = .ok leftWord)
    (hright0 : Array.index_usize right component = .ok rightRow)
    (hright1 : Array.index_usize rightRow channel = .ok rightWord)
    (hsums0 : Array.index_usize sums component = .ok sumRow)
    (hsums1 : Array.index_usize sumRow channel = .ok acc)
    (hleftCanonical : leftWord.val < P) (hrightCanonical : rightWord.val < P)
    (hacc : acc.val ≤ 2 * (P - 1) ^ 2)
    (hcomponent : component.val < 3) (hchannel : channel.val < 3) :
    ∃ updated : U64, ∃ out : Sums,
      AspisR1PoseidonPreparedChannelGeneratedStep.generatedChannelUpdate leftWord rightWord acc = .ok updated ∧
      AspisR1PoseidonPreparedChannelLoopStep.runStep left sums index right component channel = .ok out ∧
      updated.val = acc.val + leftWord.val * rightWord.val ∧
      out = sums.set component (sumRow.set channel updated) := by
  obtain ⟨mutRow, mutBack, hmut0, hmutRow, hmutBack⟩ :=
    AspisR1PoseidonPreparedChannelArraySpecs.index_mut_ok sums component hcomponent
  obtain ⟨readRow, hreadRow, hreadValue⟩ :=
    AspisR1PoseidonPreparedChannelArraySpecs.index_ok sums component hcomponent
  have hreadEq : readRow = sumRow := Result.ok.inj (hreadRow.symm.trans hsums0)
  have hmutRowEq : mutRow = sumRow := hmutRow.trans hreadValue.symm |>.trans hreadEq
  have hmut : Array.index_mut_usize sums component =
      .ok (sumRow, fun row => sums.set component row) := by
    simpa [hmutRowEq, hmutBack] using hmut0
  obtain ⟨updated, out, hupd, hrun, hval, hout⟩ :=
    AspisR1PoseidonPreparedChannelRunStepExact.runStep_success
      left sums index right component channel pqm leftRow rightRow leftWord rightWord
      sumRow acc (fun row => sums.set component row)
      hleft0 hleft1 hleft2 hright0 hright1 hsums0 hsums1 hmut
      hleftCanonical hrightCanonical hacc hchannel
  exact ⟨updated, out, hupd, hrun, hval, by simpa using hout⟩

#print axioms runStep_success
end AspisR1PoseidonPreparedChannelRunStepArrays
