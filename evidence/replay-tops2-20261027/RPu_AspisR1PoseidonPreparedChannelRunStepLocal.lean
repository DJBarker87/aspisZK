import RPu_AspisR1PoseidonPreparedChannelRunStepArrays
import RPu_AspisR1PoseidonPreparedChannelArraySpecs

set_option autoImplicit false
namespace AspisR1PoseidonPreparedChannelRunStepLocal
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe

abbrev U64 := UScalar UScalarTy.U64
abbrev P : Nat := 2147483647
abbrev Sums := Array (Array U64 3#usize) 3#usize
abbrev PreparedArray := Array field.PreparedQm31Multiplier 3#usize
abbrev ComponentArray := Array (Array field.M31 3#usize) 3#usize

def at3 {α : Type} (a : Array α 3#usize) (i : Std.Usize) (hi : i.val < 3) : α :=
  a.val[i.val]'(by simpa [a.property] using hi)

/-- All array reads and the index-mut back closure for one source channel step
are derived from Aeneas specs. Only semantic word bounds and the accumulator
bound remain as invariant inputs. -/
theorem runStep_success
    (left : PreparedArray) (sums : Sums) (index : Std.Usize)
    (right : ComponentArray) (component channel : Std.Usize)
    (hindex : index.val < 3) (hcomponent : component.val < 3)
    (hchannel : channel.val < 3)
    (hleftCanonical : (at3 (at3 (at3 left index hindex).components component hcomponent) channel hchannel).val < P)
    (hrightCanonical : (at3 (at3 right component hcomponent) channel hchannel).val < P)
    (haccBound : (at3 (at3 sums component hcomponent) channel hchannel).val ≤ 2 * (P - 1) ^ 2) :
    ∃ updated : U64, ∃ out : Sums,
      AspisR1PoseidonPreparedChannelLoopStep.runStep left sums index right component channel = .ok out ∧
      updated.val = (at3 (at3 sums component hcomponent) channel hchannel).val +
        (at3 (at3 (at3 left index hindex).components component hcomponent) channel hchannel).val *
        (at3 (at3 right component hcomponent) channel hchannel).val ∧
      out = sums.set component ((at3 sums component hcomponent).set channel updated) := by
  obtain ⟨pqm, hleft0, hpqm⟩ := AspisR1PoseidonPreparedChannelArraySpecs.index_ok left index hindex
  obtain ⟨leftRow, hleft1, hleftRow⟩ :=
    AspisR1PoseidonPreparedChannelArraySpecs.index_ok pqm.components component hcomponent
  obtain ⟨leftWord, hleft2, hleftWord⟩ :=
    AspisR1PoseidonPreparedChannelArraySpecs.index_ok leftRow channel hchannel
  obtain ⟨rightRow, hright0, hrightRow⟩ :=
    AspisR1PoseidonPreparedChannelArraySpecs.index_ok right component hcomponent
  obtain ⟨rightWord, hright1, hrightWord⟩ :=
    AspisR1PoseidonPreparedChannelArraySpecs.index_ok rightRow channel hchannel
  obtain ⟨sumRow, hsums0, hsumRow⟩ :=
    AspisR1PoseidonPreparedChannelArraySpecs.index_ok sums component hcomponent
  obtain ⟨acc, hsums1, hacc⟩ :=
    AspisR1PoseidonPreparedChannelArraySpecs.index_ok sumRow channel hchannel
  have hleftRow' : leftRow = at3 pqm.components component hcomponent := by
    simpa [at3] using hleftRow
  have hpqm' : pqm = at3 left index hindex := by
    simpa [at3] using hpqm
  have hleftWord' : leftWord = at3 leftRow channel hchannel := by
    simpa [at3] using hleftWord
  have hrightRow' : rightRow = at3 right component hcomponent := by
    simpa [at3] using hrightRow
  have hrightWord' : rightWord = at3 rightRow channel hchannel := by
    simpa [at3] using hrightWord
  have hsumRow' : sumRow = at3 sums component hcomponent := by
    simpa [at3] using hsumRow
  have hacc' : acc = at3 sumRow channel hchannel := by
    simpa [at3] using hacc
  have hleftWordEq : leftWord =
      at3 (at3 (at3 left index hindex).components component hcomponent) channel hchannel := by
    calc
      leftWord = at3 leftRow channel hchannel := hleftWord'
      _ = at3 (at3 pqm.components component hcomponent) channel hchannel := by rw [hleftRow']
      _ = at3 (at3 (at3 left index hindex).components component hcomponent) channel hchannel := by rw [hpqm']
  have hrightWordEq : rightWord = at3 (at3 right component hcomponent) channel hchannel := by
    calc
      rightWord = at3 rightRow channel hchannel := hrightWord'
      _ = at3 (at3 right component hcomponent) channel hchannel := by rw [hrightRow']
  have haccEq : acc = at3 (at3 sums component hcomponent) channel hchannel := by
    calc
      acc = at3 sumRow channel hchannel := hacc'
      _ = at3 (at3 sums component hcomponent) channel hchannel := by rw [hsumRow']
  have hlcan : leftWord.val < P := by
    rw [hleftWordEq]
    exact hleftCanonical
  have hrcan : rightWord.val < P := by
    rw [hrightWordEq]
    exact hrightCanonical
  have hac : acc.val ≤ 2 * (P - 1) ^ 2 := by
    rw [haccEq]
    exact haccBound
  obtain ⟨updated, out, hupd, hrun, hvalue, hout⟩ :=
    AspisR1PoseidonPreparedChannelRunStepArrays.runStep_success
      left sums index right component channel pqm leftRow rightRow leftWord rightWord
      sumRow acc hleft0 hleft1 hleft2 hright0 hright1 hsums0 hsums1 hlcan hrcan hac
      hcomponent hchannel
  have houtvalue : updated.val =
      (at3 (at3 sums component hcomponent) channel hchannel).val +
        (at3 (at3 (at3 left index hindex).components component hcomponent) channel hchannel).val *
        (at3 (at3 right component hcomponent) channel hchannel).val := by
    rw [← haccEq, ← hleftWordEq, ← hrightWordEq]
    exact hvalue
  have houtarray : out = sums.set component ((at3 sums component hcomponent).set channel updated) := by
    rw [← hsumRow']
    exact hout
  exact ⟨updated, out, hrun, houtvalue, houtarray⟩

#print axioms runStep_success
end AspisR1PoseidonPreparedChannelRunStepLocal
