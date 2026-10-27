import RPu_AspisR1PoseidonPreparedChannelNestedSet

set_option autoImplicit false
namespace AspisR1PoseidonPreparedChannelUpdateInvariantV2
open Aeneas.Std
abbrev U64 := UScalar UScalarTy.U64
abbrev at3 {α : Type} (a : Array α 3#usize) (i : Usize) (hi : i.val < 3) : α :=
  AspisR1PoseidonPreparedChannelArraySet.at3 a i hi

abbrev Sums := Array (Array U64 3#usize) 3#usize

def sumCell (sums : Sums) (component channel : Usize)
    (hc : component.val < 3) (hch : channel.val < 3) : U64 :=
  at3 (at3 sums component hc) channel hch

def updateComponent (sums : Sums) (component channel : Usize)
    (updated : U64) (hc : component.val < 3) : Sums :=
  sums.set component ((at3 sums component hc).set channel updated)

/-- The nested setter changes exactly the current cell. This pure invariant
step is independent of the generated iterator and is used by its fuel proof. -/
theorem update_invariants
    (sums initial : Sums) (component channel : Usize) (updated : U64)
    (hc : component.val < 3) (hchannel : channel.val < 3)
    (product : (ch : Usize) → ch.val < 3 → Nat)
    (hcurrent : sumCell sums component channel hc hchannel =
      sumCell initial component channel hc hchannel)
    (hupdated : updated.val = (sumCell sums component channel hc hchannel).val + product channel hchannel)
    (hprocessed : ∀ (ch : Usize) (hch : ch.val < 3), ch.val < channel.val →
      (sumCell sums component ch hc hch).val =
        (sumCell initial component ch hc hch).val + product ch hch)
    (hremaining : ∀ (ch : Usize) (hch : ch.val < 3), channel.val ≤ ch.val →
      sumCell sums component ch hc hch = sumCell initial component ch hc hch)
    (hframe : ∀ (c : Usize) (hcc : c.val < 3), c.val ≠ component.val →
      ∀ (ch : Usize) (hch : ch.val < 3),
        sumCell sums c ch hcc hch = sumCell initial c ch hcc hch) :
    (∀ (ch : Usize) (hch : ch.val < 3), ch.val < channel.val + 1 →
      (sumCell (updateComponent sums component channel updated hc)
        component ch hc hch).val =
        (sumCell initial component ch hc hch).val + product ch hch) ∧
    (∀ (ch : Usize) (hch : ch.val < 3), channel.val + 1 ≤ ch.val →
      sumCell (updateComponent sums component channel updated hc)
        component ch hc hch = sumCell initial component ch hc hch) ∧
    (∀ (c : Usize) (hcc : c.val < 3), c.val ≠ component.val →
      ∀ (ch : Usize) (hch : ch.val < 3),
        sumCell (updateComponent sums component channel updated hc)
          c ch hcc hch = sumCell initial c ch hcc hch) := by
  have hselected : ∀ (ch : Usize) (hch : ch.val < 3),
      sumCell (updateComponent sums component channel updated hc) component ch hc hch =
        if ch.val = channel.val then updated else sumCell sums component ch hc hch := by
    intro ch hch
    have hnest := AspisR1PoseidonPreparedChannelNestedSet.cell_nested_set
      sums component channel component ch (at3 sums component hc) updated
      hc hchannel hc hch rfl
    simpa [sumCell, updateComponent] using hnest
  have hother : ∀ (c : Usize) (hcc : c.val < 3), c.val ≠ component.val →
      ∀ (ch : Usize) (hch : ch.val < 3),
        sumCell (updateComponent sums component channel updated hc) c ch hcc hch =
          sumCell sums c ch hcc hch := by
    intro c hcc hne ch hch
    have hnest := AspisR1PoseidonPreparedChannelNestedSet.cell_nested_set
      sums component channel c ch (at3 sums component hc) updated
      hc hchannel hcc hch rfl
    simpa [sumCell, updateComponent, hne] using hnest
  constructor
  · intro ch hch hbound
    by_cases heq : ch.val = channel.val
    · have hchEq : ch = channel := UScalar.eq_of_val_eq heq
      subst ch
      have hsame := hselected channel hchannel
      rw [if_pos rfl] at hsame
      calc
        (sumCell (updateComponent sums component channel updated hc) component channel hc hchannel).val = updated.val :=
          congrArg (fun x : U64 => x.val) hsame
        _ = (sumCell sums component channel hc hchannel).val + product channel hchannel := hupdated
        _ = (sumCell initial component channel hc hchannel).val + product channel hchannel := by rw [hcurrent]
    · have hbefore : ch.val < channel.val := by omega
      rw [hselected, if_neg heq]
      exact hprocessed ch hch hbefore
  · constructor
    · intro ch hch hbound
      have hne : ch.val ≠ channel.val := by omega
      rw [hselected, if_neg hne]
      exact hremaining ch hch (by omega)
    · intro c hcc hne ch hch
      rw [hother c hcc hne ch hch]
      exact hframe c hcc hne ch hch

#print axioms update_invariants
end AspisR1PoseidonPreparedChannelUpdateInvariantV2
