import AspisR1.PoseidonPreparedIndexComponentsCanonical

set_option autoImplicit false
namespace AspisR1PoseidonPreparedIndexProductBounds
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe

abbrev P : Nat := 2147483647
abbrev Q : Nat := (P - 1) ^ 2
abbrev PreparedArray := Array field.PreparedQm31Multiplier 3#usize
abbrev Components := Array (Array field.M31 3#usize) 3#usize

def uFin (i : Fin 3) : Std.Usize := UScalar.ofNatCore i.val (by scalar_tac)

theorem uFin_val (i : Fin 3) : (uFin i).val = i.val := by
  exact UScalar.ofNatCore_val_eq (by scalar_tac)

private def at3 {α : Type} (a : Array α 3#usize) (i : Std.Usize) (hi : i.val < 3) : α :=
  AspisR1PoseidonPreparedChannelRunStepLocal.at3 a i hi

private def leftCell (left : PreparedArray) (index component channel : Std.Usize)
    (hi : index.val < 3) (hc : component.val < 3) (hch : channel.val < 3) : field.M31 :=
  at3 (at3 (at3 left index hi).components component hc) channel hch

private def tableCell (table : Components) (component channel : Std.Usize)
    (hc : component.val < 3) (hch : channel.val < 3) : field.M31 :=
  at3 (at3 table component hc) channel hch

def product (left : PreparedArray) (tables : Fin 3 → Components)
    (index : Fin 3) (component channel : Std.Usize)
    (hc : component.val < 3) (hch : channel.val < 3) : Nat :=
  (leftCell left (uFin index) component channel (by rw [uFin_val]; exact index.isLt) hc hch).val *
    (tableCell (tables index) component channel hc hch).val

def prefixProduct (left : PreparedArray) (tables : Fin 3 → Components)
    (count : Nat) (component channel : Std.Usize)
    (hc : component.val < 3) (hch : channel.val < 3) : Nat :=
  Nat.rec 0
    (fun n acc => acc + product left tables ⟨n % 3, Nat.mod_lt _ (by omega)⟩ component channel hc hch)
    count

theorem product_le (left : PreparedArray) (tables : Fin 3 → Components)
    (hleft : ∀ (i : Fin 3) (c ch : Std.Usize) (hc : c.val < 3) (hch : ch.val < 3),
      (leftCell left (uFin i) c ch (by rw [uFin_val]; exact i.isLt) hc hch).val < P)
    (htable : ∀ (i : Fin 3) (c ch : Std.Usize) (hc : c.val < 3) (hch : ch.val < 3),
      (tableCell (tables i) c ch hc hch).val < P)
    (i : Fin 3) (component channel : Std.Usize)
    (hc : component.val < 3) (hch : channel.val < 3) :
    product left tables i component channel hc hch ≤ Q := by
  unfold product
  have hl := hleft i component channel hc hch
  have hr := htable i component channel hc hch
  have hl' : (leftCell left (uFin i) component channel
      (by rw [uFin_val]; exact i.isLt) hc hch).val ≤ P - 1 := by omega
  have hr' : (tableCell (tables i) component channel hc hch).val ≤ P - 1 := by omega
  have hmul := Nat.mul_le_mul hl' hr'
  nlinarith [hmul]

theorem prefixProduct_succ (left : PreparedArray) (tables : Fin 3 → Components)
    (count : Nat) (component channel : Std.Usize)
    (hc : component.val < 3) (hch : channel.val < 3) :
    prefixProduct left tables (count + 1) component channel hc hch =
      prefixProduct left tables count component channel hc hch +
        product left tables ⟨count % 3, Nat.mod_lt _ (by omega)⟩ component channel hc hch := by
  simp [prefixProduct]

theorem prefixProduct_le (left : PreparedArray) (tables : Fin 3 → Components)
    (hleft : ∀ (i : Fin 3) (c ch : Std.Usize) (hc : c.val < 3) (hch : ch.val < 3),
      (leftCell left (uFin i) c ch (by rw [uFin_val]; exact i.isLt) hc hch).val < P)
    (htable : ∀ (i : Fin 3) (c ch : Std.Usize) (hc : c.val < 3) (hch : ch.val < 3),
      (tableCell (tables i) c ch hc hch).val < P)
    (count : Nat) (component channel : Std.Usize)
    (hc : component.val < 3) (hch : channel.val < 3) :
    prefixProduct left tables count component channel hc hch ≤ count * Q := by
  induction count with
  | zero => simp [prefixProduct]
  | succ n ih =>
      have hp := product_le left tables hleft htable
        ⟨n % 3, Nat.mod_lt _ (by omega)⟩ component channel hc hch
      calc
        prefixProduct left tables (n + 1) component channel hc hch =
            prefixProduct left tables n component channel hc hch +
              product left tables ⟨n % 3, Nat.mod_lt _ (by omega)⟩ component channel hc hch :=
          prefixProduct_succ left tables n component channel hc hch
        _ ≤ n * Q + Q := Nat.add_le_add ih hp
        _ = (n + 1) * Q := by rw [Nat.succ_mul]

#print axioms product_le
#print axioms prefixProduct_succ
#print axioms prefixProduct_le
end AspisR1PoseidonPreparedIndexProductBounds
