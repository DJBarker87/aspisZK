import PV_L2C_ScalarCanonical
import PV_L2C_SampleCanonical
set_option autoImplicit false
namespace PV_L2C_MaskRange
open PV_L2C_M31
abbrev Cell := Fin 16 × Fin 1024
abbrev Bank := Fin 16 → Fin 1024 → word
def Canonical (bank : Bank) : Prop := ∀ c r, canonical (bank c r)

def put (bank : Bank) (cell : Cell) (mask : word) : Bank :=
  fun c r => if (c,r)=cell then add (bank c r) mask else bank c r

theorem put_canonical (bank : Bank) (hc : Canonical bank) (cell : Cell) (mask : word)
    (hm : canonical mask) : Canonical (put bank cell mask) := by
  intro c r
  unfold put
  split
  · exact add_canonical _ _ (hc c r) hm
  · exact hc c r
#print axioms put_canonical

def applyCells (bank : Bank) (cells : List (Cell × word)) : Bank :=
  cells.foldl (fun b cm => put b cm.1 cm.2) bank

theorem applied (bank : Bank) (hc : Canonical bank) (cells : List (Cell × word))
    (hm : ∀ cm ∈ cells, canonical cm.2) : Canonical (applyCells bank cells) := by
  induction cells generalizing bank with
  | nil => exact hc
  | cons cm rest ih =>
    exact ih (put bank cm.1 cm.2) (put_canonical bank hc cm.1 cm.2 (hm cm (by simp)))
      (fun cr hr => hm cr (by simp [hr]))
#print axioms applied

def balance (bank : Bank) (active : Fin 1024 → Bool) (dependent : Fin 16 → Aeneas.Std.Usize) : Bank :=
  fun c => PV_L2C_ScalarBalance.output (bank c) active (dependent c)

theorem balanced (bank : Bank) (hc : Canonical bank) (active : Fin 1024 → Bool)
    (dependent : Fin 16 → Aeneas.Std.Usize) : Canonical (balance bank active dependent) := by
  intro c r
  exact PV_L2C_ScalarCanonical.output_canonical (bank c) active (hc c) (dependent c) r
#print axioms balanced

theorem application (bank : Bank) (hc : Canonical bank) (cells : List (Cell × word))
    (hm : ∀ cm ∈ cells, canonical cm.2) (active : Fin 1024 → Bool)
    (dependent : Fin 16 → Aeneas.Std.Usize) :
    Canonical (balance (applyCells bank cells) active dependent) :=
  balanced _ (applied bank hc cells hm) active dependent
#print axioms application
end PV_L2C_MaskRange
