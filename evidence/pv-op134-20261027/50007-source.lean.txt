import R1Z.PV_Op134_Order
import R1Z.PV_CBM_InventoryCardinality
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Card
namespace R1Z.PV_Op134_Coverage
open PV_Op134_Order PV_CBM_InventoryShape
set_option autoImplicit false
abbrev FreeCell := PV_CBM_InventoryCardinality.Cell

def toFree (xs : List Cell)
    (hb : ∀ c ∈ xs, c.row.val < 1024 ∧ c.column.val < 16)
    (hf : ∀ c ∈ xs, free c.row.val c.column.val)
    (c : {c : Cell // c ∈ xs}) : FreeCell :=
  ⟨(⟨c.val.row.val,(hb c.val c.prop).1⟩,
     ⟨c.val.column.val,(hb c.val c.prop).2⟩),hf c.val c.prop⟩

theorem toFree_injective (xs : List Cell)
    (hb : ∀ c ∈ xs, c.row.val < 1024 ∧ c.column.val < 16)
    (hf : ∀ c ∈ xs, free c.row.val c.column.val) :
    Function.Injective (toFree xs hb hf) := by
  intro a b h
  apply Subtype.ext
  apply key_injective (hb a.val a.prop).1 (hb b.val b.prop).1
  have hr := congrArg (fun c : FreeCell => c.val.1.val) h
  have hc := congrArg (fun c : FreeCell => c.val.2.val) h
  change a.val.row.val = b.val.row.val at hr
  change a.val.column.val = b.val.column.val at hc
  simp only [key,hr,hc]

theorem complete (xs : List Cell) (hn : xs.Nodup)
    (hb : ∀ c ∈ xs, c.row.val < 1024 ∧ c.column.val < 16)
    (hf : ∀ c ∈ xs, free c.row.val c.column.val)
    (hl : xs.length = 3803) (row column : Nat)
    (hr : row < 1024) (hc : column < 16) (hfree : free row column) :
    ∃ c ∈ xs, c.row.val = row ∧ c.column.val = column := by
  classical
  let ys := xs.attach.map (toFree xs hb hf)
  have hn' : ys.Nodup := hn.attach.map (toFree_injective xs hb hf)
  have hlen : ys.length = 3803 := by
    simpa only [ys,List.length_map,List.length_attach] using hl
  have hall : ys.toFinset = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [List.toFinset_card_of_nodup hn',hlen,PV_CBM_InventoryCardinality.cardinal])
  let target : FreeCell := ⟨(⟨row,hr⟩,⟨column,hc⟩),hfree⟩
  have ht : target ∈ ys := by
    apply List.mem_toFinset.mp
    rw [hall]
    exact Finset.mem_univ target
  obtain ⟨c,_,he⟩ := List.mem_map.mp ht
  refine ⟨c.val,c.prop,?_,?_⟩
  · exact congrArg (fun c : FreeCell => c.val.1.val) he
  · exact congrArg (fun c : FreeCell => c.val.2.val) he
#print axioms toFree_injective
#print axioms complete
end R1Z.PV_Op134_Coverage
