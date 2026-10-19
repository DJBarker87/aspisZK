import CuSavingsRhoBatches

/-! Derive all coordinate/basis admission obligations from the actual bounded
256-cell basis carrier and loop length, rather than assuming an admitted list.
The enclosing basis-generation and source-loop bindings remain separate. -/
set_option autoImplicit false
namespace AspisR1.CuSavingsRhoInputs
open Aeneas Aeneas.Std Result AspisR1CuRho
open CuSavingsRhoInitRow CuSavingsRhoBatches
abbrev Basis := Array U32 256#usize

def index (length : Usize) (i : Fin length.val) : Usize :=
  UScalar.ofNatCore i.val (Nat.lt_trans i.isLt length.bv.isLt)

theorem index_val (length : Usize) (i : Fin length.val) : (index length i).val = i.val := rfl

def basisAt (basis : Basis) (length : Usize) (hlen : length.val ≤ 256)
    (i : Fin length.val) : U32 :=
  basis.val[i.val]'(by
    have hi : i.val < 256 := Nat.lt_of_lt_of_le i.isLt hlen
    have hn : (256#usize).val = 256 := by scalar_tac
    simpa only [basis.property,hn] using hi)

def items (basis : Basis) (length : Usize) (hlen : length.val ≤ 256) :
    List (Usize × U32) :=
  List.ofFn (fun i : Fin length.val => (index length i,basisAt basis length hlen i))

theorem items_length (basis : Basis) (length : Usize) (hlen : length.val ≤ 256) :
    (items basis length hlen).length = length.val := by
  simp only [items,List.length_ofFn]

theorem items_indices (basis : Basis) (length : Usize) (hlen : length.val ≤ 256) :
    (items basis length hlen).map (fun pair => pair.1.val) = (List.finRange length.val).map Fin.val := by
  simp only [items,List.map_ofFn,index_val,List.finRange]

theorem indices_unique (basis : Basis) (length : Usize) (hlen : length.val ≤ 256) :
    ((items basis length hlen).map (fun pair => pair.1.val)).Nodup := by
  simp only [items,List.map_ofFn,index_val]
  exact List.nodup_ofFn.mpr (fun i j h => Fin.ext h)

theorem indices_cover (basis : Basis) (length : Usize) (hlen : length.val ≤ 256)
    (i : Usize) (hi : i.val < length.val) :
    i.val ∈ (items basis length hlen).map (fun pair => pair.1.val) := by
  simp only [items,List.map_ofFn,index_val,List.mem_ofFn]
  exact ⟨⟨i.val,hi⟩,rfl⟩

theorem input_admitted (power : field.QM31) (basis : Basis) (length : Usize)
    (hlen : length.val ≤ 256) (hp : Canonical power)
    (hb : ∀ i : Fin length.val,(basisAt basis length hlen i).val < AspisV8R17.RawReducer.P) :
    Admitted {power:=power,items:=items basis length hlen} length.val := by
  refine ⟨hp,?_,?_,indices_unique basis length hlen,indices_cover basis length hlen⟩
  · intro pair hm
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hm
    exact i.isLt
  · intro pair hm
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hm
    exact hb i

#print axioms items_length
#print axioms items_indices
#print axioms indices_unique
#print axioms indices_cover
#print axioms input_admitted
end AspisR1.CuSavingsRhoInputs
