import NDO_JFv_TX2_Rows
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFv_TX2_GatherShape
open Aeneas Aeneas.Std Result
abbrev Row := Port4C_GeometryGather.Row

def row (i : Nat) : Row := JFv_TX2_Rows.value ⟨i%12,by omega⟩
def zs (n : Nat) : List U32 := (List.range n).map (fun i => (row i).lineZ)
def flat (n : Nat) : List U32 := (List.range n).flatMap (fun i => (row i).words)
def selected : Slice U32 := ⟨List.ofFn JFv_TX2_Rows.query,by simp;scalar_tac⟩

theorem lengths (n : Nat) : (zs n).length=n ∧ (flat n).length=5*n := by
  constructor
  · simp only [zs,List.length_map,List.length_range]
  · induction n with
    | zero => rfl
    | succ n ih =>
      rw [flat,List.range_succ,List.flatMap_append,List.flatMap_singleton,List.length_append]
      change (flat n).length+5=5*(n+1)
      omega

theorem step (n : Nat) : zs (n+1)=zs n++[(row n).lineZ] ∧
    flat (n+1)=flat n++(row n).words := by
  simp only [zs,flat,List.range_succ,List.map_append,List.map_singleton,
    List.flatMap_append,List.flatMap_singleton,and_self]

theorem nonzero (n : Nat) : ∀ x∈flat n,S7JoinBasisMachine.decode x≠0 := by
  intro x member
  obtain ⟨i,_,hx⟩ := List.mem_flatMap.mp member
  exact JFv_TX2_Rows.nonzero ⟨i%12,by omega⟩ x hx

theorem query (i : Nat) (active : i<12) :
    selected.val[i]'(by change i<(List.ofFn JFv_TX2_Rows.query).length;simpa using active)=
      JFv_TX2_Rows.query ⟨i,active⟩ := by
  simp only [selected,List.getElem_ofFn]

theorem row_eq (i : Nat) (active : i<12) : row i=JFv_TX2_Rows.value ⟨i,active⟩ := by
  exact congrArg JFv_TX2_Rows.value (Fin.ext (Nat.mod_eq_of_lt active))

#print axioms lengths
#print axioms step
#print axioms nonzero
#print axioms query
#print axioms row_eq
end AspisR1.JFv_TX2_GatherShape
end
