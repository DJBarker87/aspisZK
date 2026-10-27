import R1Z.PV_RunJoin_ParentRoundLift
import R1Z.PV_RunJoin_SourceTables
import R0Z.PoseidonConstLift

/-! Lift a finite literal table using the existing certified per-lane theorems.
The generic list lemma is symbolic and never evaluates a hash recurrence. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_TableListLift
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_ParentRoundLift

theorem map_table {α β : Type} [Inhabited α] {n : Usize}
    (a : Array α n) (f : α → β) (g : Fin n.val → β)
    (h : ∀ i, f a.val[i.val]! = g i) : a.val.map f = List.ofFn g := by
  apply List.ext_getElem?
  intro j
  by_cases hj : j < n.val
  · have ha : j < a.val.length := by simpa only [a.property] using hj
    have hg : a.val[j]? = some a.val[j]! := by
      simp only [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem ha,Option.getD_some]
    simpa only [List.getElem?_map,List.getElem?_ofFn,dif_pos hj,hg,Option.map_some] using
      congrArg some (h ⟨j,hj⟩)
  · have hn : a.val[j]? = none := List.getElem?_eq_none (by rw [a.property];omega)
    simp only [List.getElem?_map,hn,Option.map_none,List.getElem?_ofFn,dif_neg hj]

theorem initial : poseidon2.EXTERNAL_INITIAL.val.map (liftA (K := M)) =
    List.ofFn (fun r : Fin 4 => R0P.poseidonExternalInitial (K := M) r) := by
  rw [PV_RunJoin_SourceTables.initial]
  apply map_table
  intro r
  funext i
  exact ei_rows r i

theorem final_constants : poseidon2.EXTERNAL_FINAL.val.map (liftA (K := M)) =
    List.ofFn (fun r : Fin 4 => R0P.poseidonExternalFinal (K := M) r) := by
  rw [PV_RunJoin_SourceTables.final_constants]
  apply map_table
  intro r
  funext i
  exact ef_rows r i

theorem internal : poseidon2.INTERNAL.val.map (liftU (K := M)) =
    List.ofFn (fun r : Fin 14 => R0P.poseidonInternalConstants (K := M) r) := by
  rw [PV_RunJoin_SourceTables.internal]
  apply map_table
  exact ic_all

#print axioms map_table
#print axioms initial
#print axioms final_constants
#print axioms internal
end R1Z.PV_RunJoin_TableListLift
