import R1Z.PV_RunJoin_BackendMInput58
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_BackendMRows58
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open PV_RunJoin_BackendMatrix58 PV_RunJoin_BackendPrefix58
abbrev Columns := Array (alloc.vec.Vec aspis_core.field.M31) 26#usize

def column (columns : Columns) (l : Nat) :=
  columns.val[l%26]'(by rw [columns.property];exact Nat.mod_lt _ (by decide))
def element (columns : Columns) (hlen : ∀ l,l<26 → (column columns l).length=1024) (l j : Nat) : U32 :=
  (column columns (l%26)).val[j%1024]'(by
    change j%1024<(column columns (l%26)).length
    rw [hlen _ (Nat.mod_lt _ (by decide))]
    exact Nat.mod_lt _ (by decide))
def values (columns : Columns) (hlen : ∀ l,l<26 → (column columns l).length=1024) (l j : Nat) : W :=
  PV_RunJoin_BackendMInput58.value (element columns hlen l j)

set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem read (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (columns : Columns) (hlen : ∀ l,l<26 → (column columns l).length=1024)
    (lane row : Usize) (hl : lane.val<26) (hr : row.val<1024) :
    (do
      let col ← Array.index_usize columns lane
      let m ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice aspis_core.field.M31) col row
      @aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31
        (types base) (selected base heap box ops) m)=ok (values columns hlen lane.val row.val) := by
  have col : Array.index_usize columns lane=ok (column columns lane.val) := by
    rw [ProverCommitArrayIndex25.array_index_usize_ok columns lane hl]
    simp only [column,Nat.mod_eq_of_lt hl]
  rw [col]
  simp only [bind_tc_ok]
  have hi : row.val<(column columns lane.val).val.length := by
    change row.val<(column columns lane.val).length
    rw [hlen _ hl]
    exact hr
  obtain ⟨m,hm,he⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.index_usize_spec (column columns lane.val) row hi)
  rw [alloc.vec.Vec.index_slice_index,hm]
  simp only [bind_tc_ok]
  rw [PV_RunJoin_BackendMInput58.complete base heap box ops]
  simp only [values,element,Nat.mod_eq_of_lt hl,Nat.mod_eq_of_lt hr]
  rw [he]

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (self : prover.Backend) (p : Nat → Nat → W) (hp : self.messages=matrix p)
    (columns : Columns) (hlen : ∀ l,l<26 → (column columns l).length=1024)
    (lane : Usize) (hl : lane.val<26) :
    @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop0_loop0
      (types base) (selected base heap box ops) self columns lane 0#usize=
      ok {self with messages:=matrix (filled p lane.val (values columns hlen lane.val) 1024)} := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  rw [PV_RunJoin_BackendRows58.c1_base]
  exact PV_RunJoin_BackendFill58.complete base heap box ops _ (values columns hlen lane.val)
    (fun row hr => read base heap box ops columns hlen lane row hl hr)
    p lane (by omega) 1024 0#usize rfl self
    (by simpa only [PV_RunJoin_BackendPrefix58.zero] using hp)

#print axioms read
#print axioms complete
end R1Z.PV_RunJoin_BackendMRows58
