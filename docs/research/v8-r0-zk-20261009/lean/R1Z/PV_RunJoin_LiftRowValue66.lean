import R1Z.PV_RunJoin_LiftPayload66
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_LiftRowValue66
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open PV_RunJoin_BackendMRows58 (Columns column)
abbrev Q := aspis_core.field.QM31

def row (columns : Columns) (hlen : ∀ l,l<26 → (column columns l).length=1024)
    (lane : Nat) : alloc.vec.Vec Q :=
  ⟨PV_RunJoin_LiftPayload66.payload columns hlen lane 0 1024,by
    simp only [PV_RunJoin_LiftPayload66.payload,List.length_ofFn];scalar_tac⟩

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (columns : Columns)
    (hlen : ∀ l,l<26 → (column columns l).length=1024)
    (lane : Usize) (hl : lane.val<26) :
    @host_semantic.lift_columns_loop0_loop0 (types base) (selected base heap box ops)
      columns lane (alloc.vec.Vec.with_capacity Q 1024#usize) 0#usize=
      ok (row columns hlen lane.val) := by
  rw [PV_RunJoin_LiftRow63.complete base heap box ops columns lane 1024 _ 0#usize rfl]
  obtain ⟨next,hn,hv⟩ := PV_RunJoin_LiftPayload66.phase base heap box ops columns hlen lane hl
    1024 0#usize (by decide) (alloc.vec.Vec.with_capacity Q 1024#usize) (by change 1024≤Usize.max;scalar_tac)
  rw [hn]
  apply congrArg Result.ok
  apply Subtype.ext
  change next.val=PV_RunJoin_LiftPayload66.payload columns hlen lane.val 0 1024
  simpa only [alloc.vec.Vec.with_capacity,List.nil_append,show (0#usize).val=0 from rfl] using hv

#print axioms row
#print axioms complete
end R1Z.PV_RunJoin_LiftRowValue66
