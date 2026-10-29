import PV_B3P_TopDown13227
namespace PV_B3P_Binding13227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_TopDown13227 Result ControlFlow
set_option autoImplicit false

def source_claim13 (claims : Array (Array SQ 29#usize) 3#usize) (i : Usize) : Result SQ := do
  let row_index ← i / 28#usize
  let row ← Array.index_usize claims row_index
  let column ← i % 28#usize
  Array.index_usize row column

theorem source_claim_binding13 (claims : Array (Array SQ 29#usize) 3#usize) (i : Usize) :
    source_claim13 claims i = reference_terminal.claim227 claims i := rfl

def source_selection_step13 (claims : Array (Array SQ 29#usize) 3#usize)
    (selected : Array SQ 84#usize) (i : Usize) :
    Result (ControlFlow (Array SQ 84#usize × Usize) (Array SQ 84#usize)) := do
  if i < 84#usize then
    let value ← source_claim13 claims i
    let selected1 ← Array.update selected i value
    let next ← lift (Usize.wrapping_add i 1#usize)
    .ok (cont (selected1,next))
  else .ok (done selected)

theorem source_selection_step_binding13 (claims : Array (Array SQ 29#usize) 3#usize)
    (selected : Array SQ 84#usize) (i : Usize) :
    source_selection_step13 claims selected i = reference_terminal.select227_loop.body claims selected i := by
  unfold source_selection_step13 reference_terminal.select227_loop.body
  simp only [source_claim_binding13]

def source_selection13 (claims : Array (Array SQ 29#usize) 3#usize) : Result (Array SQ 84#usize) :=
  loop (fun (selected,i) => source_selection_step13 claims selected i)
    (Array.repeat 84#usize aspis_core.field.QM31.ZERO,0#usize)

theorem source_selection_binding13 : source_selection13 = reference_terminal.select227 := by
  funext claims
  unfold source_selection13 reference_terminal.select227 reference_terminal.select227_loop
  congr 1
  funext state
  exact source_selection_step_binding13 claims state.1 state.2

def with_selection13 (base : ProverRwFull.ExternalTypes) (native : SourcePorts base) : SourcePorts base :=
  {native with select := source_selection13}

theorem selection_link13 (base : ProverRwFull.ExternalTypes) (native : SourcePorts base) :
    PV_B3P_Link_selection base (with_selection13 base native) := source_selection_binding13

#print axioms source_claim_binding13
#print axioms source_selection_step_binding13
#print axioms source_selection_binding13
#print axioms selection_link13
end PV_B3P_Binding13227
