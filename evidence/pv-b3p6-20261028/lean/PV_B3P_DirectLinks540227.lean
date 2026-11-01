import PV_B3P_DirectAbsorption17227
import PV_B3P_DirectDigest17227
import PV_B3P_DirectPreweightedCallers17227
import PV_B3P_LinkDefinitions13227
namespace PV_B3P_Direct540227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Direct17227 PV_B3P_Links13227
set_option autoImplicit false

/-- These use the directly extracted deployed definitions, not source-model slots. -/
theorem extracted_absorption_link540 :
    PV_B3P_Link_terminal_absorption_lanes_literal
      host_terminal.absorption_lanes_literal := by
  funext low fixed two eight nodes opened
  exact absorption_extraction_reference17 low fixed two eight nodes opened

theorem extracted_digest_link540 :
    PV_B3P_Link_terminal_add_digest_binding host_terminal.add_digest_binding := by
  funext output selector opened start expected tweak
  exact digest_extraction_reference17 output selector opened start expected tweak

/-- Frozen actual call families only. This does not change the old total Link3.
The source-call inventory is an independent provenance obligation. -/
structure PreweightedCall540 where
  length : Usize
  start : Usize
  actual : PreweightedActualCall17 length start

abbrev Packed540 := Array aspis_core.field.QM31 24#usize

def extracted_preweighted_called540 (call : PreweightedCall540)
    (packed : Packed540) (values : Array aspis_core.field.QM31 call.length) :=
  host_terminal.add_preweighted packed call.start values

def reference_preweighted_called540 (call : PreweightedCall540)
    (packed : Packed540) (values : Array aspis_core.field.QM31 call.length) :=
  reference_terminal.add_preweighted packed call.start values

/-- A new, separately named restricted-domain predicate; no total source law
is inferred from it and no endpoint hypothesis is silently replaced. -/
def PV_B3P_Link_preweighted_actual540 : Prop :=
  extracted_preweighted_called540 = reference_preweighted_called540

theorem extracted_preweighted_actual_link540 : PV_B3P_Link_preweighted_actual540 := by
  funext call packed values
  exact preweighted_actual_extraction_reference17 packed call.start values call.actual

/-- Preserve the entire Result through any caller continuation, including all
failure and divergence results. No successful-execution assumption is used. -/
theorem preweighted_actual_continuation540 {β : Type}
    (call : PreweightedCall540) (packed : Packed540)
    (values : Array aspis_core.field.QM31 call.length) (next : Packed540 → Result β) :
    (do let after ← extracted_preweighted_called540 call packed values; next after) =
    (do let after ← reference_preweighted_called540 call packed values; next after) := by
  rw [extracted_preweighted_actual_link540]

/-- Non-emptiness of the actual typed domain, not an invented intrinsic model. -/
theorem preweighted_actual_nonempty540 : Nonempty PreweightedCall540 := by
  refine ⟨⟨16#usize,0#usize,?_⟩⟩
  exact Or.inl ⟨rfl,rfl⟩

/-- The two total direct Links and the restricted actual preweighted Link hold
jointly. This is a local direct-body conjunction, not the 36-body skeleton. -/
theorem direct_local_links540 :
    PV_B3P_Link_terminal_absorption_lanes_literal host_terminal.absorption_lanes_literal ∧
    PV_B3P_Link_terminal_add_digest_binding host_terminal.add_digest_binding ∧
    PV_B3P_Link_preweighted_actual540 ∧ Nonempty PreweightedCall540 :=
  ⟨extracted_absorption_link540,extracted_digest_link540,
    extracted_preweighted_actual_link540,preweighted_actual_nonempty540⟩

#print axioms extracted_absorption_link540
#print axioms extracted_digest_link540
#print axioms extracted_preweighted_actual_link540
#print axioms preweighted_actual_continuation540
#print axioms preweighted_actual_nonempty540
#print axioms direct_local_links540
end PV_B3P_Direct540227
