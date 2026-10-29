import PV_B3P_Install227
namespace PV_B3P_TopDown13227
open Aeneas Aeneas.Std ProverRwFull
set_option autoImplicit false
noncomputable section
abbrev SP := PV_B3P_227.reference_terminal.SemanticPublic
abbrev SQ := PV_B3P_227.aspis_core.field.QM31
abbrev SC := PV_B3P_227.aspis_core.state_only_prefix.r0.Challenges
abbrev SE := PV_B3P_227.aspis_core.state_only_prefix.r0.Error
abbrev PE := PV_B3P_227.reference_terminal.PoolV1PairForestSemanticTerminalErrorV1
abbrev Parts := SQ × Array SQ 16#usize × Array SQ 10#usize × SQ
abbrev PartsFn := SP → Array SQ 84#usize → Array SQ 10#usize → SQ → SQ → SQ → Array SQ 10#usize → SQ → Result (core.result.Result Parts PE)
abbrev Public (base : ExternalTypes) :=
  @aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public (PV_B3P_Install227.Types base)
/-- Explicit source semantics slots. These are parameters, not extracted models
or axioms. Binding each slot to an exact source body remains an obligation. -/
structure SourcePorts (base : ExternalTypes) where
  semantic : Public base → Result SP
  select : Array (Array SQ 29#usize) 3#usize → Result (Array SQ 84#usize)
  parts : PartsFn

def source_continuation (base : ExternalTypes) (native : SourcePorts base)
    (p : Public base) (claims : Array (Array aspis_core.field.QM31 29#usize) 3#usize)
    (point : Array aspis_core.field.QM31 10#usize)
    (c : aspis_core.state_only_prefix.r0.Challenges) : Result (core.result.Result SQ SE) := do
  let selected ← native.select (PV_B3P_Carrier227.mapArray
    (PV_B3P_Carrier227.mapArray PV_B3P_Carrier227.toQ) claims)
  let public1 ← native.semantic p
  let cs := PV_B3P_Carrier227.challenges c
  let r ← native.parts public1 selected (PV_B3P_Carrier227.mapArray PV_B3P_Carrier227.toQ point)
    cs.lambda cs.chi cs.theta cs.zc cs.mu
  match r with
  | .Ok parts => .ok (.Ok parts.1)
  | .Err _ => .ok (.Err .Public)

/-- The source wrapper equation, with its actual selection, semantic conversion,
callee invocation, and both Rust Result branches exposed. -/
def PV_B3P_Link_terminal_qm31 (base : ExternalTypes)
    (ops : @ExternalFuns (PV_B3P_Install227.Types base)) (native : SourcePorts base) : Prop :=
  ∀ p claims point c, ops.op227 p claims point c =
    PV_B3P_Install227.transport (source_continuation base native p claims point c)

def PV_B3P_Link_semantic (base : ExternalTypes) (native : SourcePorts base) : Prop :=
  ∀ p, native.semantic p = .ok (PV_B3P_Carrier227.semantic base p)

def PV_B3P_Link_selection (base : ExternalTypes) (native : SourcePorts base) : Prop :=
  native.select = PV_B3P_227.reference_terminal.select227

def PV_B3P_Link_terminal_parts (base : ExternalTypes) (native : SourcePorts base) : Prop :=
  native.parts = PV_B3P_227.reference_terminal.terminal_parts

def transported_reference (base : ExternalTypes) (p : Public base)
    (claims : Array (Array aspis_core.field.QM31 29#usize) 3#usize)
    (point : Array aspis_core.field.QM31 10#usize)
    (c : aspis_core.state_only_prefix.r0.Challenges) :=
  PV_B3P_Install227.transport (PV_B3P_227.reference_terminal.reference227
    (PV_B3P_Carrier227.semantic base p)
    (PV_B3P_Carrier227.mapArray (PV_B3P_Carrier227.mapArray PV_B3P_Carrier227.toQ) claims)
    (PV_B3P_Carrier227.mapArray PV_B3P_Carrier227.toQ point)
    (PV_B3P_Carrier227.challenges c))

attribute [local irreducible] PV_B3P_227.reference_terminal.terminal_parts
  PV_B3P_227.reference_terminal.select227 PV_B3P_Carrier227.semantic

theorem continuation_composes (base : ExternalTypes) (native : SourcePorts base)
    (semantic : PV_B3P_Link_semantic base native)
    (selection : PV_B3P_Link_selection base native)
    (parts : PV_B3P_Link_terminal_parts base native)
    (p : Public base) (claims : Array (Array aspis_core.field.QM31 29#usize) 3#usize)
    (point : Array aspis_core.field.QM31 10#usize)
    (c : aspis_core.state_only_prefix.r0.Challenges) :
    PV_B3P_Install227.transport (source_continuation base native p claims point c) =
      transported_reference base p claims point c := by
  unfold source_continuation transported_reference
  rw [selection]
  unfold PV_B3P_227.reference_terminal.reference227
  congr 1
  apply congrArg (Aeneas.Std.bind _)
  funext selected
  rw [semantic p]
  rw [parts]
  rfl

section
variable (base : ExternalTypes)
local notation "terminal" => transported_reference base
/-- Exact bridge conclusion, specialized to the explicit transported reference.
This is conditional composition only: no source binding credit is asserted. -/
theorem selected_callback (ops : @ExternalFuns (PV_B3P_Install227.Types base))
    (native : SourcePorts base)
    (wrapper : PV_B3P_Link_terminal_qm31 base ops native)
    (semantic : PV_B3P_Link_semantic base native)
    (selection : PV_B3P_Link_selection base native)
    (parts : PV_B3P_Link_terminal_parts base native)
    (self : @host_semantic.SemanticOracle (PV_B3P_Install227.Types base))
    (point : Array aspis_core.field.QM31 10#usize) :
    letI : ExternalTypes := PV_B3P_Install227.Types base
    ∀ claims,
      ops.op227 self.«public» claims point self.challenges =
        terminal self.«public» claims point self.challenges := by
  letI : ExternalTypes := PV_B3P_Install227.Types base
  intro claims
  exact Eq.trans (wrapper self.«public» claims point self.challenges)
    (continuation_composes base native semantic selection parts self.«public» claims point self.challenges)
end
#print axioms continuation_composes
#print axioms selected_callback
end
end PV_B3P_TopDown13227
