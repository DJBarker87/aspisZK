import AspisR1CuArrayGraph.Types
import AspisR1CuArraySource.Primitives

/-! Explicit primitive interpretations for the exact library emission. The
checked-domain slice/write/add models are shared with the earlier Guard proof.
Unsafe primitive source admission is still required. No axiom template is
imported; uninitialized array reads fail in this model. -/
set_option autoImplicit false
namespace AspisR1CuArrayGraph
open Aeneas Aeneas.Std Result

abbrev core.slice.Slice.get_unchecked_mut :=
  @AspisR1CuArraySource.core.slice.Slice.get_unchecked_mut
abbrev core.mem.maybe_uninit.MaybeUninit.write :=
  @AspisR1CuArraySource.core.mem.maybe_uninit.MaybeUninit.write
abbrev core.num.Usize.unchecked_add :=
  AspisR1CuArraySource.core.num.Usize.unchecked_add

def core.mem.maybe_uninit.MaybeUninit.uninit (T : Type) :
    Result (core.mem.maybe_uninit.MaybeUninit T) := .ok none

def initializedCells {T : Type} : (xs : List (Option T)) →
    Result {out : List T // out.length = xs.length}
  | [] => .ok ⟨[],rfl⟩
  | none::_ => .fail .undef
  | some value::rest => do
      let out ← initializedCells rest
      .ok ⟨value::out.val,by simp only [List.length_cons,out.property]⟩

def core.mem.maybe_uninit.MaybeUninit.array_assume_init {T : Type} {N : Usize}
    (array : Array (core.mem.maybe_uninit.MaybeUninit T) N) : Result (Array T N) := do
  let out ← initializedCells array.val
  .ok ⟨out.val,out.property.trans array.property⟩

def core.ops.control_flow.ControlFlow.Insts.CoreOpsTry_traitTry.branch {B C : Type}
    (value : Aeneas.Std.core.ops.control_flow.ControlFlow B C) :
    Result (Aeneas.Std.core.ops.control_flow.ControlFlow
      (Aeneas.Std.core.ops.control_flow.ControlFlow B core.convert.Infallible) C) :=
  match value with
  | .Continue item => .ok (.Continue item)
  | .Break error => .ok (.Break (.Break error))

def core.ops.control_flow.ControlFlow.Insts.CoreOpsTry_traitFromResidualControlFlowBInfallible.from_residual
    {B : Type} (C : Type)
    (value : Aeneas.Std.core.ops.control_flow.ControlFlow B core.convert.Infallible) :
    Result (Aeneas.Std.core.ops.control_flow.ControlFlow B C) :=
  match value with
  | .Break error => .ok (.Break error)
  | .Continue impossible => nomatch impossible

/-- Borrow-aware handback at the selected Guard-containing-reference call.
The generic opaque template's Unit output omits this retained reference state;
the actual emitted caller reads the returned Guard.array_mut. -/
def core.mem.forget {T : Type} (value : T) : Result T := .ok value

#print axioms core.slice.Slice.get_unchecked_mut
#print axioms core.mem.maybe_uninit.MaybeUninit.write
#print axioms core.num.Usize.unchecked_add
#print axioms core.mem.maybe_uninit.MaybeUninit.uninit
#print axioms initializedCells
#print axioms core.mem.maybe_uninit.MaybeUninit.array_assume_init
#print axioms core.ops.control_flow.ControlFlow.Insts.CoreOpsTry_traitTry.branch
#print axioms core.ops.control_flow.ControlFlow.Insts.CoreOpsTry_traitFromResidualControlFlowBInfallible.from_residual
#print axioms core.mem.forget
end AspisR1CuArrayGraph
