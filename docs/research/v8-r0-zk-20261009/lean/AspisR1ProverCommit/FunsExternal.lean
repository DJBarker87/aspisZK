import AspisR1ProverCommit.Types
open Aeneas Aeneas.Std Result ControlFlow Error
namespace AspisR1ProverCommit
/-! Live payload and Result adapters for per-leaf extraction. Allocation and
zeroization are deliberately unsupported (`fail .panic`), rather than axioms
or claims about the Rust allocator/drop path. The address theorem does not
invoke either operation. -/
def core.result.Result.map {T E U F : Type}
    (inst : core.ops.function.FnOnce F T U)
    (self : core.result.Result T E) (f : F) : Result (core.result.Result U E) := do
  match self with
  | .Ok x => do
    let y ← inst.call_once f x
    ok (.Ok y)
  | .Err e => ok (.Err e)

def alloc.vec.Vec.try_reserve_exact {T : Type} (_A : Type)
    (_self : alloc.vec.Vec T) (_n : Std.Usize) :
    Result ((core.result.Result Unit alloc.collections.TryReserveError) × alloc.vec.Vec T) :=
  .fail .panic

def aspis_core.r0.FIBRE_COUNT : Result Std.Usize := .ok 262144#usize

def zeroize.Zeroizing.Insts.CoreConvertAsRef.as_ref {T Z : Type}
    (inst : core.convert.AsRef Z T) (_zero : zeroize.Zeroize Z)
    (self : zeroize.Zeroizing Z) : Result T := inst.as_ref self

def Array.Insts.ZeroizeZeroize.zeroize {Z : Type} {N : Std.Usize}
    (_inst : zeroize.Zeroize Z) (_self : Array Z N) : Result (Array Z N) := .fail .panic

def zeroize.Zeroize.Blanket.zeroize {Z : Type}
    (_inst : zeroize.DefaultIsZeroes Z) (_self : Z) : Result Z := .fail .panic
end AspisR1ProverCommit
