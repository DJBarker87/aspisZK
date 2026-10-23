-- Control flow of the actual full-MIR std slice::Iter::any emission.
-- Pointer carriers and next are explicit parameters; no native instance is
-- inferred, and no pointer value, field, callback or short-circuit is erased.
import Aeneas
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result ControlFlow Error
namespace AspisS2StdAnySource
structure SourceIter (P Q : Type) where
  ptr : P
  end_or_len : Q
  _marker : Unit

/-- [core::slice::iter::{impl core::iter::traits::iterator::Iterator<&'a T> for core::slice::iter::Iter<'a, T>}::any]: loop body 0:
    Source: '/rustc/library/core/src/slice/iter/macros.rs', lines 331:16-337:13
    Name pattern: [core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::any]
    Visibility: public -/
def anyBody
  {T P Q F : Type} (next : SourceIter P Q → Result ((Option T) × (SourceIter P Q))) (opsfunctionFnMutFTupleSharedTBoolInst :
  core.ops.function.FnMut F T Bool) (nn : P)
  (p : Q) (f : F) :
  Result (ControlFlow ((P) × (Q) × F)
    ((P) × (Q) × (Option Bool)))
  := do
  let (o, self) ←
    next
      { ptr := nn, end_or_len := p, _marker := () }
  match o with
  | none => ok (done (self.ptr, self.end_or_len, none))
  | some x =>
    let (b, f1) ← opsfunctionFnMutFTupleSharedTBoolInst.call_mut f x
    if b
    then ok (done (self.ptr, self.end_or_len, some true))
    else ok (cont (self.ptr, self.end_or_len, f1))

/-- [core::slice::iter::{impl core::iter::traits::iterator::Iterator<&'a T> for core::slice::iter::Iter<'a, T>}::any]: loop 0:
    Source: '/rustc/library/core/src/slice/iter/macros.rs', lines 331:16-337:13
    Name pattern: [core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::any]
    Visibility: public -/
def anyLoop
  {T P Q F : Type} (next : SourceIter P Q → Result ((Option T) × (SourceIter P Q))) (opsfunctionFnMutFTupleSharedTBoolInst :
  core.ops.function.FnMut F T Bool) (nn : P)
  (p : Q) (f : F) :
  Result ((P) × (Q) × (Option Bool))
  := do
  loop
    (fun (nn1, p1, f1) =>
      (anyBody next)
      opsfunctionFnMutFTupleSharedTBoolInst nn1 p1 f1)
    (nn, p, f)

/-- [core::slice::iter::{impl core::iter::traits::iterator::Iterator<&'a T> for core::slice::iter::Iter<'a, T>}::any]:
    Source: '/rustc/library/core/src/slice/iter/macros.rs', lines 326:12-329:45
    Name pattern: [core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::any]
    Visibility: public -/
def sourceAny
  {T P Q F : Type} (next : SourceIter P Q → Result ((Option T) × (SourceIter P Q))) (opsfunctionFnMutFTupleSharedATBoolInst :
  core.ops.function.FnMut F T Bool) (self : SourceIter P Q) (f : F) :
  Result (Bool × (SourceIter P Q))
  := do
  let (nn, p, pending_return) ←
    (anyLoop next)
      opsfunctionFnMutFTupleSharedATBoolInst self.ptr self.end_or_len f
  match pending_return with
  | none => ok (false, { ptr := nn, end_or_len := p, _marker := () })
  | some b => ok (b, { ptr := nn, end_or_len := p, _marker := () })


#print axioms anyBody
#print axioms sourceAny
end AspisS2StdAnySource
