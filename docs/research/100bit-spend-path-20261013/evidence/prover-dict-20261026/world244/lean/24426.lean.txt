import Aeneas
set_option autoImplicit false
namespace PDict_CopySource244
open Aeneas Aeneas.Std Result ControlFlow Error


/-- [pdict_world244::coefficients::copy_owned]: loop body 0:
    Source: 'coefficients.rs', lines 21:4-24:5
    Visibility: public -/
@[rust_loop_body]
def coefficients.copy_owned_loop.body
  {T : Type} (rows : Array T 1024#usize) (out : Array T 1024#usize)
  (index : Std.Usize) :
  Result (ControlFlow ((Array T 1024#usize) × Std.Usize) (Array T 1024#usize))
  := do
  if index < 1024#usize
  then
    let t ← Array.index_usize rows index
    let out1 ← Array.update out index t
    let index1 ← lift (Std.Usize.wrapping_add index 1#usize)
    ok (cont (out1, index1))
  else ok (done out)

/-- [pdict_world244::coefficients::copy_owned]: loop 0:
    Source: 'coefficients.rs', lines 21:4-24:5
    Visibility: public -/
@[rust_loop]
def coefficients.copy_owned_loop
  {T : Type} (rows : Array T 1024#usize) (out : Array T 1024#usize)
  (index : Std.Usize) :
  Result (Array T 1024#usize)
  := do
  loop
    (fun (out1, index1) => coefficients.copy_owned_loop.body rows out1 index1)
    (out, index)

/-- [pdict_world244::coefficients::copy_owned]:
    Source: 'coefficients.rs', lines 18:0-26:1
    Visibility: public -/
@[reducible]
def coefficients.copy_owned
  {T : Type} (coremarkerCopyInst : core.marker.Copy T)
  (rows : Array T 1024#usize) :
  Result (Array T 1024#usize)
  := do
  coefficients.copy_owned_loop rows rows 0#usize

#print axioms coefficients.copy_owned_loop.body
#print axioms coefficients.copy_owned_loop
#print axioms coefficients.copy_owned
end PDict_CopySource244
