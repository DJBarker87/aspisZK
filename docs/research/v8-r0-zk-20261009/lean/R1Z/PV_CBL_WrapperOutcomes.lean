import R1Z.PV_CBL_WrapperReference
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_WrapperOutcomes
open PV_CBL_LibraryShapes
set_option autoImplicit false

theorem default_full_result {T A : Type} (core : Result T) (buffer : Result (Buffer A)) :
    PV_CBL_WrapperReference.makeDefault core buffer =
      match core with
      | .fail e => .fail e
      | .div => .div
      | .ok c => match buffer with
        | .fail e => .fail e
        | .div => .div
        | .ok b => .ok ⟨c,b⟩ := by
  cases core <;> cases buffer <;> simp only [PV_CBL_WrapperReference.makeDefault,
    bind_tc_ok,bind_tc_fail,bind_tc_div]

theorem finalize_full_result {T A Out : Type}
    (coreFinalize : T→Buffer A→Out→Result (T×Buffer A×Out))
    (self : Wrapper T A) (out : Out) :
    PV_CBL_WrapperReference.finalize coreFinalize self out =
      match coreFinalize self.core self.buffer out with
      | .fail e => .fail e
      | .div => .div
      | .ok (_,_,output) => .ok output := by
  simp only [PV_CBL_WrapperReference.finalize]
  cases coreFinalize self.core self.buffer out with
  | fail e => rfl
  | div => rfl
  | ok x => rcases x with ⟨c,b,o⟩; rfl

#print axioms default_full_result
#print axioms finalize_full_result
end R1Z.PV_CBL_WrapperOutcomes
