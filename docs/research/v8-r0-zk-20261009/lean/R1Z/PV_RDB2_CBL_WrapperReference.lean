import R1Z.PV_RDB2_CBL_LibraryShapes
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_WrapperReference
open PV_CBL_LibraryShapes
set_option autoImplicit false

/-- Source-shaped pure reference. Defaults are explicit frontier parameters;
no op217 source-binding theorem is asserted here. -/
def makeDefault {T A : Type} (core : Result T) (buffer : Result (Buffer A)) :
    Result (Wrapper T A) := do
  let c ← core
  let b ← buffer
  ok ⟨c,b⟩

/-- Pure output projection corresponding to wrapper.rs finalize_into. Source
extraction, trait association and destructor semantics remain separate gates. -/
def finalize {T A Out : Type}
    (coreFinalize : T→Buffer A→Out→Result (T×Buffer A×Out))
    (self : Wrapper T A) (out : Out) : Result Out := do
  let (_,_,output) ← coreFinalize self.core self.buffer out
  ok output

#print axioms makeDefault
#print axioms finalize
end R1Z.PV_CBL_WrapperReference
