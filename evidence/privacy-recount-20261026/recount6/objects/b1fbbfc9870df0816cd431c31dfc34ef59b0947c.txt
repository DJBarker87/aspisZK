import Aeneas
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_LibraryShapes
set_option autoImplicit false

/- Field shapes from the byte-pinned generic-array/block-buffer/digest sources.
These are reference carriers, not a callback source-binding certificate. -/
structure Even (T U : Type) where
  parent1 : U
  parent2 : U
  marker : Unit

structure Odd (T U : Type) where
  parent1 : U
  parent2 : U
  data : T

structure GenericArray (T U A : Type) where
  data : A

structure Buffer (A : Type) where
  buffer : A
  pos : U8
  marker : Unit

structure Wrapper (T A : Type) where
  core : T
  buffer : Buffer A

structure CtWrapper (T : Type) where
  inner : T
  marker : Unit

#print axioms Even
#print axioms Odd
#print axioms GenericArray
#print axioms Buffer
#print axioms Wrapper
#print axioms CtWrapper
end R1Z.PV_CBL_LibraryShapes
