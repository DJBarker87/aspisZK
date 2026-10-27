import Aeneas
open Aeneas Aeneas.Std
namespace R1Z.PV_CBL_PathJoinValue
set_option autoImplicit false
/- Value-only Unix byte-join specification. Allocation failure, destructor
semantics, exact Path carriers and native association remain open gates. -/
def slash : U8 := 47#u8

def separator (base : List U8) : List U8 :=
  if base=[] ∨ base.getLast?=some slash then [] else [slash]

def join (base path : List U8) : List U8 :=
  if path.head?=some slash then path else base++separator base++path
#print axioms slash
#print axioms separator
#print axioms join
end R1Z.PV_CBL_PathJoinValue
