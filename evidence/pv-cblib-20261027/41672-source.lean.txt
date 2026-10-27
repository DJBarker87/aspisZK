import Aeneas
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_PaddingModel
set_option autoImplicit false
/-- Value-only SHA-256 specialization of digest_pad; source/loan link is separate. -/
def delimited (buffer : List U8) (pos : Nat) : List U8 :=
  buffer.take pos ++ [128#u8] ++ List.replicate (63-pos) 0#u8
def first (buffer : List U8) (pos : Nat) (suffix : List U8) : List U8 :=
  let head := delimited buffer pos
  if pos<56 then head.take 56 ++ suffix else head
def second (pos : Nat) (suffix : List U8) : Option (List U8) :=
  if pos<56 then none else some (List.replicate 56 0#u8 ++ suffix)
def blocks (buffer : List U8) (pos : Nat) (suffix : List U8) : List (List U8) :=
  first buffer pos suffix :: (second pos suffix).toList
/-- The native two-block branch retains the first buffer, not the local second block. -/
def retained (buffer : List U8) (pos : Nat) (suffix : List U8) : List U8 × Nat :=
  (first buffer pos suffix,0)
#print axioms delimited
#print axioms first
#print axioms second
#print axioms blocks
#print axioms retained
end R1Z.PV_CBL_PaddingModel
