import Aeneas
import AspisV8R19.DuplexFrames

/-! Generated-package-independent interface for byte-oracle logs. The two
extractions generate conflicting global discriminant instances; their proved
certificates compose through this common, definitionally identical carrier. -/
set_option autoImplicit false
namespace AspisR1DigestLogCarrier
open Aeneas Aeneas.Std
open AspisV8R19.DuplexFrames
abbrev State := Fin 32 → AspisV8R19.DuplexFrames.Byte

def decodeByte (b : U8) : AspisV8R19.DuplexFrames.Byte := ⟨b.val,b.bv.isLt⟩
def decodeState (s : Array U8 32#usize) : State :=
  fun i => decodeByte (s.val[i.val]'(by have hs : s.val.length = 32 := s.property; omega))
def flatten (input : Slice (Slice U8)) : Bytes :=
  (input.val.flatMap (fun part => part.val)).map decodeByte

def Consistent (Hbytes : Bytes → State) (tr : List (Bytes × State)) : Prop :=
  ∀ q ∈ tr, q.2 = Hbytes q.1

def Covers (reached : Bytes × State → Prop) (tr : List (Bytes × State)) : Prop :=
  ∀ q, reached q → q ∈ tr

theorem append_consistent (Hbytes : Bytes → State) (tr1 tr2 : List (Bytes × State))
    (h1 : Consistent Hbytes tr1) (h2 : Consistent Hbytes tr2) :
    Consistent Hbytes (tr1 ++ tr2) := by
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · exact h1 q hq
  · exact h2 q hq

theorem append_covers (reached1 reached2 : Bytes × State → Prop)
    (tr1 tr2 : List (Bytes × State)) (h1 : Covers reached1 tr1) (h2 : Covers reached2 tr2) :
    Covers (fun q => reached1 q ∨ reached2 q) (tr1 ++ tr2) := by
  intro q hq
  rcases hq with hq | hq
  · exact List.mem_append_left _ (h1 q hq)
  · exact List.mem_append_right _ (h2 q hq)

#print axioms append_consistent
#print axioms append_covers
end AspisR1DigestLogCarrier
