import NEO_ComplexCells
set_option autoImplicit false
namespace NEO_ComplexReference
open Aeneas Aeneas.Std Result
attribute [local irreducible] core.num.U32.from_le_bytes

def observe (c : AspisR1CandidateParser.field.CM31) : Array U32 2#usize :=
 Array.make 2#usize [c.a,c.b]

def cohort (bytes : Slice U8) : Result (Option (Array U32 2#usize)) := do
 let parsed : Option AspisR1CandidateParser.field.CM31 ←
  AspisR1CandidateParser.field.CM31.from_le_bytes bytes
 ok (Option.map observe parsed)

/-- Complete comparison factors through four-byte reads and a symbolic two-word
parser law. No concrete LE arithmetic or large numeral is normalized here. -/
theorem eight (a b c d e f g h : U8) :
 NEO_WindowV2.complex (NEO_ComplexCells.bytes a b c d e f g h) =
 cohort (NEO_ComplexCells.bytes a b c d e f g h) := by
 have cut := NEO_ByteCuts.complex (NEO_ComplexCells.bytes a b c d e f g h)
  (Array.make 4#usize [a,b,c,d]) (Array.make 4#usize [e,f,g,h])
  (NEO_ComplexCells.first a b c d e f g h) (NEO_ComplexCells.second a b c d e f g h)
 unfold cohort
 rw [cut,bind_tc_ok]
 simp only [NEO_WindowV2.complex,NEO_ComplexCells.word0,NEO_ComplexCells.word4,
  NEO_WindowV2.P,AspisR1CandidateParser.field.P,bind_tc_ok]
 repeat' split
 all_goals simp_all [observe]

#print axioms eight
end NEO_ComplexReference
