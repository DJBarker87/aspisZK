import PV_STX2_ChainCaptures
import PV_STX2_SliceF0
import PV_STX2_SliceF1
import PV_STX2_SliceF2
import PV_STX2_SliceF4
import PV_STX2_SliceF5
import PV_STX2_SliceF6
import PV_STX2_SliceF7
import PV_STX2_SliceF8
import PV_STX2_SliceF9
import PV_STX2_SliceF11
import PV_STX2_SliceF12
import PV_STX2_SliceF13
import PV_STX2_SliceF15
import PV_STX2_SliceF19
import PV_STX2_SliceF21
import PV_STX2_SliceF22
import PV_STX2_SliceF23
import PV_STX2_SliceF24
import PV_STX2_SliceF32
import PV_STX2_SliceF33
import PV_STX2_SliceF34
import PV_STX2_SliceF42
set_option autoImplicit false
namespace PV_STX2_SlicePrograms
open PV_STX2_Syntax PV_STX2_SliceSyntax
/-- Conditional on owner acceptance of the translator patch. Source-bound
lookup generated from the retained Charon declarations, not value matching. -/
def resolve : Data → Option Nat
  | .object [("Regular",.object [("kind",.object [("Trait",.array [.object [("HashConsedValue",.array [.number 1670,_])],.number 0])]),("generics",_)])] => some 6
  | .object [("Regular",.object [("kind",.object [("Trait",.array [.object [("HashConsedValue",.array [.number 1686,_])],.number 0])]),("generics",_)])] => some 8
  | .object [("Regular",.object [("kind",.object [("Trait",.array [.object [("Deduplicated",.number 1670)],.number 0])]),("generics",_)])] => some 6
  | .object [("Regular",.object [("kind",.object [("Trait",.array [.object [("Deduplicated",.number 1686)],.number 0])]),("generics",_)])] => some 8
  | callee => PV_STX2_ChainCaptures.regular callee
/-- Conditional on owner acceptance of the translator patch. Source-bound
lookup generated from the retained Charon declarations, not value matching. -/
def function : Nat → Option PV_STX2_SliceSyntax.Program
  | 0 => some PV_STX2_SliceF0.program
  | 1 => some PV_STX2_SliceF1.program
  | 2 => some PV_STX2_SliceF2.program
  | 4 => some PV_STX2_SliceF4.program
  | 5 => some PV_STX2_SliceF5.program
  | 6 => some PV_STX2_SliceF6.program
  | 7 => some PV_STX2_SliceF7.program
  | 8 => some PV_STX2_SliceF8.program
  | 9 => some PV_STX2_SliceF9.program
  | 11 => some PV_STX2_SliceF11.program
  | 12 => some PV_STX2_SliceF12.program
  | 13 => some PV_STX2_SliceF13.program
  | 15 => some PV_STX2_SliceF15.program
  | 19 => some PV_STX2_SliceF19.program
  | 21 => some PV_STX2_SliceF21.program
  | 22 => some PV_STX2_SliceF22.program
  | 23 => some PV_STX2_SliceF23.program
  | 24 => some PV_STX2_SliceF24.program
  | 32 => some PV_STX2_SliceF32.program
  | 33 => some PV_STX2_SliceF33.program
  | 34 => some PV_STX2_SliceF34.program
  | 42 => some PV_STX2_SliceF42.program
  | _ => none
/-- Conditional on owner acceptance of the translator patch. Source-bound
lookup generated from the retained Charon declarations, not value matching. -/
def dispatch (callee : Data) : Option PV_STX2_SliceSyntax.Program := do
  let fid ← resolve callee
  function fid
/-- Conditional on owner acceptance of the translator patch. Source-bound
lookup generated from the retained Charon declarations, not value matching. -/
def selectedCallee : Node → Option Data
  | .leaf (.call _ callee _ _ _) => some callee
  | _ => none
/-- Conditional on owner acceptance of the translator patch. Source-bound
lookup generated from the retained Charon declarations, not value matching. -/
theorem source5_call126 : (selectedCallee PV_STX2_SliceF5.node3).bind dispatch = some PV_STX2_SliceF6.program := rfl
#print axioms source5_call126
/-- Conditional on owner acceptance of the translator patch. Source-bound
lookup generated from the retained Charon declarations, not value matching. -/
theorem source7_call173 : (selectedCallee PV_STX2_SliceF7.node3).bind dispatch = some PV_STX2_SliceF8.program := rfl
#print axioms source7_call173
/-- Conditional on owner acceptance of the translator patch. Source-bound
lookup generated from the retained Charon declarations, not value matching. -/
theorem source8_call195 : (selectedCallee PV_STX2_SliceF8.node8).bind dispatch = some PV_STX2_SliceF6.program := rfl
#print axioms source8_call195
/-- Conditional on owner acceptance of the translator patch. Source-bound
lookup generated from the retained Charon declarations, not value matching. -/
theorem source9_call266 : (selectedCallee PV_STX2_SliceF9.node27).bind dispatch = some PV_STX2_SliceF8.program := rfl
#print axioms source9_call266
#print axioms resolve
#print axioms function
#print axioms dispatch
#print axioms selectedCallee
end PV_STX2_SlicePrograms
