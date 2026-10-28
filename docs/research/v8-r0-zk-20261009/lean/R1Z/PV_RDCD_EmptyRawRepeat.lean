import R1Z.PV_RDCD_EmptyRaw194
import R1Z.PV_RDCD_ConstructorFrame
set_option autoImplicit false
namespace R1Z.PV_RDCD_EmptyRawRepeat
open Aeneas Aeneas.Std Result
open PV_RDCD_EmptyRaw194
/-- Source order of array Default's literal constructors, at the same world and
    primitive representation boundary as raw_four. -/
def repeated {World : Type} (n : Nat) (world : World) : Result (List EmptyRaw × World) :=
  PV_RDCD_ConstructorFrame.repeated (rawNew 4#usize) n world

theorem frame {World : Type} (n : Nat) (world : World) :
    repeated n world = ok (List.replicate n (⟨4#usize,0#usize⟩ : EmptyRaw),world) :=
  PV_RDCD_ConstructorFrame.frame (rawNew 4#usize) _ raw_four n world

theorem array10 {World : Type} (world : World) :
    repeated 10 world = ok (List.replicate 10 (⟨4#usize,0#usize⟩ : EmptyRaw),world) := frame 10 world

theorem array16 {World : Type} (world : World) :
    repeated 16 world = ok (List.replicate 16 (⟨4#usize,0#usize⟩ : EmptyRaw),world) := frame 16 world
#print axioms frame
#print axioms array10
#print axioms array16
end R1Z.PV_RDCD_EmptyRawRepeat
