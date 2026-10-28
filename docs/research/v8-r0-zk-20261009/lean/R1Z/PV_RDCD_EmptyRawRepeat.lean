import R1Z.PV_RDCD_EmptyRaw194
set_option autoImplicit false
namespace R1Z.PV_RDCD_EmptyRawRepeat
open Aeneas Aeneas.Std Result
open PV_RDCD_EmptyRaw194
/-- Source order of array Default's literal constructors, at the same world and
    primitive representation boundary as raw_four. -/
def repeated {World : Type} : Nat → World → Result (List EmptyRaw × World)
  | 0, world => ok ([],world)
  | n+1, world => do
    let (head,world1) ← rawNew 4#usize world
    let (tail,world2) ← repeated n world1
    ok (head::tail,world2)

theorem frame {World : Type} (n : Nat) (world : World) :
    repeated n world = ok (List.replicate n (⟨4#usize,0#usize⟩ : EmptyRaw),world) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [repeated,raw_four,bind_tc_ok]
    dsimp only
    rw [ih]
    rfl

theorem array10 {World : Type} (world : World) :
    repeated 10 world = ok (List.replicate 10 (⟨4#usize,0#usize⟩ : EmptyRaw),world) := frame 10 world

theorem array16 {World : Type} (world : World) :
    repeated 16 world = ok (List.replicate 16 (⟨4#usize,0#usize⟩ : EmptyRaw),world) := frame 16 world
#print axioms frame
#print axioms array10
#print axioms array16
end R1Z.PV_RDCD_EmptyRawRepeat
