import R1Z.PV_RDB2E_FallbackArray4

section
-- Unchanged source component R1Z.PV_CBL_FallbackScalar
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackScalar
set_option autoImplicit false
abbrev big0 (x : U32) : U32 :=
  core.num.U32.rotate_right x 2#u32 ^^^ core.num.U32.rotate_right x 13#u32 ^^^ core.num.U32.rotate_right x 22#u32
abbrev big1 (x : U32) : U32 :=
  core.num.U32.rotate_right x 6#u32 ^^^ core.num.U32.rotate_right x 11#u32 ^^^ core.num.U32.rotate_right x 25#u32
abbrev choose (x y z : U32) : U32 := z ^^^ (x &&& (y ^^^ z))
abbrev majority (x y z : U32) : U32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)
abbrev t1 (e f g h w : U32) : U32 :=
  U32.wrapping_add (U32.wrapping_add (U32.wrapping_add (big1 e) (choose e f g)) w) h
abbrev t2 (a b c : U32) : U32 := U32.wrapping_add (big0 a) (majority a b c)
structure State where
  a : U32
  b : U32
  c : U32
  d : U32
  e : U32
  f : U32
  g : U32
  h : U32
def step (s : State) (w : U32) : State :=
  ⟨U32.wrapping_add (t1 s.e s.f s.g s.h w) (t2 s.a s.b s.c),
    s.a,s.b,s.c,U32.wrapping_add (t1 s.e s.f s.g s.h w) s.d,s.e,s.f,s.g⟩
#print axioms big0
#print axioms big1
#print axioms choose
#print axioms majority
#print axioms t1
#print axioms t2
#print axioms step
end R1Z.PV_CBL_FallbackScalar

end
