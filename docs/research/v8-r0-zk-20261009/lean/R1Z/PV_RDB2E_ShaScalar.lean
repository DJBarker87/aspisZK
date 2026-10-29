import Aeneas
/-! Logical scalar projection of sha2-0.10.9 soft.rs. This is an owned
model, not an extraction and not a proof of intrinsic/source adequacy. -/
namespace R1Z.PV_RDB2E_ShaScalar
set_option autoImplicit false
abbrev W := BitVec 32
structure V where
  a : W
  b : W
  c : W
  d : W
  deriving DecidableEq
structure S where
  a : W
  b : W
  c : W
  d : W
  e : W
  f : W
  g : W
  h : W
  deriving DecidableEq

def sigma0 (x : W) : W := x.rotateRight 7 ^^^ x.rotateRight 18 ^^^ (x >>> 3)
def sigma1 (x : W) : W := x.rotateRight 17 ^^^ x.rotateRight 19 ^^^ (x >>> 10)
def big0 (x : W) : W := x.rotateRight 2 ^^^ x.rotateRight 13 ^^^ x.rotateRight 22
def big1 (x : W) : W := x.rotateRight 6 ^^^ x.rotateRight 11 ^^^ x.rotateRight 25
def choose (a b c : W) : W := c ^^^ (a &&& (b ^^^ c))
def majority (a b c : W) : W := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
def round (s : S) (wk : W) : S :=
  let x := ((big1 s.e + choose s.e s.f s.g) + wk) + s.h
  let y := big0 s.a + majority s.a s.b s.c
  ⟨x+y,s.a,s.b,s.c,x+s.d,s.e,s.f,s.g⟩
def abef (s : S) : V := ⟨s.a,s.b,s.e,s.f⟩
def cdgh (s : S) : V := ⟨s.c,s.d,s.g,s.h⟩
def join (ab cd : V) : S := ⟨ab.a,ab.b,cd.a,cd.b,ab.c,ab.d,cd.c,cd.d⟩
def add (x y : V) : V := ⟨x.a+y.a,x.b+y.b,x.c+y.c,x.d+y.d⟩
def swap (x : V) : V := ⟨x.c,x.d,x.a,x.b⟩
def load (x y : V) : V := ⟨y.d,x.a,x.b,x.c⟩
def msg1 (x y : V) : V :=
  let z := load x y
  add x ⟨sigma0 z.a,sigma0 z.b,sigma0 z.c,sigma0 z.d⟩
def msg2 (x y : V) : V :=
  let w16 := x.d + sigma1 y.b
  let w17 := x.c + sigma1 y.a
  let w18 := x.b + sigma1 w16
  let w19 := x.a + sigma1 w17
  ⟨w19,w18,w17,w16⟩
def schedule (v0 v1 v2 v3 : V) : V := msg2 (add (msg1 v0 v1) (load v2 v3)) v3
/-- Direct source lane projection of the two unrolled rounds. -/
def round2 (cd ab wk : V) : V :=
  let a0:=ab.a; let b0:=ab.b; let e0:=ab.c; let f0:=ab.d
  let c0:=cd.a; let d0:=cd.b; let g0:=cd.c; let h0:=cd.d
  let x0 := ((big1 e0 + choose e0 f0 g0) + wk.d) + h0
  let y0 := big0 a0 + majority a0 b0 c0
  let a1:=x0+y0; let b1:=a0; let e1:=x0+d0; let f1:=e0
  let c1:=b0; let d1:=c0; let g1:=f0; let h1:=g0
  let x1 := ((big1 e1 + choose e1 f1 g1) + wk.c) + h1
  let y1 := big0 a1 + majority a1 b1 c1
  ⟨x1+y1,a1,x1+d1,e1⟩
def rounds4 (ab cd rest k : V) : V × V :=
  let t1 := add rest k
  let cd1 := round2 cd ab t1
  let ab1 := round2 ab cd1 (swap t1)
  (ab1,cd1)
def four (s : S) (wk : V) : S :=
  round (round (round (round s wk.d) wk.c) wk.b) wk.a

theorem round2_source (s : S) (wk : V) :
    round2 (cdgh s) (abef s) wk=abef (round (round s wk.d) wk.c) := rfl

theorem round2_retained (s : S) (wk : V) :
    cdgh (round (round s wk.d) wk.c)=abef s := rfl

theorem four_source (s : S) (rest k : V) :
    join (rounds4 (abef s) (cdgh s) rest k).1
      (rounds4 (abef s) (cdgh s) rest k).2=four s (add rest k) := rfl

#print axioms round2_source
#print axioms round2_retained
#print axioms four_source
end R1Z.PV_RDB2E_ShaScalar
