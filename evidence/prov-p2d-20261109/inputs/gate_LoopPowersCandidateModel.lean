import CurrentPowersExactProduct
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error
namespace AspisR1LoopPowers

/-- [aspis_r1_current_powers::field::M31]
    Source: 'lib.rs', lines 3:0-3:24
    Visibility: public -/
@[reducible]
def field.M31 := Std.U32

/-- [aspis_r1_current_powers::field::CM31]
    Source: 'lib.rs', lines 5:0-8:1
    Visibility: public -/
structure field.CM31 where
  a : field.M31
  b : field.M31

/-- [aspis_r1_current_powers::field::QM31]
    Source: 'lib.rs', lines 10:0-13:1
    Visibility: public -/
structure field.QM31 where
  c0 : field.CM31
  c1 : field.CM31

/-- [aspis_r1_current_powers::field::WideExact]
    Source: 'lib.rs', lines 15:0-18:1
    Visibility: public -/
structure field.WideExact where
  c0 : field.QM31
  c1 : field.QM31


def toOldQM (x : field.QM31) : AspisR1PowersConcreteMul.CallbackQM :=
  ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def fromOldQM (x : AspisR1PowersConcreteMul.CallbackQM) : field.QM31 :=
  ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def toOld (x : field.WideExact) : AspisR1PowersConcreteMul.CallbackWide :=
  ⟨toOldQM x.c0,toOldQM x.c1⟩
def fromOld (x : AspisR1PowersConcreteMul.CallbackWide) : field.WideExact :=
  ⟨fromOldQM x.c0,fromOldQM x.c1⟩
theorem to_from_old (x : AspisR1PowersConcreteMul.CallbackWide) : toOld (fromOld x) = x := by rfl
theorem from_to_old (x : field.WideExact) : fromOld (toOld x) = x := by rfl

def Canonical (x : field.WideExact) : Prop := AspisR1PowersConcreteMul.Canonical (toOld x)
def decode (x : field.WideExact) : AspisWideTower.WideExact := AspisR1PowersExactProduct.decode (toOld x)
def field.WideExact.mul (x y : field.WideExact) : Result field.WideExact := do
  let z ← AspisR1PowersConcreteMul.sourceMul (toOld x) (toOld y)
  ok (fromOld z)

/-- [aspis_r1_current_powers::field::{aspis_r1_current_powers::field::QM31}::ZERO]
    Source: 'lib.rs', lines 20:0-29:6
    Visibility: public -/
@[global_simps, irreducible]
def field.QM31.ZERO : field.QM31 :=
  { c0 := { a := 0#u32, b := 0#u32 }, c1 := { a := 0#u32, b := 0#u32 } }

/-- [aspis_r1_current_powers::field::{aspis_r1_current_powers::field::QM31}::ONE]
    Source: 'lib.rs', lines 30:0-39:6
    Visibility: public -/
@[global_simps, irreducible]
def field.QM31.ONE : field.QM31 :=
  { c0 := { a := 1#u32, b := 0#u32 }, c1 := { a := 0#u32, b := 0#u32 } }

/-- [aspis_r1_current_powers::field::{aspis_r1_current_powers::field::WideExact}::ONE]
    Source: 'lib.rs', lines 42:0-45:6
    Visibility: public -/
@[global_simps, irreducible]
def field.WideExact.ONE : field.WideExact :=
  { c0 := field.QM31.ONE, c1 := field.QM31.ZERO }

/-- [aspis_r1_current_powers::weights::powers]: loop body 0:
    Source: 'lib.rs', lines 54:1-58:2
    Visibility: public -/
@[rust_loop_body]
def weights.powers_loop.body
  {N : Std.Usize} (x : field.WideExact) (out : Array field.WideExact N)
  (p : field.WideExact) (i : Std.Usize) :
  Result (ControlFlow ((Array field.WideExact N) × field.WideExact ×
    Std.Usize) (Array field.WideExact N))
  := do
  if i < N
  then
    let a ← Array.update out i p
    let p1 ← field.WideExact.mul p x
    let i1 ← i + 1#usize
    ok (cont (a, p1, i1))
  else ok (done out)

/-- [aspis_r1_current_powers::weights::powers]: loop 0:
    Source: 'lib.rs', lines 54:1-58:2
    Visibility: public -/
@[rust_loop]
def weights.powers_loop
  {N : Std.Usize} (x : field.WideExact) (out : Array field.WideExact N)
  (p : field.WideExact) (i : Std.Usize) :
  Result (Array field.WideExact N)
  := do
  loop
    (fun (out1, p1, i1) => weights.powers_loop.body x out1 p1 i1)
    (out, p, i)

/-- [aspis_r1_current_powers::weights::powers]:
    Source: 'lib.rs', lines 50:0-60:1
    Visibility: public -/
def weights.powers
  (N : Std.Usize) (x : field.WideExact) :
  Result (Array field.WideExact N)
  := do
  let out := Array.repeat N field.WideExact.ONE
  weights.powers_loop x out field.WideExact.ONE 0#usize

/-- [aspis_r1_current_powers::powers_entry]:
    Source: 'lib.rs', lines 62:0-62:88
    Visibility: public -/
def powers_entry
  (x : field.WideExact) : Result (Array field.WideExact 29#usize) := do
  weights.powers 29#usize x



theorem mul_total_exact (x y : field.WideExact) (hx : Canonical x) (hy : Canonical y) :
    ∃ z, field.WideExact.mul x y = .ok z ∧ Canonical z ∧ decode z = decode x * decode y := by
  obtain ⟨z,hz,hc,he⟩ := AspisR1PowersExactProduct.sourceMul_total_exact (toOld x) (toOld y) hx hy
  refine ⟨fromOld z,?_,?_,?_⟩
  · simp only [field.WideExact.mul,hz,bind_tc_ok]
  · simpa only [Canonical,to_from_old] using hc
  · simpa only [decode,to_from_old] using he

#print axioms to_from_old
#print axioms from_to_old
#print axioms mul_total_exact
end AspisR1LoopPowers
