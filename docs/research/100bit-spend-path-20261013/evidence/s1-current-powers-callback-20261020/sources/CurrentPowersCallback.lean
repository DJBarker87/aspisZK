import Aeneas
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error
namespace AspisR1CurrentPowers


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

/-- [aspis_r1_current_powers::weights::powers::closure]
    Source: 'lib.rs', lines 50:81-50:107 -/
def weights.powers.closure (N : Std.Usize) :=
  field.WideExact × field.WideExact

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

/-- [aspis_r1_current_powers::weights::powers::{impl core::ops::function::FnMut<(usize,), aspis_r1_current_powers::field::WideExact> for aspis_r1_current_powers::weights::powers::closure<'_0, '_1, N>}::call_mut]:
    Source: 'lib.rs', lines 50:81-50:107 -/
def
  weights.powers.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
  (mul : field.WideExact → field.WideExact → Result field.WideExact) {N : Std.Usize} (c : weights.powers.closure N) (tupled_args : Std.Usize) :
  Result (field.WideExact × (weights.powers.closure N) ×
    (weights.powers.closure N → weights.powers.closure N))
  := do
  let (a, we) := c
  let we1 ← mul a we
  let back := fun c1 => let (we2, _) := c1
                        (we2, we)
  ok (a, (we1, we), back)

/-- [aspis_r1_current_powers::weights::powers::{impl core::ops::function::FnOnce<(usize,), aspis_r1_current_powers::field::WideExact> for aspis_r1_current_powers::weights::powers::closure<'_0, '_1, N>}::call_once]:
    Source: 'lib.rs', lines 50:81-50:107 -/
def
  weights.powers.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeWideExact.call_once
  (mul : field.WideExact → field.WideExact → Result field.WideExact) {N : Std.Usize} (c : weights.powers.closure N) (i : Std.Usize) :
  Result (field.WideExact × (weights.powers.closure N))
  := do
  let (_, we) := c
  let (we1, c1, call_mut_back) ←
    weights.powers.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
      mul c i
  let (we2, _) := call_mut_back c1
  ok (we1, (we2, we))



theorem call_once_of_mul (mul : field.WideExact → field.WideExact → Result field.WideExact)
    {N : Usize} (p x next : field.WideExact) (i : Usize)
    (h : mul p x = .ok next) :
    weights.powers.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeWideExact.call_once
      mul (N := N) (p,x) i = .ok (p,(next,x)) := by
  simp [weights.powers.closure,
    weights.powers.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeWideExact.call_once,
    weights.powers.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut, h]

theorem call_once_success_mul (mul : field.WideExact → field.WideExact → Result field.WideExact)
    {N : Usize} (p x value : field.WideExact) (next : weights.powers.closure N) (i : Usize)
    (h : weights.powers.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeWideExact.call_once
      mul (N := N) (p,x) i = .ok (value,next)) :
    ∃ product, mul p x = .ok product ∧ value = p ∧ next = (product,x) := by
  cases hm : mul p x with
  | fail e =>
    simp [weights.powers.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeWideExact.call_once,
      weights.powers.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut, hm] at h
  | div =>
    simp [weights.powers.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeWideExact.call_once,
      weights.powers.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut, hm] at h
  | ok product =>
    have he := (call_once_of_mul mul (N := N) p x product i hm).symm.trans h
    have hp := Result.ok.inj he
    cases hp
    exact ⟨product, rfl, rfl, rfl⟩

/-- Index independence and state preservation are properties of the emitted
callback body. Actual multiplication and the borrowing from_fn owner remain separate. -/
theorem call_once_index_independent
    (mul : field.WideExact → field.WideExact → Result field.WideExact)
    {N : Usize} (state : weights.powers.closure N) (i j : Usize) :
    weights.powers.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeWideExact.call_once mul state i =
    weights.powers.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeWideExact.call_once mul state j := by rfl

#print axioms call_once_of_mul
#print axioms call_once_success_mul
#print axioms call_once_index_independent
end AspisR1CurrentPowers
