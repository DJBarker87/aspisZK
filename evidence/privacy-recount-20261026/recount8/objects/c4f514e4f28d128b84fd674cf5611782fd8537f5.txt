import PV_B3P_FieldExt227
import PV_B3P_ArrayWrite227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

/-- Successful termination of the extraction Result; distinct from Rust Ok. -/
def Success {α : Type} (r : Result α) : Prop := ∃ value, r = .ok value

theorem ok {α : Type} (x : α) : Success (.ok x) := ⟨x,rfl⟩
theorem bind {α β : Type} (r : Result α) (f : α → Result β)
    (hr : Success r) (hf : ∀ x, Success (f x)) : Success (r >>= f) := by
  obtain ⟨x,hx⟩ := hr
  rw [hx]
  exact hf x

theorem index {α : Type} {n : Usize} (xs : Array α n) (i : Usize)
    (h : i.val < n.val) : Success (Array.index_usize xs i) :=
  ⟨_,PV_B3P_SelectIndex227.index_value xs i h⟩
theorem update {α : Type} {n : Usize} (xs : Array α n) (i : Usize) (x : α)
    (h : i.val < n.val) : Success (Array.update xs i x) :=
  ⟨_,PV_B3P_ArrayWrite227.update xs i h x⟩
theorem borrow {α : Type} {n : Usize} (xs : Array α n) (i : Usize)
    (h : i.val < n.val) : Success (Array.index_mut_usize xs i) :=
  ⟨_,PV_B3P_ArrayWrite227.borrow xs i h⟩

open PV_B3P_FieldBase227 PV_B3P_FieldExt227

theorem sub (x y : U32) : Success (aspis_core.field.M31.sub x y) := ⟨_,rfl⟩
theorem cnew (x y : U32) : Success (aspis_core.field.CM31.new x y) := ⟨_,rfl⟩
#print axioms sub
#print axioms cnew
theorem qadd (x y : Q) : Success (aspis_core.field.QM31.add x y) := ⟨_,qadd_result x y⟩
theorem qsub (x y : Q) : Success (aspis_core.field.QM31.sub x y) := ⟨_,qsub_result x y⟩
theorem qmul (x y : Q) : Success (aspis_core.field.QM31.mul x y) := ⟨_,qmul_result x y⟩
theorem cadd (x y : C) : Success (aspis_core.field.CM31.add x y) := ⟨_,cadd_result x y⟩
theorem csub (x y : C) : Success (aspis_core.field.CM31.sub x y) := ⟨_,csub_result x y⟩
theorem cmul (x y : C) : Success (aspis_core.field.CM31.mul x y) := ⟨_,cmul_result x y⟩
theorem add (x y : U32) : Success (aspis_core.field.M31.add x y) := ⟨_,add_result x y⟩
theorem mul (x y : U32) : Success (aspis_core.field.M31.mul x y) := ⟨_,mul_result x y⟩
theorem qsquare (x : Q) : Success (aspis_core.field.QM31.square x) := ⟨_,qsquare_result x⟩
theorem csquare (x : C) : Success (aspis_core.field.CM31.square x) := ⟨_,csquare_result x⟩
theorem reduce64 (x : U64) : Success (aspis_core.field.M31.reduce_u64 x) := ⟨_,reduce64_result x⟩
theorem reduce62 (x : U64) : Success (aspis_core.field.M31.reduce_u62 x) := ⟨_,reduce62_result x⟩
theorem double (x : U32) : Success (aspis_core.field.M31.double x) := ⟨_,double_result x⟩
theorem qmul_m31 (x : Q) (y : U32) : Success (aspis_core.field.QM31.mul_m31 x y) :=
  ⟨_,qmul_m31_result x y⟩
theorem cmul_m31 (x : C) (y : U32) : Success (aspis_core.field.CM31.mul_m31 x y) :=
  ⟨_,cmul_m31_result x y⟩

#print axioms ok
#print axioms bind
#print axioms index
#print axioms update
#print axioms borrow
#print axioms qadd
#print axioms qsub
#print axioms qmul
#print axioms cadd
#print axioms csub
#print axioms cmul
#print axioms add
#print axioms mul
#print axioms qsquare
#print axioms csquare
#print axioms reduce64
#print axioms reduce62
#print axioms double
#print axioms qmul_m31
#print axioms cmul_m31
/-- A well-founded loop rule. The invariant and decrease are required for every
continuation; no fuel execution or concrete field reduction is involved. -/
theorem loop_total {α β : Type} (body : α → Result (ControlFlow α β))
    (measure : α → Nat) (Inv : α → Prop)
    (step : ∀ a, Inv a → ∃ cf, body a = .ok cf ∧
      match cf with
      | .done _ => True
      | .cont a' => Inv a' ∧ measure a' < measure a)
    (a : α) (ha : Inv a) : Success (loop body a) := by
  suffices ∀ n a, Inv a → measure a = n → Success (loop body a) from this _ a ha rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro a ha hm
    obtain ⟨cf,hcf,hstep⟩ := step a ha
    rw [loop.eq_1]
    rw [hcf]
    cases cf with
    | done b => exact ok b
    | cont a' =>
      exact ih (measure a') (by simpa only [hm] using hstep.2) a' hstep.1 rfl

#print axioms loop_total
end PV_B3P_Success227
