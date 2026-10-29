import PV_B3P_Success227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

/-- Symbolic reflexivity of the actual imported array-comparison body. -/
theorem list_self {T : Type} (cmp : core.cmp.PartialEq T T)
    (hn : ∀ x, cmp.ne x x = .ok false) (xs : List T) :
    List.allM (fun (x,y) => do let b ← cmp.ne x y; .ok (¬b)) (xs.zip xs) = .ok true := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.zip_cons_cons,List.allM_cons,hn,bind_tc_ok,↓reduceIte]
    exact ih

theorem array_ne_self {T : Type} {n : Usize} (cmp : core.cmp.PartialEq T T)
    (hn : ∀ x, cmp.ne x x = .ok false) (a : Array T n) :
    core.array.equality.PartialEqArray.ne cmp a a = .ok false := by
  rw [core.array.equality.PartialEqArray.ne,core.array.equality.PartialEqArray.eq]
  rw [if_pos rfl,list_self cmp hn a.val]
  rfl

theorem byte_ne_self (x : U8) : core.cmp.PartialEqU8.ne x x = .ok false := by
  change Result.ok (decide (x ≠ x)) = Result.ok false
  simp only [ne_self_iff_false,decide_false]

theorem word_ne_self (x : U32) :
    aspis_core.field.M31.Insts.CoreCmpPartialEqM31.ne x x = .ok false := by
  simp only [core.cmp.PartialEq.ne.trait_default,core.cmp.PartialEq.ne.default,
    aspis_core.field.M31.Insts.CoreCmpPartialEqM31,
    aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq,
    decide_true,eq_self,bind_tc_ok,Bool.not_true]

theorem bytes_ne_self {n : Usize} (a : Array U8 n) :
    core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 a a = .ok false :=
  array_ne_self _ byte_ne_self a

theorem digest_ne_self (a : Array U32 8#usize) :
    core.array.equality.PartialEqArray.ne aspis_core.field.M31.Insts.CoreCmpPartialEqM31 a a = .ok false :=
  array_ne_self _ word_ne_self a

#print axioms list_self
#print axioms array_ne_self
#print axioms byte_ne_self
#print axioms word_ne_self
#print axioms bytes_ne_self
#print axioms digest_ne_self
end PV_B3P_Success227
