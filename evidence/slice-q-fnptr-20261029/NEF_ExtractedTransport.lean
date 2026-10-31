import NEF_Reference.Funs
import NEF_InvSpecialisation
set_option autoImplicit false
namespace NEF_ExtractedTransport
open Aeneas Aeneas.Std Result NEF_Reference
abbrev Exec := StateT NEF_Log Result

def mul (a b : U32) : Exec U32 := fun s => NEF_Log.mul s a b
def add (a b : U32) : Exec U32 := fun s => NEF_Log.add s a b
def neg (a : U32) : Exec U32 := fun s => NEF_Log.neg s a
def inv (a : U32) : Exec U32 := fun s => NEF_Log.inv s a

theorem run_bind {A B : Type} (f : Exec A) (k : A → Exec B) (s : NEF_Log) :
    (f >>= k) s = (do let (a,s') ← f s; k a s') := rfl

theorem run_pure {A : Type} (a : A) (s : NEF_Log) :
    (pure a : Exec A) s = ok (a,s) := rfl

theorem result_bind_assoc {A B C : Type} (r : Result A)
    (f : A → Result B) (g : B → Result C) :
    ((r >>= f) >>= g) = (r >>= fun a => f a >>= g) := by
  cases r <;> rfl

/-- Full emitted Result and log state, including bounds/overflow failures. -/
theorem extracted_static (x : NEF_CM) (s : NEF_Log) :
    NEF_inv_static x s = (do
      let (v, s') ← NEF.invStatic mul add neg inv (⟨x.a,x.b⟩ : NEF.CM U32) s
      ok (⟨v.a,v.b⟩,s')) := by
  cases h0 : NEF_Log.mul s x.a x.a with
  | ok pair =>
    rcases pair with ⟨aa,s1⟩
    cases h1 : NEF_Log.mul s1 x.b x.b with
    | ok pair =>
      rcases pair with ⟨bb,s2⟩
      cases h2 : NEF_Log.add s2 aa bb with
      | ok pair =>
        rcases pair with ⟨norm,s3⟩
        cases h3 : NEF_Log.inv s3 norm with
        | ok pair =>
          rcases pair with ⟨iv,s4⟩
          cases h4 : NEF_Log.mul s4 x.a iv with
          | ok pair =>
            rcases pair with ⟨a,s5⟩
            cases h5 : NEF_Log.neg s5 x.b with
            | ok pair =>
              rcases pair with ⟨nb,s6⟩
              cases h6 : NEF_Log.mul s6 nb iv with
              | ok pair =>
                rcases pair with ⟨b,s7⟩
                simp only [NEF_inv_static, NEF.invStatic, mul, add, neg, inv, run_bind, run_pure, h0, h1, h2, h3, h4, h5, h6, bind_tc_ok, bind_tc_fail, bind_tc_div, Aeneas.Std.uncurry]
              | fail error => simp only [NEF_inv_static, NEF.invStatic, mul, add, neg, inv, run_bind, run_pure, h0, h1, h2, h3, h4, h5, h6, bind_tc_ok, bind_tc_fail, bind_tc_div, Aeneas.Std.uncurry]
              | div => simp only [NEF_inv_static, NEF.invStatic, mul, add, neg, inv, run_bind, run_pure, h0, h1, h2, h3, h4, h5, h6, bind_tc_ok, bind_tc_fail, bind_tc_div, Aeneas.Std.uncurry]
            | fail error => simp only [NEF_inv_static, NEF.invStatic, mul, add, neg, inv, run_bind, run_pure, h0, h1, h2, h3, h4, h5, bind_tc_ok, bind_tc_fail, bind_tc_div, Aeneas.Std.uncurry]
            | div => simp only [NEF_inv_static, NEF.invStatic, mul, add, neg, inv, run_bind, run_pure, h0, h1, h2, h3, h4, h5, bind_tc_ok, bind_tc_fail, bind_tc_div, Aeneas.Std.uncurry]
          | fail error => simp only [NEF_inv_static, NEF.invStatic, mul, add, neg, inv, run_bind, run_pure, h0, h1, h2, h3, h4, bind_tc_ok, bind_tc_fail, bind_tc_div, Aeneas.Std.uncurry]
          | div => simp only [NEF_inv_static, NEF.invStatic, mul, add, neg, inv, run_bind, run_pure, h0, h1, h2, h3, h4, bind_tc_ok, bind_tc_fail, bind_tc_div, Aeneas.Std.uncurry]
        | fail error => simp only [NEF_inv_static, NEF.invStatic, mul, add, neg, inv, run_bind, run_pure, h0, h1, h2, h3, bind_tc_ok, bind_tc_fail, bind_tc_div, Aeneas.Std.uncurry]
        | div => simp only [NEF_inv_static, NEF.invStatic, mul, add, neg, inv, run_bind, run_pure, h0, h1, h2, h3, bind_tc_ok, bind_tc_fail, bind_tc_div, Aeneas.Std.uncurry]
      | fail error => simp only [NEF_inv_static, NEF.invStatic, mul, add, neg, inv, run_bind, run_pure, h0, h1, h2, bind_tc_ok, bind_tc_fail, bind_tc_div, Aeneas.Std.uncurry]
      | div => simp only [NEF_inv_static, NEF.invStatic, mul, add, neg, inv, run_bind, run_pure, h0, h1, h2, bind_tc_ok, bind_tc_fail, bind_tc_div, Aeneas.Std.uncurry]
    | fail error => simp only [NEF_inv_static, NEF.invStatic, mul, add, neg, inv, run_bind, run_pure, h0, h1, bind_tc_ok, bind_tc_fail, bind_tc_div, Aeneas.Std.uncurry]
    | div => simp only [NEF_inv_static, NEF.invStatic, mul, add, neg, inv, run_bind, run_pure, h0, h1, bind_tc_ok, bind_tc_fail, bind_tc_div, Aeneas.Std.uncurry]
  | fail error => simp only [NEF_inv_static, NEF.invStatic, mul, add, neg, inv, run_bind, run_pure, h0, bind_tc_ok, bind_tc_fail, bind_tc_div, Aeneas.Std.uncurry]
  | div => simp only [NEF_inv_static, NEF.invStatic, mul, add, neg, inv, run_bind, run_pure, h0, bind_tc_ok, bind_tc_fail, bind_tc_div, Aeneas.Std.uncurry]

/-- The fixed-backend source and the extracted static reference have identical
state+Result semantics. No pointer representation enters this statement. -/
theorem extracted_specialisation (x : NEF_CM) (s : NEF_Log) :
    NEF_inv_static x s = (do
      let (v, s') ← NEF.invWith mul add neg inv (⟨x.a,x.b⟩ : NEF.CM U32) s
      ok (⟨v.a,v.b⟩,s')) := by
  rw [NEF.inv_with_static]
  exact extracted_static x s
#print axioms run_bind
#print axioms run_pure
#print axioms result_bind_assoc
#print axioms extracted_static
#print axioms extracted_specialisation
end NEF_ExtractedTransport
