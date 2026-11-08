import NNU_MerkleSlots
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNU_InactiveStructure
open Aeneas Aeneas.Std Result

def post {A B : Type} (f : A → B) (r : Result A) : Result B := do
 let x ← r
 ok (f x)

theorem post_bind {A B C : Type} (f : B → C) (r : Result A) (g : A → Result B) :
 post f (r >>= g) = r >>= fun x => post f (g x) := by
 cases r <;> rfl

theorem post_if {A B : Type} (f : A → B) (p : Prop) [Decidable p] (yes no : Result A) :
 post f (if p then yes else no) = if p then post f yes else post f no := by
 split <;> rfl

theorem post_ok {A B : Type} (f : A → B) (x : A) : post f (.ok x)=.ok (f x) := rfl

theorem limbs (words : Array U32 8#usize) :
 Port1_LibrarySource.fromLimbs words =
 post (Option.map FIo_Install.fromE)
  (FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs words) := by
 unfold FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs
 simp only [post_bind,post_if,post_ok,Option.map]
 rfl
#print axioms post_bind
#print axioms post_if
#print axioms post_ok
#print axioms limbs
end AspisR1.NNU_InactiveStructure
end
