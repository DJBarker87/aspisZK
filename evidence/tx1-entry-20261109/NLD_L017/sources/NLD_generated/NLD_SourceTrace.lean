import NJD_Trace
set_option autoImplicit false
namespace AspisR1.NLD_SourceTrace
open Aeneas Aeneas.Std Result
/-- Source-only occurrence log. Reuses NJD's checked failure/no-suffix algebra.
The occurrence number is its location in the pinned canonical emission. -/
abbrev Trace (A : Type) := NJD_Trace.Run Nat A
instance : Monad Trace where
  pure := NJD_Trace.pure
  bind := NJD_Trace.bind

def call {A : Type} (occurrence : Nat) (reply : Result A) : Trace A :=
  NJD_Trace.call occurrence reply

theorem erase_bind {A B : Type} (m : Trace A) (f : A → Trace B) :
    (m >>= f).2 = (m.2 >>= fun x => (f x).2) := NJD_Trace.erase_bind m f

theorem erase_call {A : Type} (i : Nat) (r : Result A) : (call i r).2 = r := rfl

theorem erase_pure {A : Type} (a : A) : (pure a : Trace A).2 = ok a := rfl

theorem erase_if {A : Type} (p : Prop) [Decidable p] (yes no : Trace A) :
    (if p then yes else no).2 = if p then yes.2 else no.2 := by split <;> rfl

theorem bind_congr {A B : Type} (r : Result A) (f g : A → Result B)
    (h : ∀ a, f a = g a) : (r >>= f) = (r >>= g) :=
  congrArg (fun k => r >>= k) (funext h)
#print axioms erase_bind
#print axioms erase_call
#print axioms erase_pure
#print axioms erase_if
#print axioms bind_congr
end AspisR1.NLD_SourceTrace
