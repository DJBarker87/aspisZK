import NNG_EmittedContext
set_option autoImplicit false
namespace AspisR1.NNG_Array136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted

def get {A : Type} {n : Usize} (a : Array A n) (i : Usize) (h : i.val < n.val) : A :=
  a.val[i.val]'(by rw [a.property]; exact h)

/-- Symbolic fixed-array selection from the accepted standard-library law. -/
theorem index {A : Type} {n : Usize} (a : Array A n) (i : Usize) (h : i.val < n.val) :
    Array.index_usize a i = .ok (get a i h) := by
  have hb : i.val < a.length := by
    change i.val < a.val.length
    rw [a.property]
    exact h
  obtain ⟨x,returned,value⟩ := WP.spec_imp_exists (Array.index_usize_spec a i hb)
  exact returned.trans (congrArg Result.ok value)
#print axioms index

def row0 (claims : Claims) : K29 := get claims 0#usize (by decide)
def at (claims : Claims) (i : Usize) (h : i.val < 29) : Q := get (row0 claims) i h
end AspisR1.NNG_Array136
