import NND_ScalarComparison
import RSL_Pool
set_option autoImplicit false
namespace NND_Carrier
open Aeneas Aeneas.Std AdapterRw

def digest (x : Array aspis_core.field.M31 8#usize) : RSL.Digest := x.val.map word
def frontier (x : Array (Array aspis_core.field.M31 8#usize) 20#usize) : List RSL.Digest := x.val.map digest
def slots (x : Array U64 8#usize) : List UInt64 := x.val.map slot

theorem map_array_injective {A B : Type} {N : Usize} (f : A → B) (hf : Function.Injective f) :
 Function.Injective (fun x : Array A N => x.val.map f) := by
 intro x y h
 apply Subtype.ext
 have inj : ∀ (xs ys : List A), xs.map f = ys.map f → xs = ys := by
  intro xs
  induction xs with
  | nil => intro ys h; cases ys <;> simp_all
  | cons x xs ih =>
    intro ys h
    cases ys with
    | nil => simp at h
    | cons y ys =>
      simp only [List.map_cons,List.cons.injEq] at h
      rw [hf h.1,ih ys h.2]
 exact inj _ _ h

theorem word_injective : Function.Injective word := by
 intro x y h
 exact (word_back x).symm.trans ((congrArg unword h).trans (word_back y))

theorem digest_injective : Function.Injective digest := map_array_injective word word_injective
theorem frontier_injective : Function.Injective frontier := map_array_injective digest digest_injective
theorem slots_injective : Function.Injective slots := map_array_injective slot slot_injective

theorem digest_length (x : Array aspis_core.field.M31 8#usize) : (digest x).length = 8 := by simp [digest,x.property]
theorem frontier_length (x : Array (Array aspis_core.field.M31 8#usize) 20#usize) : (frontier x).length = 20 := by simp [frontier,x.property]
theorem slots_length (x : Array U64 8#usize) : (slots x).length = 8 := by simp [slots,x.property]

#print axioms map_array_injective
#print axioms word_injective
#print axioms digest_injective
#print axioms frontier_injective
#print axioms slots_injective
#print axioms digest_length
#print axioms frontier_length
#print axioms slots_length
end NND_Carrier
