import Aeneas

/-! Symbolic list identities for the mutable-iterator handback. Prove one
generic suffix-map step rather than reducing a concrete four-step term. -/
set_option autoImplicit false
namespace AspisR1.CuSavingsSuffixMap
variable {T : Type}

def suffixMap (f : T → T) : Nat → List T → List T
  | 0, xs => xs.map f
  | _+1, [] => []
  | n+1, x::xs => x::suffixMap f n xs

theorem length_suffixMap (f : T → T) (n : Nat) (xs : List T) :
    (suffixMap f n xs).length = xs.length := by
  induction n generalizing xs with
  | zero => simp only [suffixMap,List.length_map]
  | succ n ih => cases xs <;> simp only [suffixMap,List.length_nil,List.length_cons,ih]

theorem suffixMap_at_length (f : T → T) (xs : List T) :
    suffixMap f xs.length xs = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.length_cons,suffixMap,ih]

theorem suffixMap_step (f : T → T) (n : Nat) (xs : List T) (hn : n < xs.length) :
    (suffixMap f (n+1) xs).set n (f (xs[n]'hn)) = suffixMap f n xs := by
  induction n generalizing xs with
  | zero =>
    cases xs with
    | nil => simp only [List.length_nil] at hn;omega
    | cons x xs => rfl
  | succ n ih =>
    cases xs with
    | nil => simp only [List.length_nil] at hn;omega
    | cons x xs =>
      have hn' : n < xs.length := by simpa only [List.length_cons,Nat.add_lt_add_iff_right] using hn
      simpa only [suffixMap,List.set_cons_succ,List.getElem_cons_succ] using
        congrArg (List.cons x) (ih xs hn')

#print axioms length_suffixMap
#print axioms suffixMap_at_length
#print axioms suffixMap_step
end AspisR1.CuSavingsSuffixMap
