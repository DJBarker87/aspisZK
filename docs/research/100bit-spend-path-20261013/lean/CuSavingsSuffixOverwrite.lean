import Aeneas

/-! Symbolic indexed overwrite for mutable-iterator handbacks. The replacement
list is independent of the original values; equality of lengths is explicit. -/
set_option autoImplicit false
namespace AspisR1.CuSavingsSuffixOverwrite
variable {T : Type}

def overwrite : Nat → List T → List T → List T
  | 0, _, ys => ys
  | _+1, [], _ => []
  | _+1, xs, [] => xs
  | n+1, x::xs, _::ys => x::overwrite n xs ys

theorem length_overwrite (n : Nat) (xs ys : List T) (hlen : xs.length = ys.length) :
    (overwrite n xs ys).length = xs.length := by
  induction n generalizing xs ys with
  | zero => simpa only [overwrite] using hlen.symm
  | succ n ih =>
    cases xs with
    | nil => rfl
    | cons x xs =>
      cases ys with
      | nil => rfl
      | cons y ys =>
        simp only [List.length_cons,Nat.add_right_cancel_iff] at hlen
        simp only [overwrite,List.length_cons,ih xs ys hlen]

theorem overwrite_at_length (xs ys : List T) (hlen : xs.length = ys.length) :
    overwrite xs.length xs ys = xs := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all only [List.length_nil,List.length_cons,overwrite]
  | cons x xs ih =>
    cases ys with
    | nil => simp only [List.length_nil,List.length_cons] at hlen;omega
    | cons y ys =>
      simp only [List.length_cons,Nat.add_right_cancel_iff] at hlen
      simp only [List.length_cons,overwrite,ih ys hlen]

theorem overwrite_step (n : Nat) (xs ys : List T) (hlen : xs.length = ys.length)
    (hn : n < ys.length) :
    (overwrite (n+1) xs ys).set n (ys[n]'hn) = overwrite n xs ys := by
  induction n generalizing xs ys with
  | zero =>
    cases ys with
    | nil => simp only [List.length_nil] at hn;omega
    | cons y ys =>
      cases xs with
      | nil => simp only [List.length_nil,List.length_cons] at hlen;omega
      | cons x xs => rfl
  | succ n ih =>
    cases ys with
    | nil => simp only [List.length_nil] at hn;omega
    | cons y ys =>
      cases xs with
      | nil => simp only [List.length_nil,List.length_cons] at hlen;omega
      | cons x xs =>
        have hn' : n < ys.length := by simpa only [List.length_cons,Nat.add_lt_add_iff_right] using hn
        have hlen' : xs.length = ys.length := by simpa only [List.length_cons,Nat.add_right_cancel_iff] using hlen
        simpa only [overwrite,List.set_cons_succ,List.getElem_cons_succ] using
          congrArg (List.cons x) (ih xs ys hlen' hn')

#print axioms length_overwrite
#print axioms overwrite_at_length
#print axioms overwrite_step
end AspisR1.CuSavingsSuffixOverwrite
