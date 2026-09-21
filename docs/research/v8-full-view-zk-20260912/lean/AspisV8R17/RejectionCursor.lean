import AspisV8R17.BoundedRejection

/-! A bounded rejection scan retaining the unconsumed word suffix. Each limb
starts at the previous limb's cursor, not at a fixed eight-word boundary.
No oracle distribution or Rust refinement is assumed here. -/
set_option autoImplicit false
namespace AspisV8R17.RejectionCursor
open AspisV8R17.BoundedRejection
variable {D : Type*}

def scan (accept : D → Bool) : ℕ → List D → Option (D × List D)
  | 0, _ => none
  | _+1, [] => none
  | n+1, x::xs => if accept x then some (x,xs) else scan accept n xs

theorem scan_projection (accept : D → Bool) (n : ℕ) (xs : List D) :
    (scan accept n xs).map Prod.fst = firstAccepted accept (xs.take n) := by
  induction n generalizing xs with
  | zero => simp [scan, firstAccepted]
  | succ n ih =>
    cases xs with
    | nil => simp [scan, firstAccepted]
    | cons x xs => cases hx : accept x <;> simp [scan, firstAccepted, hx, ih]

theorem scan_of_prefix (accept : D → Bool) (pref : List D) (x : D) (rest : List D)
    (n : ℕ) (rejects : ∀ y ∈ pref, accept y = false)
    (accepts : accept x = true) (fits : pref.length < n) :
    scan accept n (pref ++ x::rest) = some (x,rest) := by
  induction pref generalizing n with
  | nil => cases n <;> simp_all [scan]
  | cons y ys ih =>
    cases n with
    | zero => simp at fits
    | succ n =>
      have hy := rejects y (by simp)
      have hr : ∀ z ∈ ys, accept z = false := by
        intro z hz
        exact rejects z (by simp [hz])
      simpa [scan, hy] using ih n hr (by simpa using fits)

theorem scan_success_prefix (accept : D → Bool) (n : ℕ) (xs : List D)
    (x : D) (rest : List D) (h : scan accept n xs = some (x,rest)) :
    ∃ pref, xs = pref ++ x::rest ∧ pref.length < n ∧
      (∀ y ∈ pref, accept y = false) ∧ accept x = true := by
  induction n generalizing xs with
  | zero => simp [scan] at h
  | succ n ih =>
    cases xs with
    | nil => simp [scan] at h
    | cons y ys =>
      cases hy : accept y with
      | true =>
        simp [scan, hy] at h
        rcases h with ⟨rfl, rfl⟩
        exact ⟨[], by simp, by simp, by simp, hy⟩
      | false =>
        have hs : scan accept n ys = some (x,rest) := by simpa [scan, hy] using h
        obtain ⟨p, hp, hn, hr, ha⟩ := ih ys hs
        refine ⟨y::p, by simp [hp], by simpa using hn, ?_, ha⟩
        intro z hz
        simp only [List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact hy
        · exact hr z hz

theorem scan_success_iff (accept : D → Bool) (n : ℕ) (xs : List D)
    (x : D) (rest : List D) :
    scan accept n xs = some (x,rest) ↔
      ∃ pref, xs = pref ++ x::rest ∧ pref.length < n ∧
        (∀ y ∈ pref, accept y = false) ∧ accept x = true := by
  constructor
  · exact scan_success_prefix accept n xs x rest
  · rintro ⟨pref, rfl, hn, hr, ha⟩
    exact scan_of_prefix accept pref x rest n hr ha hn

def scanMany (accept : D → Bool) (fuel : ℕ) : ℕ → List D → Option (List D × List D)
  | 0, xs => some ([],xs)
  | limbs+1, xs => do
    let (x, rest) ← scan accept fuel xs
    let (values, tail) ← scanMany accept fuel limbs rest
    pure (x::values, tail)

theorem scanMany_success (accept : D → Bool) (fuel limbs : ℕ)
    (xs values tail : List D) (h : scanMany accept fuel limbs xs = some (values,tail)) :
    values.length = limbs ∧ (∀ x ∈ values, accept x = true) ∧
      ∃ consumed, xs = consumed ++ tail ∧ consumed.length ≤ fuel * limbs := by
  induction limbs generalizing xs values with
  | zero =>
    simp [scanMany] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨rfl, by simp, [], by simp, by simp⟩
  | succ limbs ih =>
    cases hs : scan accept fuel xs with
    | none => simp [scanMany, hs] at h
    | some pair =>
      rcases pair with ⟨x,rest⟩
      cases hm : scanMany accept fuel limbs rest with
      | none => simp [scanMany, hs, hm] at h
      | some pair =>
        rcases pair with ⟨vs,ts⟩
        simp [scanMany, hs, hm] at h
        rcases h with ⟨rfl, rfl⟩
        obtain ⟨hlen, hv, used, hused, hbound⟩ := ih rest vs hm
        obtain ⟨pref, hpref, hpbound, hreject, hx⟩ := scan_success_prefix accept fuel xs x rest hs
        refine ⟨by simp [hlen], ?_, pref ++ x::used, ?_, ?_⟩
        · intro y hy
          simp only [List.mem_cons] at hy
          rcases hy with rfl | hy
          · exact hx
          · exact hv y hy
        · simp [hpref, hused, List.append_assoc]
        · simp only [List.length_append, List.length_cons]
          have hp : pref.length + 1 ≤ fuel := hpbound
          calc
            pref.length + (used.length + 1) = (pref.length + 1) + used.length := by omega
            _ ≤ fuel + fuel * limbs := Nat.add_le_add hp hbound
            _ = fuel * (limbs + 1) := by rw [Nat.mul_succ, Nat.add_comm]

#print axioms scanMany_success
#print axioms scan_projection
#print axioms scan_of_prefix
#print axioms scan_success_prefix
#print axioms scan_success_iff
end AspisV8R17.RejectionCursor
