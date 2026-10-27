import R1Z.PV_Op134_DedupTransport
namespace R1Z.PV_Op134_Union
set_option autoImplicit false

def union (xs : List Nat) : Nat := xs.foldr (fun a b => a ||| b) 0

theorem bits (xs : List Nat) (bit : Nat) :
    (union xs).testBit bit = true ↔ ∃ x ∈ xs, x.testBit bit = true := by
  induction xs with
  | nil => simp [union]
  | cons x xs ih =>
    change (x ||| union xs).testBit bit = true ↔ _
    simp only [Nat.testBit_or,Bool.or_eq_true,ih,List.mem_cons]
    constructor
    · rintro (hx | ⟨y,hy,hb⟩)
      · exact ⟨x,Or.inl rfl,hx⟩
      · exact ⟨y,Or.inr hy,hb⟩
    · rintro ⟨y,(hy | hy),hb⟩
      · subst y; exact Or.inl hb
      · exact Or.inr ⟨y,hy,hb⟩

theorem membership (xs ys : List Nat) (hm : ∀ x, x ∈ xs ↔ x ∈ ys) :
    union xs = union ys := by
  apply Nat.eq_of_testBit_eq
  intro bit
  have hm' : (∃ x ∈ xs, x.testBit bit = true) ↔ (∃ x ∈ ys, x.testBit bit = true) := by
    simp only [hm]
  have h := (bits xs bit).trans (hm'.trans (bits ys bit).symm)
  cases (union xs).testBit bit <;> cases (union ys).testBit bit <;> simp_all

theorem perm (xs ys : List Nat) (h : xs.Perm ys) : union xs = union ys :=
  membership xs ys (fun x => h.mem_iff)

theorem dedup (xs : List Nat) : union xs.dedup = union xs :=
  membership _ _ (fun _ => List.mem_dedup)
#print axioms bits
#print axioms membership
#print axioms perm
#print axioms dedup
end R1Z.PV_Op134_Union
