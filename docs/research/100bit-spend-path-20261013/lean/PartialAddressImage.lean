import PartialAddressTrace

/-! The inverse direction of a partial address embedding: a canonical
trace can be placed back in the legacy address carrier, with undefined
table entries everywhere outside the image. This is exact deterministic
bookkeeping, including the entire table before a retained frame. -/
set_option autoImplicit false
namespace AspisR1.PartialAddressTrace.Embedding

open FS FS2 FS2.Duplex AspisV8PairedCommitment

variable {I J A : Type} [DecidableEq I] [DecidableEq J]
variable (e : Embedding I J)

def imageTrace (tr : List (J × A)) : List (I × A) :=
  tr.map fun q => (e.embed q.1, q.2)

def push (T : Table J A) : Table I A := fun i => (e.decode i).bind T

theorem push_embed (T : Table J A) (j : J) : e.push T (e.embed j) = T j := by
  simp [push, e.decode_embed j]

theorem push_empty : e.push (emptyTable : Table J A) = emptyTable := by
  funext i
  cases h : e.decode i <;> simp [push, h, emptyTable]

theorem pull_push (T : Table J A) : e.pull (e.push T) = T := by
  funext j
  exact e.push_embed T j

theorem push_put (T : Table J A) (j : J) (v : A) :
    e.push (put T j v) = put (e.push T) (e.embed j) v := by
  funext i
  cases hd : e.decode i with
  | none =>
      have hne : i ≠ e.embed j := by
        intro he
        subst i
        rw [e.decode_embed j] at hd
        cases hd
      simp [push, hd, put, hne]
  | some k =>
      have he := (e.decode_iff i k).1 hd
      by_cases hkj : k = j
      · subst k
        rw [← he]
        simp [push, e.decode_embed j, put]
      · have hne : i ≠ e.embed j := by
          rw [← he]
          exact fun h => hkj (e.embed_injective h)
        simp [push, hd, put, hkj, hne]

theorem project_imageTrace (tr : List (J × A)) :
    e.project (e.imageTrace tr) = tr := by
  induction tr with
  | nil => rfl
  | cons q rest ih =>
      obtain ⟨j,v⟩ := q
      change e.project ((e.embed j,v)::e.imageTrace rest) = (j,v)::rest
      rw [e.project_cons_some _ _ _ j (e.decode_embed j), ih]

theorem tableBefore_imageTrace (T : Table J A) (tr : List (J × A)) (j : J) :
    tableBefore (e.push T) (e.imageTrace tr) (e.embed j) =
      e.push (tableBefore T tr j) := by
  induction tr generalizing T with
  | nil => rfl
  | cons q rest ih =>
      obtain ⟨k,v⟩ := q
      change tableBefore (e.push T) ((e.embed k,v)::e.imageTrace rest) (e.embed j) =
        e.push (tableBefore T ((k,v)::rest) j)
      by_cases hkj : k = j
      · subst k
        simp [tableBefore]
      · have hne : e.embed k ≠ e.embed j := fun h => hkj (e.embed_injective h)
        simp only [tableBefore, if_neg hne, if_neg hkj]
        rw [← e.push_put T k v, ih (put T k v)]

theorem traceFrom_imageTrace (tr : List (J × A)) (j : J) :
    traceFrom (e.imageTrace tr) (e.embed j) = e.imageTrace (traceFrom tr j) := by
  induction tr with
  | nil => rfl
  | cons q rest ih =>
      obtain ⟨k,v⟩ := q
      by_cases hkj : k = j
      · subst k
        simp [imageTrace, traceFrom]
      · have hne : e.embed k ≠ e.embed j := fun h => hkj (e.embed_injective h)
        simpa only [imageTrace, List.map_cons, traceFrom, if_neg hne, if_neg hkj] using ih

theorem firstReads_imageTrace (T : Table J A) (tr : List (J × A)) :
    firstReads (e.push T) (e.imageTrace tr) = firstReads T tr := by
  induction tr generalizing T with
  | nil => rfl
  | cons q rest ih =>
      obtain ⟨j,v⟩ := q
      change firstReads (e.push T) ((e.embed j,v)::e.imageTrace rest) =
        firstReads T ((j,v)::rest)
      simp only [firstReads, e.push_embed T j]
      rw [← e.push_put T j v, ih (put T j v)]

theorem mem_imageTrace (tr : List (J × A)) (i : I) (v : A) :
    (i,v) ∈ e.imageTrace tr ↔ ∃ j, e.embed j = i ∧ (j,v) ∈ tr := by
  simp only [imageTrace, List.mem_map]
  constructor
  · rintro ⟨⟨j,a⟩, hmem, he⟩
    simp only [Prod.mk.injEq] at he
    rcases he with ⟨he, rfl⟩
    exact ⟨j, he, hmem⟩
  · rintro ⟨j, he, hmem⟩
    exact ⟨(j,v), hmem, by simp [he]⟩

#print axioms project_imageTrace
#print axioms tableBefore_imageTrace
#print axioms traceFrom_imageTrace
#print axioms firstReads_imageTrace
#print axioms mem_imageTrace
end AspisR1.PartialAddressTrace.Embedding
