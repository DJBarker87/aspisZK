import BinMultiproof
import BinMerkleTable

/-! Pure insertion-sort/dedup model of multiproof.rs:255-288 and
candidate.rs:104-132. It rejects conflicting equal indices. Array extraction
and equality with the source's in-place insertion sort remain source work. -/
set_option autoImplicit false
namespace AspisR1.BinBatchDedup
open BinMerkle32Path
abbrev Entry := Nat × Digest

def insert (q : Entry) : List Entry → Option (List Entry)
  | [] => some [q]
  | r :: rs =>
      if q.1 < r.1 then some (q :: r :: rs)
      else if q.1 = r.1 then
        if q.2 = r.2 then some (r :: rs) else none
      else (insert q rs).map (r :: ·)

def run : List Entry → Option (List Entry)
  | [] => some []
  | q :: qs => (run qs).bind (insert q)

theorem insert_preserves (q : Entry) : ∀ (xs ys : List Entry),
    insert q xs = some ys → q ∈ ys ∧ xs ⊆ ys := by
  intro xs
  induction xs with
  | nil =>
      intro ys h
      have hy : ys = [q] := by simpa [insert] using h.symm
      subst ys
      simp
  | cons r rs ih =>
      intro ys h
      by_cases hlt : q.1 < r.1
      · have hy : ys = q :: r :: rs := by simpa [insert, hlt] using h.symm
        subst ys
        exact ⟨by simp, by intro x hx; exact List.mem_cons_of_mem _ hx⟩
      · by_cases he : q.1 = r.1
        · by_cases hv : q.2 = r.2
          · have hqr : q = r := Prod.ext he hv
            have hy : ys = r :: rs := by simpa [insert, hlt, he, hv] using h.symm
            subst ys
            exact ⟨by simp [hqr], by intro x hx; exact hx⟩
          · simp [insert, hlt, he, hv] at h
        · cases hr : insert q rs with
          | none => simp [insert, hlt, he, hr] at h
          | some tail =>
              have hy : ys = r :: tail := by simpa [insert, hlt, he, hr] using h.symm
              subst ys
              obtain ⟨hq, hs⟩ := ih tail hr
              refine ⟨List.mem_cons_of_mem r hq, ?_⟩
              intro x hx
              rcases List.mem_cons.mp hx with heq | hm
              · exact List.mem_cons.mpr (Or.inl heq)
              · exact List.mem_cons_of_mem r (hs hm)

theorem run_preserves : ∀ (batch canonical : List Entry),
    run batch = some canonical → batch ⊆ canonical := by
  intro batch
  induction batch with
  | nil => intro canonical _ x hx; simp at hx
  | cons q qs ih =>
      intro canonical h
      cases ht : run qs with
      | none => simp [run, ht] at h
      | some tail =>
          have hins : insert q tail = some canonical := by simpa [run, ht] using h
          obtain ⟨hq, hp⟩ := insert_preserves q tail canonical hins
          intro x hx
          rcases List.mem_cons.mp hx with heq | hm
          · exact heq.symm ▸ hq
          · exact hp (ih tail ht hm)

/-- Accepted canonical pairs represent a unique digest at each active index.
The preservation needed for all original queries is proved by `run_preserves`.
Conflicting original duplicates are therefore impossible on acceptance. -/
theorem dedup_sound {batch canonical : List Entry}
    {active : BinMultiproof.Active} {v : BinMultiproof.Values}
    (hrun : run batch = some canonical) (hrep : BinMultiproof.Dedup canonical active v) :
    BinMultiproof.Dedup batch active v := by
  intro q hq
  exact hrep q (run_preserves batch canonical hrun hq)

theorem accepted_original_queries {H : List Byte → Digest} {root : Digest}
    {depth : Nat} {active : BinMultiproof.Active} {v : BinMultiproof.Values}
    {nodes : List Digest} {trace : List (List Byte)} {batch canonical : List Entry}
    (hrun : run batch = some canonical) (hrep : BinMultiproof.Dedup canonical active v)
    (h : BinMultiproof.Accept H root depth active v nodes trace) :
    ∀ q ∈ batch, ∃ path : Path (BinMultiproof.slots depth q.1),
      foldPath H path q.2 = root ∧ inputTrace H path q.2 ⊆ trace :=
  BinMultiproof.batch_accepted_paths h (dedup_sound hrun hrep)

#print axioms insert_preserves
#print axioms run_preserves
#print axioms dedup_sound
#print axioms accepted_original_queries
end AspisR1.BinBatchDedup
