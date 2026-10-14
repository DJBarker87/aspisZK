import R1ParsedTargetsFirstHit

/-! Prefix separation for first reads, followed by the finite-family hit adapter. -/
set_option autoImplicit false
namespace AspisR1.ParsedTargetsPrefixHit

open FS FS2 FS2.Duplex
open AspisV8R19.SourceDuplexStep

variable {M Cv : Type} {L : Nat}

theorem firstIdx_append_of_read (b : Addr L) (pre post : List (Addr L × State))
    (hb : Read pre b) :
    firstIdx b (pre ++ post) = firstIdx b pre := by
  induction pre with
  | nil => simp [Read] at hb
  | cons q rest ih =>
      obtain ⟨i, v⟩ := q
      simp only [Read, List.map_cons, List.mem_cons] at hb
      by_cases h : i = b
      · simp [firstIdx, h]
      · have hr : Read rest b := hb.resolve_left (Ne.symm h)
        simp [firstIdx, h, ih hr]

theorem firstIdx_append_of_not_read (a : Addr L) (pre post : List (Addr L × State))
    (hna : ¬ Read pre a) :
    firstIdx a (pre ++ post) = pre.length + firstIdx a post := by
  induction pre with
  | nil => simp
  | cons q rest ih =>
      obtain ⟨i, v⟩ := q
      have hne : i ≠ a := by
        intro h
        apply hna
        simp [Read, h]
      have hr : ¬ Read rest a := by
        intro h
        apply hna
        simp [Read, h]
      simp [firstIdx, hne, ih hr]

theorem before_of_prefix (a b : Addr L) (pre post : List (Addr L × State))
    (hb : Read pre b) (hna : ¬ Read pre a) :
    Before (pre ++ post) b a := by
  refine ⟨?_, ?_⟩
  · exact (firstIdx_append_of_read b pre post hb ▸ hb)
  · rw [firstIdx_append_of_read b pre post hb,
      firstIdx_append_of_not_read a pre post hna]
    have hlt := firstIdx_lt_length b pre hb
    omega

theorem prefix_hit {B : Nat}
    (pred : Fin B → Addr L → Option State) (Qtot : Nat)
    (H : Addr L → State) (pre post : List (Addr L × State))
    (hcons : ∀ q ∈ pre ++ post, q.2 = H q.1)
    (hQ : firstReads emptyTable (pre ++ post) ≤ Qtot)
    (a b : Addr L) (ha : Read post a) (hna : ¬ Read pre a)
    (hb : Read pre b) (j : Fin B) (hp : pred j b = some (H a)) :
    hitsBad (ParsedTargetsCollision.bad pred Qtot) emptyTable (pre ++ post) := by
  apply ParsedTargetsFirstHit.first_hit pred Qtot H (pre ++ post) hcons hQ a b
  · exact List.mem_append.mpr (Or.inr ha)
  · exact before_of_prefix a b pre post hb hna
  · exact hb
  · exact j
  · exact hp

#print axioms firstIdx_append_of_read
#print axioms firstIdx_append_of_not_read
#print axioms before_of_prefix
#print axioms prefix_hit

end AspisR1.ParsedTargetsPrefixHit
