import FS2.DuplexTrace
import R1TraceTable

/-! Deterministic restriction of a raw oracle trace to a partial address
embedding. Addresses outside the image are discarded, never aliased. The
raw trace and adversary remain unrestricted; no probability law is transported.
These facts permit reuse of bounded canonical decoder bookkeeping. -/
set_option autoImplicit false
namespace AspisR1.PartialAddressTrace

open FS FS2 FS2.Duplex AspisV8PairedCommitment

variable {I J A : Type} [DecidableEq I] [DecidableEq J]

structure Embedding (I J : Type) where
  embed : J → I
  decode : I → Option J
  decode_iff : ∀ i j, decode i = some j ↔ embed j = i

namespace Embedding

variable (e : Embedding I J)

theorem decode_embed (j : J) : e.decode (e.embed j) = some j :=
  (e.decode_iff _ _).2 rfl

theorem embed_injective : Function.Injective e.embed := by
  intro a b h
  have ha := e.decode_embed a
  rw [h, e.decode_embed b] at ha
  exact (Option.some.inj ha).symm

def project (tr : List (I × A)) : List (J × A) :=
  tr.filterMap fun q => (e.decode q.1).map fun j => (j, q.2)

def pull (t : Table I A) : Table J A := fun j => t (e.embed j)

theorem pull_put_some (t : Table I A) (i : I) (v : A) (j : J)
    (h : e.decode i = some j) :
    e.pull (put t i v) = put (e.pull t) j v := by
  have he := (e.decode_iff i j).1 h
  subst i
  funext k
  simp only [pull, put]
  by_cases hkj : k = j
  · subst k
    simp
  · have hne : e.embed k ≠ e.embed j := fun h => hkj (e.embed_injective h)
    simp [hkj, hne]

theorem pull_put_none (t : Table I A) (i : I) (v : A)
    (h : e.decode i = none) : e.pull (put t i v) = e.pull t := by
  funext k
  have hne : e.embed k ≠ i := by
    intro he
    have hd := (e.decode_iff i k).2 he
    rw [h] at hd
    cases hd
  simp [pull, put, hne]

theorem project_cons_none (i : I) (v : A) (tr : List (I × A))
    (h : e.decode i = none) : e.project ((i,v)::tr) = e.project tr := by
  simp [project, h]

theorem project_cons_some (i : I) (v : A) (tr : List (I × A)) (j : J)
    (h : e.decode i = some j) :
    e.project ((i,v)::tr) = (j,v)::e.project tr := by
  simp [project, h]

theorem tableBefore_project (t : Table I A) (tr : List (I × A)) (j : J) :
    tableBefore (e.pull t) (e.project tr) j =
      e.pull (tableBefore t tr (e.embed j)) := by
  induction tr generalizing t with
  | nil => rfl
  | cons q rest ih =>
      obtain ⟨i,v⟩ := q
      cases hd : e.decode i with
      | none =>
          have hne : i ≠ e.embed j := by
            intro he
            subst i
            rw [e.decode_embed j] at hd
            cases hd
          rw [e.project_cons_none i v rest hd]
          simp only [tableBefore, if_neg hne]
          rw [← ih (put t i v), e.pull_put_none t i v hd]
      | some k =>
          have he := (e.decode_iff i k).1 hd
          rw [e.project_cons_some i v rest k hd]
          by_cases hkj : k = j
          · subst k
            rw [← he]
            simp [tableBefore]
          · have hne : i ≠ e.embed j := by
              rw [← he]
              exact fun h => hkj (e.embed_injective h)
            simp only [tableBefore, if_neg hkj, if_neg hne]
            rw [← ih (put t i v), e.pull_put_some t i v k hd]

theorem traceFrom_project (tr : List (I × A)) (j : J) :
    e.project (traceFrom tr (e.embed j)) = traceFrom (e.project tr) j := by
  induction tr with
  | nil => rfl
  | cons q rest ih =>
      obtain ⟨i,v⟩ := q
      cases hd : e.decode i with
      | none =>
          have hne : i ≠ e.embed j := by
            intro he
            subst i
            rw [e.decode_embed j] at hd
            cases hd
          rw [e.project_cons_none i v rest hd]
          simpa only [traceFrom, if_neg hne] using ih
      | some k =>
          have he := (e.decode_iff i k).1 hd
          rw [e.project_cons_some i v rest k hd]
          by_cases hkj : k = j
          · subst k
            rw [← he]
            simp only [traceFrom, if_pos rfl]
            exact e.project_cons_some _ v rest j (e.decode_embed j)
          · have hne : i ≠ e.embed j := by
              rw [← he]
              exact fun h => hkj (e.embed_injective h)
            simpa only [traceFrom, if_neg hne, if_neg hkj] using ih

theorem firstReads_project_le (t : Table I A) (tr : List (I × A)) :
    firstReads (e.pull t) (e.project tr) ≤ firstReads t tr := by
  induction tr generalizing t with
  | nil => rfl
  | cons q rest ih =>
      obtain ⟨i,v⟩ := q
      have hrest := ih (put t i v)
      cases hd : e.decode i with
      | none =>
          rw [e.project_cons_none i v rest hd]
          rw [e.pull_put_none t i v hd] at hrest
          simp only [firstReads]
          omega
      | some k =>
          have he := (e.decode_iff i k).1 hd
          rw [e.project_cons_some i v rest k hd]
          rw [e.pull_put_some t i v k hd] at hrest
          simp only [firstReads, pull, he]
          exact Nat.add_le_add_left hrest _

theorem replay_project (t : Table I A) (tr : List (I × A)) :
    TraceTable.replay (e.pull t) (e.project tr) = e.pull (TraceTable.replay t tr) := by
  induction tr generalizing t with
  | nil => rfl
  | cons q rest ih =>
      obtain ⟨i,v⟩ := q
      cases hd : e.decode i with
      | none =>
          rw [e.project_cons_none i v rest hd]
          change _ = e.pull (TraceTable.replay (put t i v) rest)
          rw [← ih (put t i v), e.pull_put_none t i v hd]
      | some k =>
          rw [e.project_cons_some i v rest k hd]
          change TraceTable.replay (put (e.pull t) k v) (e.project rest) =
            e.pull (TraceTable.replay (put t i v) rest)
          rw [← ih (put t i v), e.pull_put_some t i v k hd]

theorem mem_project (tr : List (I × A)) (j : J) (v : A) :
    (j,v) ∈ e.project tr ↔ (e.embed j,v) ∈ tr := by
  simp only [project, List.mem_filterMap]
  constructor
  · rintro ⟨⟨i,a⟩, hmem, hout⟩
    cases hd : e.decode i with
    | none => simp [hd] at hout
    | some k =>
        simp only [hd, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hout
        rcases hout with ⟨rfl, rfl⟩
        rwa [(e.decode_iff i k).1 hd] 
  · intro hmem
    exact ⟨(e.embed j,v), hmem, by simp [e.decode_embed j]⟩

theorem project_consistent (H : I → A) (tr : List (I × A))
    (hcons : ∀ q ∈ tr, q.2 = H q.1) :
    ∀ q ∈ e.project tr, q.2 = H (e.embed q.1) := by
  intro q hq
  exact hcons (e.embed q.1, q.2) ((e.mem_project tr q.1 q.2).1 hq)

#print axioms tableBefore_project
#print axioms traceFrom_project
#print axioms firstReads_project_le
#print axioms replay_project
#print axioms mem_project
#print axioms project_consistent
end Embedding
end AspisR1.PartialAddressTrace
