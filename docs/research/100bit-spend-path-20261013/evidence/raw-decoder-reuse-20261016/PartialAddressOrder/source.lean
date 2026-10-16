import PartialAddressTrace

/-! A partial injective restriction preserves the first-read order among
retained addresses. Unrelated oracle calls may be removed without changing
which retained answers are available before a retained challenge frame. -/
set_option autoImplicit false
namespace AspisR1.PartialAddressOrder

open FS FS2 FS2.Duplex AspisV8PairedCommitment
open PartialAddressTrace

variable {I J A : Type} [DecidableEq I] [DecidableEq J]

theorem read_project_iff (e : Embedding I J) (tr : List (I × A)) (j : J) :
    Read (e.project tr) j ↔ Read tr (e.embed j) := by
  simp only [Read, List.mem_map]
  constructor
  · rintro ⟨⟨k,v⟩, hmem, he⟩
    simp only [Prod.fst] at he
    subst k
    exact ⟨(e.embed j,v), (e.mem_project tr j v).1 hmem, rfl⟩
  · rintro ⟨⟨i,v⟩, hmem, he⟩
    simp only [Prod.fst] at he
    subst i
    exact ⟨(j,v), (e.mem_project tr j v).2 hmem, rfl⟩

theorem before_project_iff (e : Embedding I J) (H : I → A)
    (tr : List (I × A)) (hcons : ∀ q ∈ tr, q.2 = H q.1) (a b : J) :
    Before (e.project tr) a b ↔ Before tr (e.embed a) (e.embed b) := by
  have hpcons := e.project_consistent H tr hcons
  have htable := congrFun (e.tableBefore_project (emptyTable : Table I A) tr b) a
  change tableBefore emptyTable (e.project tr) b a =
    tableBefore emptyTable tr (e.embed b) (e.embed a) at htable
  rw [tableBefore_eq (fun j => H (e.embed j)) (e.project tr) emptyTable b a hpcons,
    tableBefore_eq H tr emptyTable (e.embed b) (e.embed a) hcons] at htable
  by_cases hleft : Before (e.project tr) a b <;>
    by_cases hright : Before tr (e.embed a) (e.embed b) <;>
    simp_all [emptyTable]

/-- Any bad event whose interpretation is preserved by table pullback can
only occur in the projected trace if its raw counterpart occurs. This
structural lemma makes no finite-address or probability-law assumption. -/
theorem hitsBad_project (e : Embedding I J)
    (badI : I → Table I A → A → Prop)
    (badJ : J → Table J A → A → Prop)
    (hbad : ∀ j t v, badJ j (e.pull t) v → badI (e.embed j) t v)
    (t : Table I A) (tr : List (I × A)) :
    hitsBad badJ (e.pull t) (e.project tr) → hitsBad badI t tr := by
  induction tr generalizing t with
  | nil => simp [PartialAddressTrace.Embedding.project, hitsBad]
  | cons q rest ih =>
      obtain ⟨i,v⟩ := q
      cases hd : e.decode i with
      | none =>
          rw [e.project_cons_none i v rest hd]
          intro h
          have hp := e.pull_put_none t i v hd
          rw [← hp] at h
          exact Or.inr (ih (put t i v) h)
      | some j =>
          rw [e.project_cons_some i v rest j hd]
          simp only [hitsBad]
          rintro (⟨hmiss,hb⟩ | hrest)
          · left
            have he := (e.decode_iff i j).1 hd
            exact ⟨by simpa [PartialAddressTrace.Embedding.pull, he] using hmiss,
              by simpa [he] using hbad j t v hb⟩
          · right
            rw [← e.pull_put_some t i v j hd] at hrest
            exact ih (put t i v) hrest

#print axioms read_project_iff
#print axioms before_project_iff
#print axioms hitsBad_project
end AspisR1.PartialAddressOrder
