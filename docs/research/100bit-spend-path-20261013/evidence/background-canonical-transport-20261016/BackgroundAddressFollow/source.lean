import BackgroundAddressMap
import PartialAddressTrace

/-! Shared-oracle follow under an injective partial address embedding.
Unrelated raw queries are skipped exactly; no finite-address or query-length
premise is imposed. -/
set_option autoImplicit false
namespace AspisR1.BackgroundAddressFollow
open R0C.V3 FS AspisV8PairedCommitment
open AspisV8R19.OracleResampling
open BackgroundAddressMap PartialAddressTrace

variable {I J A X C : Type} [DecidableEq I] [DecidableEq J] [Inhabited A]

theorem pushSpawns_idem (s : BS I A X) (p : List (I × Option A)) :
    pushSpawns (pushSpawns s p).1 (pushSpawns s p).2 = pushSpawns s p := by
  induction s generalizing p with
  | done x => rfl
  | ask i k ih => rfl
  | spawn i n ih => exact ih (p ++ [(i,none)])

theorem bfollow_push (g : X → List A → C) (tr : List (I × A))
    (s : BS I A X) (p : List (I × Option A)) (T : Table I A) :
    bfollow g tr (pushSpawns s p).1 (pushSpawns s p).2 T = bfollow g tr s p T := by
  cases tr <;> simp only [bfollow, pushSpawns_idem]

theorem bfollow_of_finished (g : X → List A → C) (tr : List (I × A))
    (s : BS I A X) (p : List (I × Option A)) (T : Table I A) (c : C)
    (h : finished g (pushSpawns s p).1 (pushSpawns s p).2 = some c) :
    bfollow g tr s p T = some c := by
  cases tr <;> simp only [bfollow, h]

theorem ownCell_embed_eq (e : Embedding I J) (s : BS J A X) (j : J) :
    ownCell (rename e.embed s) = some (e.embed j) ↔ ownCell s = some j := by
  cases s <;> simp [rename, ownCell, e.embed_injective.eq_iff]

theorem ownCell_embed_none (e : Embedding I J) (s : BS J A X) (i : I)
    (hi : e.decode i = none) : ownCell (rename e.embed s) ≠ some i := by
  cases s with
  | done x => simp [rename, ownCell]
  | spawn j n => simp [rename, ownCell]
  | ask j k =>
      intro h
      have he : e.embed j = i := Option.some.inj h
      have hd := (e.decode_iff i j).2 he
      rw [hi] at hd
      cases hd

theorem waits_embed_none (e : Embedding I J) (p : List (J × Option A)) (i : I)
    (hi : e.decode i = none) : waits i (pendMap e.embed p) = false := by
  induction p with
  | nil => rfl
  | cons q p ih =>
      rcases q with ⟨j,a⟩
      have hne : e.embed j ≠ i := by
        intro he
        have hd := (e.decode_iff i j).2 he
        rw [hi] at hd
        cases hd
      cases a <;> simp [waits, hne, ih]

theorem bfollow_project (e : Embedding I J) (g : X → List A → C)
    (tr : List (I × A)) (s : BS J A X) (p : List (J × Option A)) (T : Table I A) :
    bfollow g tr (rename e.embed s) (pendMap e.embed p) T =
      bfollow g (e.project tr) s p (e.pull T) := by
  induction tr generalizing s p T with
  | nil => simp only [bfollow, pushSpawns_rename, finished_rename, Embedding.project,
      List.filterMap_nil]
  | cons q rest ih =>
      rcases q with ⟨i,a⟩
      cases hd : e.decode i with
      | none =>
          rw [e.project_cons_none i a rest hd]
          have ho := ownCell_embed_none e (pushSpawns s p).1 i hd
          have hw := waits_embed_none e (pushSpawns s p).2 i hd
          rw [bfollow, pushSpawns_rename, finished_rename]
          cases hf : finished g (pushSpawns s p).1 (pushSpawns s p).2 with
          | some c => exact (bfollow_of_finished g (e.project rest) s p (e.pull T) c hf).symm
          | none =>
              simp only [ho, if_false, hw, Bool.false_eq_true]
              rw [ih, e.pull_put_none T i a hd, bfollow_push]
      | some j =>
          have he := (e.decode_iff i j).1 hd
          subst i
          rw [e.project_cons_some (e.embed j) a rest j (e.decode_embed j)]
          simp only [bfollow, pushSpawns_rename, finished_rename]
          cases hf : finished g (pushSpawns s p).1 (pushSpawns s p).2 with
          | some c => rfl
          | none =>
              simp only [ownCell_embed_eq, waits_pendMap e.embed e.embed_injective]
              have ht : T (e.embed j) = (e.pull T) j := rfl
              by_cases ho : ownCell (pushSpawns s p).1 = some j
              · by_cases hw : waits j (pushSpawns s p).2 = true
                · simp [ho, hw]
                · by_cases hn : (e.pull T) j = none
                  · simp only [ho, if_true, hw, if_false, ht, hn, stepAsk_rename]
                    rw [ih, e.pull_put_some T (e.embed j) a j (e.decode_embed j)]
                  · simp [ho, hw, ht, hn]
              · by_cases hw : waits j (pushSpawns s p).2 = true
                · by_cases hn : (e.pull T) j = none
                  · simp only [ho, if_false, hw, if_true, ht, hn,
                      record_pendMap e.embed e.embed_injective]
                    rw [ih, e.pull_put_some T (e.embed j) a j (e.decode_embed j)]
                  · simp [ho, hw, ht, hn]
                · simp only [ho, if_false, hw]
                  simp only [Bool.false_eq_true, if_false]
                  rw [ih, e.pull_put_some T (e.embed j) a j (e.decode_embed j)]

#print axioms bfollow_push
#print axioms bfollow_project
end AspisR1.BackgroundAddressFollow
