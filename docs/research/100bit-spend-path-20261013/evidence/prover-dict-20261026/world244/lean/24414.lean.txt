import R1Z.PDict_TapeCore244
set_option autoImplicit false
namespace R1Z.PDict_TapeCore244

inductive Replay {A : Type} : Tape A → List A → Tape A → Prop
  | nil (t : Tape A) : Replay t [] t
  | cons {t next final : Tape A} {reply : A} {rest : List A}
      (head : read t = some (reply,next))
      (tail : Replay next rest final) : Replay t (reply::rest) final

theorem replay_inventory {A : Type} {t final : Tape A} {out : List A}
    (trace : Replay t out final) :
    final.replies = t.replies ∧ final.used = t.used+out.length := by
  induction trace with
  | nil t => exact ⟨rfl, rfl⟩
  | @cons t next final reply rest head tail ih =>
    obtain ⟨_,same,used⟩ := read_success t next reply head
    exact ⟨ih.1.trans same, by simp only [List.length_cons]; omega⟩

theorem replay_reads {A : Type} {t final : Tape A} {out : List A}
    (trace : Replay t out final) : reads out.length t = some (out, final) := by
  induction trace with
  | nil t => rfl
  | @cons t next final reply rest head tail ih =>
    simp [List.length_cons, reads, head, ih]

theorem reads_replay {A : Type} (n : Nat) (t final : Tape A) (out : List A)
    (run : reads n t = some (out,final)) : Replay t out final := by
  induction n generalizing t out final with
  | zero =>
    have eq : ([],t) = (out,final) := Option.some.inj run
    cases eq
    exact .nil t
  | succ n ih =>
    cases hr : read t with
    | none => simp [reads,hr] at run
    | some pair =>
      rcases pair with ⟨reply,next⟩
      cases hs : reads n next with
      | none => simp [reads,hr,hs] at run
      | some pair =>
        rcases pair with ⟨rest,last⟩
        have eq : reply::rest = out ∧ last = final := by
          simpa [reads,hr,hs] using run
        rw [←eq.1,←eq.2]
        exact .cons hr (ih next last rest hs)

theorem replay_append {A : Type} {t middle final : Tape A} {left right : List A}
    (first : Replay t left middle) (second : Replay middle right final) :
    Replay t (left++right) final := by
  induction first with
  | nil t => exact second
  | cons head tail ih => exact .cons head (ih second)

/-- A failed reply in the trace is data: append does not condition on success,
erase rejected prefixes, or reset the shared provider at the second call. -/
theorem reads_compose {A : Type} (m n : Nat) (t middle final : Tape A)
    (left right : List A)
    (first : reads m t = some (left,middle))
    (second : reads n middle = some (right,final)) :
    reads (m+n) t = some (left++right,final) := by
  have trace := replay_append (reads_replay m t middle left first)
    (reads_replay n middle final right second)
  have hl := (reads_inventory m t middle left first).2.2
  have hr := (reads_inventory n middle final right second).2.2
  have length : (left++right).length = m+n := by simp only [List.length_append,hl,hr]
  simpa only [length] using replay_reads trace

theorem replay_deterministic {A : Type} {t left right : Tape A} {out out' : List A}
    (first : Replay t out left) (second : Replay t out' right)
    (sameLength : out.length = out'.length) : out=out' ∧ left=right := by
  have h1 := replay_reads first
  have h2 := replay_reads second
  rw [sameLength] at h1
  exact Prod.mk.inj (Option.some.inj (h1.symm.trans h2))

#print axioms replay_inventory
#print axioms replay_reads
#print axioms reads_replay
#print axioms replay_append
#print axioms reads_compose
#print axioms replay_deterministic
end R1Z.PDict_TapeCore244
