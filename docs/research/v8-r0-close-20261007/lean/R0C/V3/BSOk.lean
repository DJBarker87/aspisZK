import R0C.V3.BS
import FS2.DuplexTrace

/-! # Following a background-read sampler to completion, and splitting its law

`bfollow_ok`: on a consistent trace, a sampler whose waiting background cells
and run cells are distinct, fresh, read, and ordered (every later run cell is
first-read after each earlier *ask*) is followed to its run output on the
oracle's values.  `blaw_split`: the initial background cells' law factors out
of the sampler's own law. -/
set_option autoImplicit false
namespace R0C.V3

open FS2.Duplex (Read Before firstIdx)
open AspisV8PairedCommitment AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleResampling
open FS (mean_mono)

section Run
variable {I A X C : Type} [DecidableEq I] [Inhabited A]

def runOut (H : I → A) : BS I A X → X × List I
  | .done x => (x, [])
  | .ask i k => runOut H (k (H i))
  | .spawn c n => ((runOut H n).1, c :: (runOut H n).2)

def evs (H : I → A) : BS I A X → List (Bool × I)
  | .done _ => []
  | .ask i k => (true, i) :: evs H (k (H i))
  | .spawn c n => (false, c) :: evs H n

def fill (H : I → A) (pend : List (I × Option A)) : List A := pend.map fun p => p.2.getD (H p.1)

def waiting : List (I × Option A) → List I
  | [] => []
  | (c, none) :: rest => c :: waiting rest
  | (_, some _) :: rest => waiting rest

def OrderOK (tr : List (I × A)) : List (Bool × I) → Prop
  | [] => True
  | (b, c) :: rest => (b = true → ∀ e ∈ rest, Before tr c e.2) ∧ OrderOK tr rest

omit [Inhabited A] in
theorem waits_iff (l : I) : ∀ pend : List (I × Option A), waits l pend = true ↔ l ∈ waiting pend := by
  intro pend
  induction pend with
  | nil => simp [waits, waiting]
  | cons p rest ih =>
      obtain ⟨c, o⟩ := p
      cases o with
      | none =>
          simp only [waits, waiting, Bool.or_eq_true, decide_eq_true_eq, List.mem_cons, ih]
          exact or_congr eq_comm Iff.rfl
      | some b => simp only [waits, waiting, ih]

omit [DecidableEq I] [Inhabited A] in
theorem allDone_iff : ∀ pend : List (I × Option A), allDone pend = true ↔ waiting pend = [] := by
  intro pend
  induction pend with
  | nil => simp [allDone, waiting]
  | cons p rest ih =>
      obtain ⟨c, o⟩ := p
      cases o with
      | none => simp [allDone, waiting]
      | some b => simp only [allDone, waiting, ih]

omit [DecidableEq I] [Inhabited A] in
theorem waiting_append : ∀ (pend post : List (I × Option A)),
    waiting (pend ++ post) = waiting pend ++ waiting post := by
  intro pend
  induction pend with
  | nil => intro post; rfl
  | cons p rest ih =>
      intro post
      obtain ⟨c, o⟩ := p
      cases o <;> simp [waiting, ih]

omit [DecidableEq I] [Inhabited A] in
theorem fill_append (H : I → A) (pend post : List (I × Option A)) :
    fill H (pend ++ post) = fill H pend ++ fill H post := by
  simp [fill]

omit [Inhabited A] in
theorem waiting_record (l : I) (a : A) : ∀ pend : List (I × Option A), l ∈ waiting pend →
    waiting (record l a pend) = (waiting pend).erase l := by
  intro pend
  induction pend with
  | nil => intro h; simp [waiting] at h
  | cons p rest ih =>
      intro h
      obtain ⟨c, o⟩ := p
      cases o with
      | some b =>
          simp only [waiting] at h
          simp only [record, waiting, ih h]
      | none =>
          by_cases hc : c = l
          · subst hc
            simp [record, waiting]
          · have h' : l ∈ waiting rest := by
              simp only [waiting, List.mem_cons] at h
              exact h.resolve_left (Ne.symm hc)
            simp only [record, if_neg hc, waiting, ih h']
            rw [List.erase_cons_tail (by simpa using hc)]

omit [Inhabited A] in
theorem fill_record (H : I → A) (l : I) : ∀ pend : List (I × Option A),
    fill H (record l (H l) pend) = fill H pend := by
  intro pend
  induction pend with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨c, o⟩ := p
      cases o with
      | some b => simp only [record, fill, List.map_cons] at ih ⊢; rw [ih]
      | none =>
          by_cases hc : c = l
          · subst hc; simp [record, fill]
          · simp only [record, if_neg hc, fill, List.map_cons] at ih ⊢; rw [ih]

omit [DecidableEq I] in
theorem answers_eq_fill (H : I → A) : ∀ pend : List (I × Option A), allDone pend = true →
    answers pend = fill H pend := by
  intro pend
  induction pend with
  | nil => intro _; rfl
  | cons p rest ih =>
      intro h
      obtain ⟨c, o⟩ := p
      cases o with
      | none => simp [allDone] at h
      | some b =>
          simp only [allDone] at h
          simp only [answers, fill, List.map_cons, Option.getD_some] at ih ⊢
          rw [ih h]

omit [Inhabited A] in
theorem push_facts (H : I → A) : ∀ (own : BS I A X) (pend : List (I × Option A)),
    (runOut H (pushSpawns own pend).1).1 = (runOut H own).1 ∧
    fill H (pushSpawns own pend).2 ++ (runOut H (pushSpawns own pend).1).2.map H =
      fill H pend ++ (runOut H own).2.map H ∧
    waiting (pushSpawns own pend).2 ++ (evs H (pushSpawns own pend).1).map Prod.snd =
      waiting pend ++ (evs H own).map Prod.snd ∧
    (∀ tr : List (I × A), OrderOK tr (evs H own) → OrderOK tr (evs H (pushSpawns own pend).1)) ∧
    (∀ c n, (pushSpawns own pend).1 ≠ .spawn c n) := by
  intro own
  induction own with
  | done x => intro pend; exact ⟨rfl, rfl, rfl, fun _ h => h, fun _ _ h => by cases h⟩
  | ask i k _ => intro pend; exact ⟨rfl, rfl, rfl, fun _ h => h, fun _ _ h => by cases h⟩
  | spawn c n ih =>
      intro pend
      obtain ⟨h1, h2, h3, h4, h5⟩ := ih (pend ++ [(c, none)])
      refine ⟨h1, ?_, ?_, ?_, h5⟩
      · simp only [pushSpawns] at h2 ⊢
        rw [h2, fill_append]
        simp [runOut, fill]
      · simp only [pushSpawns] at h3 ⊢
        rw [h3, waiting_append]
        simp [waiting, evs]
      · intro tr ho
        simp only [pushSpawns]
        exact h4 tr ho.2

end Run

section Trace
variable {I A : Type} [DecidableEq I]

omit [DecidableEq I] in
theorem read_tail (l : I) (a : A) (rest : List (I × A)) (c : I)
    (h : Read ((l, a) :: rest) c) (hc : c ≠ l) : Read rest c := by
  have h' : c ∈ l :: rest.map Prod.fst := h
  rcases List.mem_cons.mp h' with e | e
  · exact absurd e hc
  · exact e

theorem firstIdx_head (l : I) (a : A) (rest : List (I × A)) : firstIdx l ((l, a) :: rest) = 0 := by
  simp [firstIdx]

theorem firstIdx_tail (l : I) (a : A) (rest : List (I × A)) (c : I) (hc : c ≠ l) :
    firstIdx c ((l, a) :: rest) = firstIdx c rest + 1 := by
  simp [firstIdx, Ne.symm hc]

theorem not_before_head (l : I) (a : A) (rest : List (I × A)) (c : I) :
    ¬ Before ((l, a) :: rest) c l := by
  rintro ⟨_, h⟩
  rw [firstIdx_head] at h
  omega

theorem before_tail (l : I) (a : A) (rest : List (I × A)) (c e : I)
    (h : Before ((l, a) :: rest) c e) (hc : c ≠ l) : Before rest c e := by
  have he : e ≠ l := by
    intro hel
    rw [hel] at h
    exact not_before_head l a rest c h
  refine ⟨read_tail l a rest c h.1 hc, ?_⟩
  have := h.2
  rw [firstIdx_tail l a rest c hc, firstIdx_tail l a rest e he] at this
  omega

theorem order_tail (l : I) (a : A) (rest : List (I × A)) :
    ∀ ev : List (Bool × I), (∀ e ∈ ev, e.2 ≠ l) →
      OrderOK ((l, a) :: rest) ev → OrderOK rest ev := by
  intro ev
  induction ev with
  | nil => intro _ _; trivial
  | cons e evs ih =>
      intro hne ho
      obtain ⟨b, c⟩ := e
      refine ⟨fun hb e he => before_tail l a rest c e.2 (ho.1 hb e he)
        (hne (b, c) (List.mem_cons_self ..)), ih (fun e he => hne e (List.mem_cons_of_mem _ he)) ho.2⟩

end Trace

section Ok
variable {I A X C : Type} [DecidableEq I] [Inhabited A]

omit [DecidableEq I] [Inhabited A] in
theorem bs_shape (b : BS I A X) (h : ∀ c n, b ≠ .spawn c n) :
    (∃ x, b = .done x) ∨ ∃ i k, b = .ask i k := by
  cases b with
  | done x => exact Or.inl ⟨x, rfl⟩
  | ask i k => exact Or.inr ⟨i, k, rfl⟩
  | spawn c n => exact absurd rfl (h c n)

theorem bfollow_ok (H : I → A) (g : X → List A → C) :
    ∀ (tr : List (I × A)) (own : BS I A X) (pend : List (I × Option A)) (t : Table I A),
      (∀ q ∈ tr, q.2 = H q.1) →
      (waiting pend ++ (evs H own).map Prod.snd).Nodup →
      (∀ c ∈ waiting pend ++ (evs H own).map Prod.snd, t c = none ∧ Read tr c) →
      OrderOK tr (evs H own) →
      bfollow g tr own pend t = some (g (runOut H own).1 (fill H pend ++ (runOut H own).2.map H)) := by
  intro tr
  induction tr with
  | nil =>
      intro own pend t _ hnd hc ho
      obtain ⟨h1, h2, h3, _, h5⟩ := push_facts H own pend
      simp only [bfollow]
      rw [← h1, ← h2]
      set own' := (pushSpawns own pend).1
      set pend' := (pushSpawns own pend).2
      have hnil : waiting pend' ++ (evs H own').map Prod.snd = [] := by
        rw [h3]
        cases hl : waiting pend ++ (evs H own).map Prod.snd with
        | nil => rfl
        | cons c cs =>
            have := (hc c (by rw [hl]; exact List.mem_cons_self ..)).2
            simp [Read] at this
      rw [List.append_eq_nil_iff] at hnil
      obtain ⟨hw, he⟩ := hnil
      cases ho' : own' with
      | done x =>
          have hd : allDone pend' = true := (allDone_iff pend').mpr hw
          simp only [finished, hd, if_true, runOut, List.map_nil, List.append_nil]
          rw [answers_eq_fill H pend' hd]
      | ask i k =>
          rw [ho'] at he
          simp [evs] at he
      | spawn c n => exact absurd ho' (h5 c n)
  | cons q rest ih =>
      intro own pend t hcons hnd hc ho
      obtain ⟨l, a⟩ := q
      have ha : a = H l := hcons (l, a) (List.mem_cons_self ..)
      have hrest : ∀ q ∈ rest, q.2 = H q.1 := fun q hq => hcons q (List.mem_cons_of_mem _ hq)
      have tr1 : ∀ c, (t c = none ∧ Read ((l, a) :: rest) c) → c ≠ l →
          put t l a c = none ∧ Read rest c := fun c h hcl =>
        ⟨by simp [put, hcl, h.1], read_tail l a rest c h.2 hcl⟩
      obtain ⟨h1, h2, h3, h4, h5⟩ := push_facts H own pend
      rw [← h1, ← h2]
      have hunf : bfollow g ((l, a) :: rest) own pend t =
          match finished g (pushSpawns own pend).1 (pushSpawns own pend).2 with
          | some c => some c
          | none =>
            if ownCell (pushSpawns own pend).1 = some l then
              (if waits l (pushSpawns own pend).2 then none
               else if t l = none then
                 bfollow g rest (stepAsk (pushSpawns own pend).1 a) (pushSpawns own pend).2 (put t l a)
               else none)
            else if waits l (pushSpawns own pend).2 then
              (if t l = none then
                 bfollow g rest (pushSpawns own pend).1 (record l a (pushSpawns own pend).2) (put t l a)
               else none)
            else bfollow g rest (pushSpawns own pend).1 (pushSpawns own pend).2 (put t l a) := rfl
      rw [hunf]
      rw [← h3] at hnd hc
      have ho' := h4 _ ho
      generalize (pushSpawns own pend).2 = pend' at hnd hc ⊢
      rcases bs_shape (pushSpawns own pend).1 h5 with ⟨x, hcase⟩ | ⟨i, k, hcase⟩
      · rw [hcase] at hnd hc ho' ⊢
        simp only [evs, List.map_nil, List.append_nil] at hnd hc
        by_cases hd : allDone pend' = true
        · simp only [finished, hd, if_true, runOut, List.map_nil, List.append_nil]
          rw [answers_eq_fill H pend' hd]
        · have hfin : finished g (BS.done x : BS I A X) pend' = none := by
            simp [finished, hd]
          rw [hfin]
          simp only [ownCell, reduceCtorEq, if_false]
          by_cases hw : l ∈ waiting pend'
          · have hwb : waits l pend' = true := (waits_iff l pend').mpr hw
            rw [if_pos hwb, if_pos (hc l hw).1]
            have hk := ih (BS.done x) (record l a pend') (put t l a) hrest ?_ ?_ trivial
            · rw [hk, ha, fill_record]
            · simp only [evs, List.map_nil, List.append_nil]
              rw [waiting_record l a pend' hw]
              exact hnd.erase l
            · simp only [evs, List.map_nil, List.append_nil]
              rw [waiting_record l a pend' hw]
              intro c hcm
              have hcl : c ≠ l := fun e => ((hnd.mem_erase_iff).mp (e ▸ hcm)).1 rfl
              exact tr1 c (hc c (List.mem_of_mem_erase hcm)) hcl
          · have hwb : ¬ waits l pend' = true := fun h => hw ((waits_iff l pend').mp h)
            rw [if_neg hwb]
            have hk := ih (BS.done x) pend' (put t l a) hrest (by simpa [evs] using hnd) ?_ trivial
            · exact hk
            · simp only [evs, List.map_nil, List.append_nil]
              intro c hcm
              exact tr1 c (hc c hcm) (fun e => hw (e ▸ hcm))
      · rw [hcase] at hnd hc ho' ⊢
        have hfin : finished g (BS.ask i k : BS I A X) pend' = none := rfl
        rw [hfin]
        simp only [ownCell]
        simp only [evs, List.map_cons] at hnd hc ho'
        rw [List.nodup_append, List.nodup_cons] at hnd
        obtain ⟨hndw, ⟨hni, hnde⟩, hdisj⟩ := hnd
        have hc' : ∀ c, c ∈ waiting pend' ∨ c = i ∨ c ∈ (evs H (k (H i))).map Prod.snd →
            t c = none ∧ Read ((l, a) :: rest) c := by
          intro c hcm
          apply hc c
          rcases hcm with hcm | hcm | hcm
          · exact List.mem_append_left _ hcm
          · exact List.mem_append_right _ (hcm ▸ List.mem_cons_self ..)
          · exact List.mem_append_right _ (List.mem_cons_of_mem _ hcm)
        have hiw : i ∉ waiting pend' := fun h => hdisj i h i (List.mem_cons_self ..) rfl
        by_cases hil : i = l
        · subst hil
          rw [if_pos rfl]
          have hnw : ¬ waits i pend' = true := fun h => hiw ((waits_iff i pend').mp h)
          rw [if_neg hnw, if_pos (hc' i (Or.inr (Or.inl rfl))).1]
          simp only [stepAsk]
          rw [← ha] at hnde hdisj hc' ho' hni
          have hk := ih (k a) pend' (put t i a) hrest ?_ ?_ ?_
          · rw [hk]
            simp only [runOut, ← ha]
          · rw [List.nodup_append]
            exact ⟨hndw, hnde, fun c h1 d h2 => hdisj c h1 d (List.mem_cons_of_mem _ h2)⟩
          · intro c hcm
            rcases List.mem_append.mp hcm with hcm | hcm
            · exact tr1 c (hc' c (Or.inl hcm)) (fun e => hiw (e ▸ hcm))
            · exact tr1 c (hc' c (Or.inr (Or.inr hcm))) (fun e => hni (e ▸ hcm))
          · apply order_tail i a rest _ ?_ ho'.2
            intro e he hei
            exact hni (hei ▸ List.mem_map_of_mem he)
        · rw [if_neg (fun h => hil (Option.some.inj h))]
          have hlev : l ∉ i :: (evs H (k (H i))).map Prod.snd := by
            intro hm
            rcases List.mem_cons.mp hm with hm | hm
            · exact hil hm.symm
            · obtain ⟨e, he, hel⟩ := List.mem_map.mp hm
              have hB := ho'.1 rfl e he
              rw [hel] at hB
              exact not_before_head l a rest i hB
          have hord : OrderOK rest (evs H (BS.ask i k)) := by
            apply order_tail l a rest _ ?_ ho'
            intro e he hel
            simp only [evs, List.mem_cons] at he
            rcases he with he | he
            · exact hlev (by rw [← hel, he]; exact List.mem_cons_self ..)
            · exact hlev (List.mem_cons_of_mem _ (hel ▸ List.mem_map_of_mem he))
          by_cases hw : l ∈ waiting pend'
          · have hwb : waits l pend' = true := (waits_iff l pend').mpr hw
            rw [if_pos hwb, if_pos (hc' l (Or.inl hw)).1]
            have hk := ih (BS.ask i k) (record l a pend') (put t l a) hrest ?_ ?_ hord
            · rw [hk, ha, fill_record]
            · rw [waiting_record l a pend' hw]
              simp only [evs, List.map_cons]
              rw [List.nodup_append, List.nodup_cons]
              exact ⟨hndw.erase l, ⟨hni, hnde⟩,
                fun c h1 d h2 => hdisj c (List.mem_of_mem_erase h1) d h2⟩
            · rw [waiting_record l a pend' hw]
              simp only [evs, List.map_cons]
              intro c hcm
              rcases List.mem_append.mp hcm with hcm | hcm
              · exact tr1 c (hc' c (Or.inl (List.mem_of_mem_erase hcm)))
                  (fun e => ((hndw.mem_erase_iff).mp (e ▸ hcm)).1 rfl)
              · have hcl : c ≠ l := fun e => hlev (e ▸ hcm)
                rcases List.mem_cons.mp hcm with hcm | hcm
                · exact tr1 c (hc' c (Or.inr (Or.inl hcm))) hcl
                · exact tr1 c (hc' c (Or.inr (Or.inr hcm))) hcl
          · have hwb : ¬ waits l pend' = true := fun h => hw ((waits_iff l pend').mp h)
            rw [if_neg hwb]
            have hk := ih (BS.ask i k) pend' (put t l a) hrest ?_ ?_ hord
            · exact hk
            · simp only [evs, List.map_cons]
              rw [List.nodup_append, List.nodup_cons]
              exact ⟨hndw, ⟨hni, hnde⟩, hdisj⟩
            · simp only [evs, List.map_cons]
              intro c hcm
              rcases List.mem_append.mp hcm with hcm | hcm
              · exact tr1 c (hc' c (Or.inl hcm)) (fun e => hw (e ▸ hcm))
              · have hcl : c ≠ l := fun e => hlev (e ▸ hcm)
                rcases List.mem_cons.mp hcm with hcm | hcm
                · exact tr1 c (hc' c (Or.inr (Or.inl hcm))) hcl
                · exact tr1 c (hc' c (Or.inr (Or.inr hcm))) hcl

end Ok

/-! ## Splitting the law -/

section Split
variable {I A X C : Type} [DecidableEq I] [Inhabited A] [Fintype A]

omit [DecidableEq I] [Inhabited A] in
theorem pmean_append : ∀ (pre post : List (I × Option A)) (f : List A → ℚ),
    pmean f (pre ++ post) = pmean (fun as => pmean (fun bs => f (as ++ bs)) post) pre := by
  intro pre
  induction pre with
  | nil => intro post f; rfl
  | cons p rest ih =>
      intro post f
      obtain ⟨c, o⟩ := p
      cases o with
      | some b => simp only [List.cons_append, pmean, ih]
      | none => simp only [List.cons_append, pmean]; exact mean_congr fun a => ih post _

omit [DecidableEq I] [Inhabited A] in
theorem pmean_mean_comm {Z : Type} [Fintype Z] : ∀ (pre : List (I × Option A)) (F : Z → List A → ℚ),
    pmean (fun as => mean (fun z => F z as)) pre = mean (fun z => pmean (F z) pre) := by
  intro pre
  induction pre with
  | nil => intro F; rfl
  | cons p rest ih =>
      intro F
      obtain ⟨c, o⟩ := p
      cases o with
      | some b => simp only [pmean]; exact ih _
      | none =>
          simp only [pmean]
          rw [mean_comm]
          exact mean_congr fun a => ih _

omit [DecidableEq I] [Inhabited A] in
theorem blaw_split (g : X → List A → C) (obs : C → ℚ) :
    ∀ (own : BS I A X) (pre post : List (I × Option A)),
      blaw g obs own (pre ++ post) =
        pmean (fun as => blaw (fun x bs => g x (as ++ bs)) obs own post) pre := by
  intro own
  induction own with
  | done x => intro pre post; exact pmean_append pre post _
  | ask i k ih =>
      intro pre post
      simp only [blaw]
      rw [pmean_mean_comm pre (fun a as => blaw (fun x bs => g x (as ++ bs)) obs (k a) post)]
      exact mean_congr fun a => ih a pre post
  | spawn c n ih =>
      intro pre post
      simp only [blaw]
      rw [List.append_assoc]
      exact ih pre (post ++ [(c, none)])

omit [DecidableEq I] [Inhabited A] in
theorem pmean_le [Nonempty A] (c : ℚ) : ∀ (pre : List (I × Option A)) (f : List A → ℚ),
    (∀ as, as.length = pre.length → f as ≤ c) → pmean f pre ≤ c := by
  intro pre
  induction pre with
  | nil => intro f h; exact h [] rfl
  | cons p rest ih =>
      intro f h
      obtain ⟨d, o⟩ := p
      cases o with
      | some b => exact ih _ fun as has => h _ (by simp [has])
      | none =>
          calc mean (fun a => pmean (fun as => f (a :: as)) rest) ≤ mean (fun _ : A => c) :=
                mean_mono fun a => ih _ fun as has => h _ (by simp [has])
            _ = c := mean_const c

end Split

#print axioms bfollow_ok
#print axioms blaw_split
end R0C.V3
