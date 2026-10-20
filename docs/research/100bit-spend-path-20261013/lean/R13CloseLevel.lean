import R13CloseLevelBody
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1Stage2.R13Close.Level

/-- Exact functional effect of one occupied binary-parent update. The source
may consume one or two inputs. Failed sibling lookup terminates with false. -/
def Progress (idx : Idx) (val : Val) (w i : Usize) (pending : Option Bool)
    (r : ControlFlow (multiproof.Arity × Idx × Val × Usize × Usize × Usize × Option Bool)
      (multiproof.Arity × Idx × Val × Usize × Usize × Option Bool × U32)) : Prop :=
  match r with
  | cont (a, idx', val', _, w', i', pending') =>
      a = .Two ∧ pending' = pending ∧ w'.val = w.val + 1 ∧
      (i'.val = i.val + 1 ∨ i'.val = i.val + 2) ∧
      ∃ parent digest, Array.update idx w parent = ok idx' ∧
        Array.update val w digest = ok val'
  | done (a, idx', val', _, _, _, _) => a = .Two ∧ idx' = idx ∧ val' = val

theorem binary_body_progress (ops : LevelOps) {H : Type}
    (D : aspis_core.digest.Digest32 H) (hash : H) (n : Usize) (nodes : Slice U8)
    (idx : Idx) (val : Val) (at1 w i : Usize) (pending : Option Bool)
    (r : ControlFlow (multiproof.Arity × Idx × Val × Usize × Usize × Usize × Option Bool)
      (multiproof.Arity × Idx × Val × Usize × Usize × Option Bool × U32))
    (h : levelBody ops D hash n nodes .Two idx val at1 w i pending = ok r) :
    Progress idx val w i pending r := by
  unfold levelBody at h
  split at h
  · obtain ⟨index, hindex, h⟩ := bind_success h
    simp only [multiproof.Arity.bits, bind_tc_ok] at h
    obtain ⟨parent, hparent, h⟩ := bind_success h
    obtain ⟨next, hnext, h⟩ := bind_success h
    have hn := UScalar.add_equiv i 1#usize
    rw [hnext] at hn
    have hn' : next.val = i.val + 1 := by simpa using hn.2.1
    split at h
    · obtain ⟨index', hindex', h⟩ := bind_success h
      simp only [lift, bind_tc_ok] at h
      split at h
      · obtain ⟨digest, hdigest, h⟩ := bind_success h
        obtain ⟨next2, hnext2, h⟩ := bind_success h
        obtain ⟨idx', hidx', h⟩ := bind_success h
        obtain ⟨val', hval', h⟩ := bind_success h
        obtain ⟨w', hw', h⟩ := bind_success h
        have hw := UScalar.add_equiv w 1#usize
        have hn2 := UScalar.add_equiv i 2#usize
        rw [hw'] at hw
        rw [hnext2] at hn2
        cases h
        exact ⟨rfl, rfl, by simpa using hw.2.1, Or.inr (by simpa using hn2.2.1),
          parent, digest, hidx', hval'⟩
      · obtain ⟨finish, hfinish, h⟩ := bind_success h
        obtain ⟨sibling, hsibling, h⟩ := bind_success h
        cases sibling with
        | none => cases h; exact ⟨rfl, rfl, rfl⟩
        | some sib =>
          simp only [lift, bind_tc_ok] at h
          obtain ⟨digest, hdigest, h⟩ := bind_success h
          obtain ⟨idx', hidx', h⟩ := bind_success h
          obtain ⟨val', hval', h⟩ := bind_success h
          obtain ⟨w', hw', h⟩ := bind_success h
          have hw := UScalar.add_equiv w 1#usize
          rw [hw'] at hw
          cases h
          exact ⟨rfl, rfl, by simpa using hw.2.1, Or.inl hn', parent, digest, hidx', hval'⟩
    · obtain ⟨finish, hfinish, h⟩ := bind_success h
      obtain ⟨sibling, hsibling, h⟩ := bind_success h
      cases sibling with
      | none => cases h; exact ⟨rfl, rfl, rfl⟩
      | some sib =>
        simp only [lift, bind_tc_ok] at h
        obtain ⟨digest, hdigest, h⟩ := bind_success h
        obtain ⟨idx', hidx', h⟩ := bind_success h
        obtain ⟨val', hval', h⟩ := bind_success h
        obtain ⟨w', hw', h⟩ := bind_success h
        have hw := UScalar.add_equiv w 1#usize
        rw [hw'] at hw
        cases h
        exact ⟨rfl, rfl, by simpa using hw.2.1, Or.inl hn', parent, digest, hidx', hval'⟩
  · cases h; exact ⟨rfl, rfl, rfl⟩

/-- The source writes exactly the functional set update and leaves the unread
suffix untouched whenever the write cursor is behind the read cursor. -/
theorem binary_cont_frame (ops : LevelOps) {H : Type}
    (D : aspis_core.digest.Digest32 H) (hash : H) (n : Usize) (nodes : Slice U8)
    (idx idx' : Idx) (val val' : Val) (at1 at' w w' i i' : Usize)
    (pending pending' : Option Bool) (arity' : multiproof.Arity)
    (hw : w.val ≤ i.val)
    (h : levelBody ops D hash n nodes .Two idx val at1 w i pending =
      ok (cont (arity', idx', val', at', w', i', pending'))) :
    arity' = .Two ∧ pending' = pending ∧ w'.val ≤ i'.val ∧
      (∃ parent digest, idx'.val = idx.val.set w.val parent ∧
        val'.val = val.val.set w.val digest) ∧
      ∀ j, i'.val ≤ j → idx'.val[j]? = idx.val[j]? ∧ val'.val[j]? = val.val[j]? := by
  obtain ⟨ha, hp, hw', hi', parent, digest, hidx, hval⟩ :=
    binary_body_progress ops D hash n nodes idx val at1 w i pending _ h
  have hwi : w.val < i'.val := by rcases hi' with hi' | hi' <;> omega
  refine ⟨ha, hp, by omega, ⟨parent, digest, (update_success idx idx' w parent hidx).2,
    (update_success val val' w digest hval).2⟩, ?_⟩
  intro j hj
  exact ⟨update_unread idx idx' w parent i'.val j hwi hj hidx,
    update_unread val val' w digest i'.val j hwi hj hval⟩

#print axioms binary_body_progress
#print axioms binary_cont_frame
end AspisR1Stage2.R13Close.Level
