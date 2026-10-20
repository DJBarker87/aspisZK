import R13SourceTerminalBody
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1Stage2.R13SourceTerminal
open AspisR1Stage2

private theorem bind_success {A B : Type} (m : Result A) (k : A → Result B) (v : B)
    (h : (do let x ← m; k x) = ok v) : ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- Invert the actual exhausted-range branch. This makes no claim that the
inner loop reaches this branch, or that it implements BinMultiproof.Level. -/
theorem terminal_acceptance (ops : TerminalOps)
    {T : Type} (D : aspis_core.digest.Digest32 T) (hash : T)
    (root : Array U8 32#usize) (nodes : Slice U8)
    (iter iter1 : core.ops.range.Range U32) (arity : multiproof.Arity)
    (idx outIdx : Indices) (val outVal : Values) (n at1 : Usize) (pending : Option Bool)
    (exhausted : core.iter.range.IteratorRange.next core.iter.range.StepU32 iter = ok (none, iter1))
    (h : terminalBody ops D hash root nodes iter arity idx val n at1 pending =
      ok (done (outIdx, outVal, some true))) :
    n = 1#usize ∧ multiproof.index_at idx 0#usize = ok 0#u32 ∧
      multiproof.root_matches val root = ok true ∧ at1 = Slice.len nodes ∧
      outIdx = idx ∧ outVal = val := by
  unfold terminalBody at h
  rw [exhausted] at h
  simp only [bind_tc_ok] at h
  split at h
  · rename_i hn
    obtain ⟨i, hi, h⟩ := bind_success _ _ _ h
    split at h
    · rename_i hz
      subst i
      obtain ⟨b, hb, h⟩ := bind_success _ _ _ h
      cases b with
      | false => simp at h
      | true =>
        have he : idx = outIdx ∧ val = outVal ∧ at1 = Slice.len nodes := by simpa using h
        exact ⟨hn, hi, hb, he.2.2, he.1.symm, he.2.1.symm⟩
    · simp at h
  · simp at h

#print axioms bind_success
#print axioms terminal_acceptance
end AspisR1Stage2.R13SourceTerminal
