import R13CloseLevel
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1Stage2.R13Close.Level

def levelLoop (ops : LevelOps)
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (hash : H) (arity : multiproof.Arity) (idx : Array Std.U32 16#usize)
  (val : Array (Array Std.U8 32#usize) 16#usize) (n : Std.Usize)
  (nodes : Slice Std.U8) (at1 : Std.Usize) (w : Std.Usize) (i : Std.Usize)
  (pending_return : Option Bool) :
  Result (multiproof.Arity × (Array Std.U32 16#usize) × (Array (Array Std.U8
    32#usize) 16#usize) × Std.Usize × Std.Usize × (Option Bool) × Std.U32)
  := do
  loop
    (fun (arity1, idx1, val1, at2, w1, i1, pending_return1) =>
      levelBody ops aspis_coredigestDigest32Inst
      hash n nodes arity1 idx1 val1 at2 w1 i1 pending_return1)
    (arity, idx, val, at1, w, i, pending_return)

/-- Chronological writes to the two actual source scratch buffers. -/
abbrev Write := Usize × U32 × Array U8 32#usize
abbrev BufferLists := List U32 × List (Array U8 32#usize)
def applyWrite (buffers : BufferLists) (write : Write) : BufferLists :=
  (buffers.1.set write.1.val write.2.1, buffers.2.set write.1.val write.2.2)

/-- Every successful extracted inner level loop starting at Arity::Two has
exactly the functional fold of its writes. This proves buffer mutation
simulation; identifying the writes with BinMultiproof.Level is separate. -/
theorem binary_loop_write_fold (ops : LevelOps) {H : Type}
    (D : aspis_core.digest.Digest32 H) (hash : H)
    (idx idx' : Idx) (val val' : Val) (n : Usize) (nodes : Slice U8)
    (at1 w i at' n' : Usize) (pending pending' : Option Bool)
    (arity' : multiproof.Arity) (code : U32)
    (h : levelLoop ops D hash .Two idx val n nodes at1 w i pending =
      ok (arity', idx', val', n', at', pending', code)) :
    arity' = .Two ∧ ∃ writes : List Write,
      (idx'.val, val'.val) = writes.foldl applyWrite (idx.val, val.val) := by
  let initial : BufferLists := (idx.val, val.val)
  have hp : (fun out : multiproof.Arity × Idx × Val × Usize × Usize × Option Bool × U32 =>
      out.1 = .Two ∧ ∃ writes : List Write,
        (out.2.1.val, out.2.2.1.val) = writes.foldl applyWrite initial)
      (arity', idx', val', n', at', pending', code) := by
    apply loop_invariant
      (fun s : multiproof.Arity × Idx × Val × Usize × Usize × Usize × Option Bool =>
        levelBody ops D hash n nodes s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2.1
          s.2.2.2.2.2.1 s.2.2.2.2.2.2)
      (fun s => s.1 = .Two ∧ ∃ writes : List Write,
        (s.2.1.val, s.2.2.1.val) = writes.foldl applyWrite initial)
      (fun out => out.1 = .Two ∧ ∃ writes : List Write,
        (out.2.1.val, out.2.2.1.val) = writes.foldl applyWrite initial)
      ?_ ⟨rfl, [], rfl⟩ h
    rintro ⟨a, currentIdx, currentVal, currentAt, currentW, currentI, currentPending⟩
      ⟨ha, writes, hwrites⟩ r hr
    change a = .Two at ha
    subst a
    have hs := binary_body_progress ops D hash n nodes currentIdx currentVal
      currentAt currentW currentI currentPending r hr
    cases r with
    | cont state =>
      rcases state with ⟨a, nextIdx, nextVal, nextAt, nextW, nextI, nextPending⟩
      obtain ⟨ha, _, _, _, parent, digest, hidx, hval⟩ := hs
      refine ⟨ha, writes ++ [(currentW, parent, digest)], ?_⟩
      have hidx' := (update_success currentIdx nextIdx currentW parent hidx).2
      have hval' := (update_success currentVal nextVal currentW digest hval).2
      change (currentIdx.val, currentVal.val) = writes.foldl applyWrite initial at hwrites
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [← hwrites]
      exact Prod.ext hidx' hval'
    | done state =>
      rcases state with ⟨a, finalIdx, finalVal, finalN, finalAt, finalPending, finalCode⟩
      obtain ⟨ha, hidx, hval⟩ := hs
      exact ⟨ha, writes, by simpa only [hidx, hval] using hwrites⟩
  exact hp

#print axioms binary_loop_write_fold
end AspisR1Stage2.R13Close.Level
