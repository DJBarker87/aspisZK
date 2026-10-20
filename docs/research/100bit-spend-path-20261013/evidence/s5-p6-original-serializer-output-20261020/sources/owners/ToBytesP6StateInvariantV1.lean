import ToBytesP6ActiveBodyV12
open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false
namespace P6ToBytes.StateInvariant
open P6ToBytes.Steps P6ToBytes.ActiveBodyV11 AspisR1WideToBytesSource

def stateAt (x : field.wide_exact.WideExact) : Nat → Zip × Back
  | 0 => (initZip x, fun z => z)
  | n+1 => match step (stateAt x n) with
      | .ok (.cont s) => s
      | _ => stateAt x n

def invariant (x : field.wide_exact.WideExact) (i : Nat) (s : Zip × Back) : Prop :=
  ∃ c d bk, s = ((⟨c,d⟩ : Zip),bk) ∧
    c.source.val.length = 32 ∧ c.chunkSize.val = 4 ∧
    c.cursor = 4*i ∧ d.data = sourceLimbs x ∧ d.cursor = i

theorem stateAt_invariant (x : field.wide_exact.WideExact) :
    ∀ i, i ≤ 8 → invariant x i (stateAt x i) := by
  intro i hi
  induction i with
  | zero =>
      refine ⟨initChunkIt, initLimbIt x, fun z => z, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rfl
      · simp [initChunkIt, initSlice, Array.to_slice]
      · rfl
      · rfl
      · rfl
      · rfl
  | succ n ih =>
      have hn : n < 8 := by omega
      rcases ih (by omega) with ⟨c,d,bk,hs,hsource,hsize,hcc,hdata,hdc⟩
      rcases P6ToBytes.ActiveBodyV11.body_progress x n c d bk
        hsource hsize hcc hdata hdc hn with
        ⟨c',d',bk',hstep,hdata',hcc',hdc',hsource',hsize'⟩
      have hnext : stateAt x (n+1) = ((⟨c',d'⟩ : Zip),bk') := by
        simp only [stateAt]
        rw [hs]
        change (match step ((⟨c,d⟩ : Zip),bk) with
          | .ok (.cont s) => s
          | _ => ((⟨c,d⟩ : Zip),bk)) = ((⟨c',d'⟩ : Zip),bk')
        rw [hstep]
      refine ⟨c',d',bk',hnext,?_,?_,hcc',hdata'.trans hdata,hdc'⟩
      · rw [hsource']
        exact hsource
      · rw [hsize']
        exact hsize

theorem stateAt_progress (x : field.wide_exact.WideExact) (i : Nat) (hi : i < 8) :
    ∃ c d bk,
      step (stateAt x i) = .ok (.cont ((⟨c,d⟩ : Zip),bk)) ∧
      stateAt x (i+1) = ((⟨c,d⟩ : Zip),bk) := by
  rcases stateAt_invariant x i (by omega) with
    ⟨c,d,bk,hs,hsource,hsize,hcc,hdata,hdc⟩
  rcases P6ToBytes.ActiveBodyV11.body_progress x i c d bk
      hsource hsize hcc hdata hdc hi with
    ⟨c',d',bk',hstep,hdata',hcc',hdc',hsource',hsize'⟩
  have hnext : stateAt x (i+1) = ((⟨c',d'⟩ : Zip),bk') := by
    simp only [stateAt]
    rw [hs]
    change (match step ((⟨c,d⟩ : Zip),bk) with
      | .ok (.cont s) => s
      | _ => ((⟨c,d⟩ : Zip),bk)) = ((⟨c',d'⟩ : Zip),bk')
    rw [hstep]
  refine ⟨c',d',bk',?_,hnext⟩
  rw [hs]
  exact hstep

theorem terminal_done (x : field.wide_exact.WideExact) :
    ∃ out, step (stateAt x 8) = .ok (.done out) := by
  rcases stateAt_invariant x 8 (by omega) with
    ⟨c,d,bk,hs,hsource,hsize,hcc,hdata,hdc⟩
  have hcc' : c.cursor = 32 := by simpa using hcc
  have hdata' : d.data.length = 8 := by
    have hlen := congrArg List.length hdata
    simpa [sourceLimbs] using hlen
  rw [hs]
  simp [step, field.wide_exact.WideExact.to_le_bytes_loop.body,
    P6ToBytes.StdModel.zipNext,
    P6ToBytes.StdModel.MutableIterator.zip.trait_default,
    P6ToBytes.StdModel.MutableIterator,
    Aeneas.Std.core.slice.iter.ChunksExactMut.Insts.CoreIterTraitsIteratorIteratorMutASlice.next,
    Aeneas.Std.core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    Aeneas.Std.Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter,
    hsource, hsize, hcc', hdata', hdc, Slice.len]

private theorem loop_cont {S T : Type} (f : S → Result (ControlFlow S T))
    (s s' : S) (out : T) (hs : f s = .ok (.cont s'))
    (ht : Aeneas.Std.loop f s' = .ok out) :
    Aeneas.Std.loop f s = .ok out := by
  rw [Aeneas.Std.loop.eq_def]
  simp [hs, ht]

private theorem loop_done {S T : Type} (f : S → Result (ControlFlow S T))
    (s : S) (out : T) (hs : f s = .ok (.done out)) :
    Aeneas.Std.loop f s = .ok out := by
  rw [Aeneas.Std.loop.eq_def]
  simp [hs]

theorem loop_success (x : field.wide_exact.WideExact) :
    ∃ out, Aeneas.Std.loop (fun s : Zip × Back => step s) (stateAt x 0) = .ok out := by
  have descend : ∀ k, k ≤ 8 → ∃ out,
      Aeneas.Std.loop (fun s : Zip × Back => step s) (stateAt x (8-k)) = .ok out := by
    intro k
    induction k with
    | zero =>
        intro hk
        obtain ⟨out,hs⟩ := terminal_done x
        exact ⟨out, loop_done _ _ _ hs⟩
    | succ k ih =>
        intro hk
        obtain ⟨out,ht⟩ := ih (by omega)
        have hidx : 8-(k+1)+1 = 8-k := by omega
        obtain ⟨c,d,bk,hs,hn⟩ := stateAt_progress x (8-(k+1)) (by omega)
        rw [hidx] at hn
        have hs' : step (stateAt x (8-(k+1))) =
            .ok (.cont (stateAt x (8-k))) := by
          rw [← hn] at hs
          exact hs
        exact ⟨out, loop_cont _ _ _ _ hs' ht⟩
  exact descend 8 (by omega)

#print axioms stateAt_invariant
#print axioms stateAt_progress
#print axioms terminal_done
#print axioms loop_success
end P6ToBytes.StateInvariant
