import ToBytesP6StateInvariantV1
import PaintSourceLimbsV1
open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false
namespace P6ToBytes.OutputInvariant
open P6ToBytes.Steps P6ToBytes.ActiveBodyV11 P6ToBytes.StateInvariant
open AspisR1WideToBytesSource

def zipSource (z : Zip) : List Std.U8 := z.fst.source.val

def writeLimb (x : field.wide_exact.WideExact) (i : Nat)
    (src : List Std.U8) : List Std.U8 :=
  src.setSlice! (4*i) (core.num.U32.to_le_bytes (sourceLimbs x)[i]!).val

def painted (x : field.wide_exact.WideExact) : Nat → List Std.U8 → List Std.U8
  | 0, src => src
  | n+1, src => painted x n (writeLimb x n src)

theorem painted_succ (x : field.wide_exact.WideExact) (i : Nat) (src : List Std.U8) :
    painted x (i+1) src = painted x i (writeLimb x i src) := by
  simp [painted, Nat.add_comm]

theorem painted_eq_generic (x : field.wide_exact.WideExact) (n : Nat)
    (src : List Std.U8) :
    painted x n src = AspisR1PaintBlocksPrefixV1.paint
      (AspisR1PaintSourceLimbsV1.limbBlock x) 4 n src := by
  induction n generalizing src with
  | zero => rfl
  | succ n ih =>
      simp only [painted, AspisR1PaintBlocksPrefixV1.paint, writeLimb,
        AspisR1PaintSourceLimbsV1.limbBlock]
      exact ih _

theorem step_paints_prefix (x : field.wide_exact.WideExact) (i : Nat)
    (c : ChunkIt) (d : LimbIt) (bk : Back)
    (hsource : c.source.val.length = 32)
    (hsize : c.chunkSize.val = 4)
    (hcc : c.cursor = 4*i)
    (hdata : d.data = sourceLimbs x)
    (hdc : d.cursor = i)
    (hi : i < 8)
    (hback : ∀ z, zipSource (bk z) = painted x i (zipSource z)) :
    ∃ c' d' bk',
      step ((⟨c,d⟩ : Zip), bk) = .ok (.cont ((⟨c',d'⟩ : Zip),bk')) ∧
      ∀ z, zipSource (bk' z) = painted x (i+1) (zipSource z) := by
  rcases body_progress x i c d bk hsource hsize hcc hdata hdc hi with
    ⟨c',d',bk',hstep,hdata',hcc',hdc',hsource',hsize'⟩
  refine ⟨c',d',bk',hstep,?_⟩
  intro z
  -- Unfold the emitted body to expose its captured-start continuation.
  have hstep' := hstep
  have hchunkLen : (List.take 4 (List.drop (4*i) c.source.val)).length = 4 := by
    simp [List.length_take, List.length_drop, hsource]
    omega
  have hchunkActive : 4*i < 32 ∧ 4*i ≤ 28 := by omega
  have hlimbActive : i < (sourceLimbs x).length := by
    simp [sourceLimbs]
    omega
  simp [step, lift, bind_tc_ok, field.wide_exact.WideExact.to_le_bytes_loop.body,
    P6ToBytes.StdModel.zipNext,
    P6ToBytes.StdModel.MutableIterator.zip.trait_default,
    P6ToBytes.StdModel.MutableIterator,
    Aeneas.Std.core.slice.Slice.chunks_exact_mut,
    Aeneas.Std.core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    Aeneas.Std.core.slice.iter.ChunksExactMut.Insts.CoreIterTraitsIteratorIteratorMutASlice.next,
    Aeneas.Std.Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter,
    core.slice.Slice.copy_from_slice, Array.to_slice, Slice.len,
    u32BytesLen, UScalar.ofNatCore_val_eq, hsource, hsize, hcc, hdata,
    hdc, hi, hchunkLen, hchunkActive, hlimbActive,
    List.length_drop, List.length_take] at hstep'
  rcases hstep' with ⟨_, _, hcallback⟩
  have hcallbackAt := congrFun hcallback z
  rw [← hcallbackAt]
  -- The current back continuation writes this chunk at the captured start,
  -- then the previously accumulated continuation handles earlier chunks.
  simpa [zipSource, writeLimb, painted_succ, hlimbActive] using
    (hback { z with fst := { z.fst with source :=
      ⟨(zipSource z).setSlice! (4*i)
        (core.num.U32.to_le_bytes (sourceLimbs x)[i]!).val, by
          rw [List.length_setSlice!]
          exact z.fst.source.property⟩ } })

theorem stateAt_paints (x : field.wide_exact.WideExact) :
    ∀ i, i ≤ 8 → ∀ z,
      zipSource ((StateInvariant.stateAt x i).2 z) =
        painted x i (zipSource z) := by
  intro i
  induction i with
  | zero =>
      intro hi z
      rfl
  | succ n ih =>
      intro hi z
      have hn : n < 8 := by omega
      rcases StateInvariant.stateAt_invariant x n (by omega) with
        ⟨c,d,bk,hs,hsource,hsize,hcc,hdata,hdc⟩
      have hback : ∀ z, zipSource (bk z) = painted x n (zipSource z) := by
        intro z
        simpa [hs] using ih (by omega) z
      rcases step_paints_prefix x n c d bk hsource hsize hcc hdata hdc hn hback with
        ⟨c',d',bk',hstep,hpaint⟩
      have hnext : StateInvariant.stateAt x (n+1) = ((⟨c',d'⟩ : Zip),bk') := by
        simp only [StateInvariant.stateAt]
        rw [hs]
        change (match step ((⟨c,d⟩ : Zip),bk) with
          | .ok (.cont s) => s
          | _ => ((⟨c,d⟩ : Zip),bk)) = ((⟨c',d'⟩ : Zip),bk')
        rw [hstep]
      rw [hnext]
      exact hpaint z

theorem terminal_returns_back (x : field.wide_exact.WideExact) :
    step (StateInvariant.stateAt x 8) =
      .ok (.done (StateInvariant.stateAt x 8).2) := by
  rcases StateInvariant.stateAt_invariant x 8 (by omega) with
    ⟨c,d,bk,hs,hsource,hsize,hcc,hdata,hdc⟩
  have hcc' : c.cursor = 32 := by simpa using hcc
  have hdata' : d.data.length = 8 := by
    have hlen := congrArg List.length hdata
    simpa [sourceLimbs] using hlen
  rw [hs]
  simp [step, field.wide_exact.WideExact.to_le_bytes_loop.body,
    P6ToBytes.StdModel.zipNext,
    P6ToBytes.StdModel.MutableIterator.zip.trait_default,
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

theorem loop_returns_final_back (x : field.wide_exact.WideExact) :
    Aeneas.Std.loop (fun s : Zip × Back => step s) (StateInvariant.stateAt x 0) =
      .ok (StateInvariant.stateAt x 8).2 := by
  have descend : ∀ k, k ≤ 8 →
      Aeneas.Std.loop (fun s : Zip × Back => step s)
        (StateInvariant.stateAt x (8-k)) = .ok (StateInvariant.stateAt x 8).2 := by
    intro k
    induction k with
    | zero =>
        intro hk
        exact loop_done _ _ _ (terminal_returns_back x)
    | succ k ih =>
        intro hk
        have hidx : 8-(k+1)+1 = 8-k := by omega
        obtain ⟨c,d,bk,hs,hn⟩ := StateInvariant.stateAt_progress x (8-(k+1)) (by omega)
        rw [hidx] at hn
        have hs' : step (StateInvariant.stateAt x (8-(k+1))) =
            .ok (.cont (StateInvariant.stateAt x (8-k))) := by
          rw [← hn] at hs
          exact hs
        exact loop_cont _ _ _ _ hs' (ih (by omega))
  exact descend 8 (by omega)

def serializedWords (x : field.wide_exact.WideExact) : List Std.U8 :=
  (sourceLimbs x).flatMap (fun w => (core.num.U32.to_le_bytes w).val)

theorem serializedWords_length (x : field.wide_exact.WideExact) :
    (serializedWords x).length = 32 := by
  simp [serializedWords, sourceLimbs, u32BytesLen]

theorem source_loop_success (x : field.wide_exact.WideExact) :
    field.wide_exact.WideExact.to_le_bytes_loop (initZip x) (fun z => z) =
      .ok (StateInvariant.stateAt x 8).2 := by
  change Aeneas.Std.loop (fun s : Zip × Back => step s)
    (StateInvariant.stateAt x 0) = .ok (StateInvariant.stateAt x 8).2
  exact loop_returns_final_back x

theorem source_loop_success_raw (x : field.wide_exact.WideExact) :
    Aeneas.Std.loop
      (fun s : Zip × Back =>
        field.wide_exact.WideExact.to_le_bytes_loop.body s.1 s.2)
      (initZip x, fun z => z) = .ok (StateInvariant.stateAt x 8).2 := by
  simpa [step, StateInvariant.stateAt] using loop_returns_final_back x

theorem loop_final_contents (x : field.wide_exact.WideExact) :
    zipSource ((StateInvariant.stateAt x 8).2 (initZip x)) = serializedWords x := by
  rw [stateAt_paints x 8 (by omega) (initZip x)]
  rw [painted_eq_generic]
  simpa [initZip, initChunkIt, initSlice, zipSource, serializedWords] using
    AspisR1PaintSourceLimbsV1.paint_eight_limbs_exact x

theorem source_limbs_into_iter (x : field.wide_exact.WideExact) :
    Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter
      (Array.make 8#usize [x.c0.c0.a, x.c0.c0.b, x.c0.c1.a, x.c0.c1.b,
        x.c1.c0.a, x.c1.c0.b, x.c1.c1.a, x.c1.c1.b]) =
      .ok (P6ToBytes.Steps.initLimbIt x) := by
  rfl

theorem source_make_data (x : field.wide_exact.WideExact) :
    (Array.make 8#usize [x.c0.c0.a, x.c0.c0.b, x.c0.c1.a, x.c0.c1.b,
      x.c1.c0.a, x.c1.c0.b, x.c1.c1.a, x.c1.c1.b]).val = sourceLimbs x := by
  rfl

theorem source_chunk_initial :
    core.slice.Slice.chunks_exact_mut initSlice 4#usize =
      .ok (initChunkIt, fun it => it.source) := by
  simp [core.slice.Slice.chunks_exact_mut, initSlice, initChunkIt,
    Aeneas.Std.Array.to_slice, Slice.len, UScalar.ofNatCore_val_eq]

theorem source_zip_initial (x : field.wide_exact.WideExact) :
    P6ToBytes.StdModel.MutableIterator.zip.trait_default
      (core.slice.iter.ChunksExactMut.Insts.CoreIterTraitsIteratorIteratorMutASlice
        Std.U8)
      (Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter Std.U32 8#usize)
      (initChunkIt)
      (Array.make 8#usize [x.c0.c0.a, x.c0.c0.b, x.c0.c1.a, x.c0.c1.b,
        x.c1.c0.a, x.c1.c0.b, x.c1.c1.a, x.c1.c1.b]) =
      .ok (initZip x, fun back => (back (initZip x)).fst) := by
  simp [P6ToBytes.StdModel.MutableIterator.zip.trait_default,
    Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter,
    Array.make, source_make_data, initZip, initLimbIt, sourceLimbs]

theorem to_le_bytes_output_contents (x : field.wide_exact.WideExact) :
    ∃ out, field.wide_exact.WideExact.to_le_bytes x = .ok out ∧
      out.val = serializedWords x := by
  have hloop := loop_returns_final_back x
  have hcontents := loop_final_contents x
  refine ⟨⟨serializedWords x, ?_⟩, ?_, rfl⟩
  · simpa [UScalar.ofNatCore_val_eq] using serializedWords_length x
  · change
      (do
        let (cem, chunksBack) ← core.slice.Slice.chunks_exact_mut initSlice 4#usize
        let a ← field.wide_exact.WideExact.to_limbs x
        let (iter, zipBack) ←
          P6ToBytes.StdModel.MutableIterator.zip.trait_default
            (core.slice.iter.ChunksExactMut.Insts.CoreIterTraitsIteratorIteratorMutASlice Std.U8)
            (Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter Std.U32 8#usize) cem a
        let back ← field.wide_exact.WideExact.to_le_bytes_loop iter (fun z => z)
        ok (Aeneas.Std.Array.from_slice (Array.repeat 32#usize 0#u8) (chunksBack (zipBack back)))) =
      .ok ⟨serializedWords x, by
        simpa [UScalar.ofNatCore_val_eq] using serializedWords_length x⟩
    rw [source_chunk_initial]
    simp only [bind_tc_ok]
    rw [field.wide_exact.WideExact.to_limbs]
    simp only [bind_tc_ok]
    rw [source_zip_initial]
    simp only [bind_tc_ok]
    rw [source_loop_success]
    simp only [bind_tc_ok]
    trace_state
    fail "root wrapper diagnostic: stop before final byte equality"

#print axioms step_paints_prefix
#print axioms painted_eq_generic
#print axioms stateAt_paints
#print axioms terminal_returns_back
#print axioms loop_returns_final_back
#print axioms source_loop_success
#print axioms source_limbs_into_iter
#print axioms loop_final_contents
#print axioms to_le_bytes_output_contents
end P6ToBytes.OutputInvariant
