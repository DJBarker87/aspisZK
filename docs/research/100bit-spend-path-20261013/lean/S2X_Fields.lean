import S2X_SecondCut

/-! Exact Required14 field implications. Source observations are explicit:
these lemmas do not construct native Inputs or a same-execution certificate. -/
set_option autoImplicit false
namespace AspisR1.S2X
open Aeneas Aeneas.Std Result MultiproofConeCanonical S2LeadInterface
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep R9PoolRuntimeBinding

theorem checkpoint_length_field (ops : AdapterRw.Ops)
    (program : AdapterRw.solana_pubkey.Pubkey) (accounts : Slice AdapterRw.Cuts.Account)
    (data : Slice U8) (checkpoint : alloc.vec.Vec U8)
    (accepted : AdapterRw.r1_pool_adapter.owned.stage1_owned ops program accounts data = ok (.Ok checkpoint))
    (account : AdapterRw.Cuts.Account)
    (at2 : Slice.index_usize accounts 2#usize = ok account)
    (snapshot : OwnedSnapshotShape ops account) (entrySize : snapshot.bytes.val.length = 1768)
    (savedBytes : Bytes) (savedAtWrite : savedBytes = bytesOf checkpoint.val) :
    savedBytes.length = 1768 := by
  rw [savedAtWrite]
  simpa only [bytesOf,List.length_map] using
    accepted_checkpoint_length ops program accounts data checkpoint accepted account at2 snapshot entrySize

/-- Fixed paired cut observations, NOT universal quantification over all
successful child calls. range1/range2 are supplied by the actual accepted
owned callers. observed1/observed2 remain source-observation obligations. -/
theorem proof_suffix_field {Observer : Type} (c : S2LeadInterface.Inputs Observer)
    (hash : Bytes → State) (written current : R9PoolRuntimeBinding.Inputs)
    (p2prime : P2Prime hash written current) (matched : digestMatches hash written current)
    (raw1 selected1 raw2 selected2 : Slice U8) (end1 end2 : Usize)
    (range1 : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      raw1 {start := 688#usize, «end» := end1} = ok selected1)
    (range2 : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      raw2 {start := 688#usize, «end» := end2} = ok selected2)
    (length1 : raw1.val.length = end1.val) (length2 : raw2.val.length = end2.val)
    (writtenCut : bytesOf selected1.val = written.proof)
    (currentCut : bytesOf selected2.val = current.proof)
    (observed1 : c.reached .tx1 → c.proofAccount .tx1 = bytesOf raw1.val)
    (observed2 : c.reached .tx2 → c.proofAccount .tx2 = bytesOf raw2.val) :
    ∀ s, c.reached s → s = .tx1 ∨ s = .tx2 →
      c.proofAccount s = (c.proofAccount s).take 688 ++ written.proof := by
  have shape1 := (AdapterRw.Ranges.suffix_exact raw1 selected1 688#usize end1
    (successful_range_ordered raw1 selected1 688#usize end1 range1) length1 range1).2
  change raw1.val = raw1.val.take 688 ++ selected1.val at shape1
  have mapped : bytesOf raw1.val = (bytesOf raw1.val).take 688 ++ written.proof := by
    rw [←writtenCut]
    simpa only [bytesOf,List.map_append,List.map_take] using congrArg bytesOf shape1
  have shape2 := tx2_suffix hash written current p2prime matched raw2 selected2 end2 length2
    (successful_range_ordered raw2 selected2 688#usize end2 range2) range2 currentCut
  intro s reached site
  rcases site with h | h <;> subst s
  · rw [observed1 reached]; exact mapped
  · rw [observed2 reached]; exact shape2

#print axioms checkpoint_length_field
#print axioms proof_suffix_field
end AspisR1.S2X
