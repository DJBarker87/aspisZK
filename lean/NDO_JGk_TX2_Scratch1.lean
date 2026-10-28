import NDO_JGk_TX2_ScratchKeys
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGk_TX2_Scratch1
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
attribute [local irreducible] JFx_NativeBytes.proof JGk_TX2_ScratchKeys.keys JGk_TX2_NativeLeaves.value0 JGk_TX2_NativeLeaves.value1 JGc_TX2_RealLeaves.value

def s00 (s : reference.Scratch) : reference.Scratch := {s with n:=0#usize,«at»:=0#usize}
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_LeafPush.push (s00 s) 14297#u32 (encodeState (JGk_TX2_NativeLeaves.value1 ⟨11,by decide⟩)) (by change (0:Nat)<16; decide)

theorem body00 {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (root : Array U8 32#usize) (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof root 1#usize hash 10#usize 12#usize 4#usize (JGk_TX2_ScratchKeys.keys 1)
      (s00 s).idx (s00 s).val (s00 s).n 0#usize=
        ok (.cont ((s01 s).idx,(s01 s).val,(s01 s).n,1#usize)) := by
  have read := JGk_TX2_ScratchKeys.stream1 0#usize 0 (by decide) rfl
  have native := JGk_TX2_LeafIteration.source1 D hash ⟨11,by decide⟩
    0#usize (JGk_TX2_ScratchKeys.keys 1) root (s00 s) (by decide) (by change (0:Nat)<16; decide) read
  dsimp only [Fin.val_mk,Nat.reduceAdd] at native
  have member : 21 ∈ OraclePortSelectedDraft.batchPositions 1 := by decide
  have decoded : Port4B_NativeLeaf.decodedIndex
      (MultiproofConeSortOrder.packed JGk_TX2_FrontierOrder.q 1 1 21)=14297#u32 := by
    apply UScalar.eq_of_val_eq
    exact (Port4B_KeyDecode.packed JGk_TX2_FrontierOrder.q 1 1 21 member 10#usize rfl).1
  have fresh : ¬(0<(s00 s).n.val ∧ (s00 s).idx.val[(s00 s).n.val-1]! = 14297#u32) := by
    intro h
    exact (Nat.lt_irrefl 0) h.1
  rw [decoded,JGk_TX2_LeafPush.step (s00 s) 14297#u32 (encodeState (JGk_TX2_NativeLeaves.value1 ⟨11,by decide⟩)) (by change (0:Nat)<16; decide) fresh] at native
  have advance : Usize.wrapping_add 0#usize 1#usize=1#usize := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment 0#usize (by decide)
  simpa only [bind_tc_ok,Port4B_LeafStep.project,advance,s01] using native
#print axioms body00
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_LeafPush.push (s01 s) 21248#u32 (encodeState (JGk_TX2_NativeLeaves.value1 ⟨7,by decide⟩)) (by change (1:Nat)<16; decide)

theorem body01 {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (root : Array U8 32#usize) (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof root 1#usize hash 10#usize 12#usize 4#usize (JGk_TX2_ScratchKeys.keys 1)
      (s01 s).idx (s01 s).val (s01 s).n 1#usize=
        ok (.cont ((s02 s).idx,(s02 s).val,(s02 s).n,2#usize)) := by
  have read := JGk_TX2_ScratchKeys.stream1 1#usize 1 (by decide) rfl
  have native := JGk_TX2_LeafIteration.source1 D hash ⟨7,by decide⟩
    1#usize (JGk_TX2_ScratchKeys.keys 1) root (s01 s) (by decide) (by change (1:Nat)<16; decide) read
  dsimp only [Fin.val_mk,Nat.reduceAdd] at native
  have member : 17 ∈ OraclePortSelectedDraft.batchPositions 1 := by decide
  have decoded : Port4B_NativeLeaf.decodedIndex
      (MultiproofConeSortOrder.packed JGk_TX2_FrontierOrder.q 1 1 17)=21248#u32 := by
    apply UScalar.eq_of_val_eq
    exact (Port4B_KeyDecode.packed JGk_TX2_FrontierOrder.q 1 1 17 member 10#usize rfl).1
  have fresh : ¬(0<(s01 s).n.val ∧ (s01 s).idx.val[(s01 s).n.val-1]! = 21248#u32) := by
    have last : (s01 s).idx.val[(s01 s).n.val-1]! = 14297#u32 :=
      JGk_TX2_LeafPush.last (s00 s) 14297#u32 (encodeState (JGk_TX2_NativeLeaves.value1 ⟨11,by decide⟩)) (by change (0:Nat)<16; decide)
    intro h
    exact (by decide : 14297#u32≠21248#u32) (last.symm.trans h.2)
  rw [decoded,JGk_TX2_LeafPush.step (s01 s) 21248#u32 (encodeState (JGk_TX2_NativeLeaves.value1 ⟨7,by decide⟩)) (by change (1:Nat)<16; decide) fresh] at native
  have advance : Usize.wrapping_add 1#usize 1#usize=2#usize := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment 1#usize (by decide)
  simpa only [bind_tc_ok,Port4B_LeafStep.project,advance,s02] using native
#print axioms body01
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_LeafPush.push (s02 s) 42158#u32 (encodeState (JGk_TX2_NativeLeaves.value1 ⟨5,by decide⟩)) (by change (2:Nat)<16; decide)

theorem body02 {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (root : Array U8 32#usize) (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof root 1#usize hash 10#usize 12#usize 4#usize (JGk_TX2_ScratchKeys.keys 1)
      (s02 s).idx (s02 s).val (s02 s).n 2#usize=
        ok (.cont ((s03 s).idx,(s03 s).val,(s03 s).n,3#usize)) := by
  have read := JGk_TX2_ScratchKeys.stream1 2#usize 2 (by decide) rfl
  have native := JGk_TX2_LeafIteration.source1 D hash ⟨5,by decide⟩
    2#usize (JGk_TX2_ScratchKeys.keys 1) root (s02 s) (by decide) (by change (2:Nat)<16; decide) read
  dsimp only [Fin.val_mk,Nat.reduceAdd] at native
  have member : 15 ∈ OraclePortSelectedDraft.batchPositions 1 := by decide
  have decoded : Port4B_NativeLeaf.decodedIndex
      (MultiproofConeSortOrder.packed JGk_TX2_FrontierOrder.q 1 1 15)=42158#u32 := by
    apply UScalar.eq_of_val_eq
    exact (Port4B_KeyDecode.packed JGk_TX2_FrontierOrder.q 1 1 15 member 10#usize rfl).1
  have fresh : ¬(0<(s02 s).n.val ∧ (s02 s).idx.val[(s02 s).n.val-1]! = 42158#u32) := by
    have last : (s02 s).idx.val[(s02 s).n.val-1]! = 21248#u32 :=
      JGk_TX2_LeafPush.last (s01 s) 21248#u32 (encodeState (JGk_TX2_NativeLeaves.value1 ⟨7,by decide⟩)) (by change (1:Nat)<16; decide)
    intro h
    exact (by decide : 21248#u32≠42158#u32) (last.symm.trans h.2)
  rw [decoded,JGk_TX2_LeafPush.step (s02 s) 42158#u32 (encodeState (JGk_TX2_NativeLeaves.value1 ⟨5,by decide⟩)) (by change (2:Nat)<16; decide) fresh] at native
  have advance : Usize.wrapping_add 2#usize 1#usize=3#usize := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment 2#usize (by decide)
  simpa only [bind_tc_ok,Port4B_LeafStep.project,advance,s03] using native
#print axioms body02
def s04 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_LeafPush.push (s03 s) 55377#u32 (encodeState (JGk_TX2_NativeLeaves.value1 ⟨9,by decide⟩)) (by change (3:Nat)<16; decide)

theorem body03 {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (root : Array U8 32#usize) (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof root 1#usize hash 10#usize 12#usize 4#usize (JGk_TX2_ScratchKeys.keys 1)
      (s03 s).idx (s03 s).val (s03 s).n 3#usize=
        ok (.cont ((s04 s).idx,(s04 s).val,(s04 s).n,4#usize)) := by
  have read := JGk_TX2_ScratchKeys.stream1 3#usize 3 (by decide) rfl
  have native := JGk_TX2_LeafIteration.source1 D hash ⟨9,by decide⟩
    3#usize (JGk_TX2_ScratchKeys.keys 1) root (s03 s) (by decide) (by change (3:Nat)<16; decide) read
  dsimp only [Fin.val_mk,Nat.reduceAdd] at native
  have member : 19 ∈ OraclePortSelectedDraft.batchPositions 1 := by decide
  have decoded : Port4B_NativeLeaf.decodedIndex
      (MultiproofConeSortOrder.packed JGk_TX2_FrontierOrder.q 1 1 19)=55377#u32 := by
    apply UScalar.eq_of_val_eq
    exact (Port4B_KeyDecode.packed JGk_TX2_FrontierOrder.q 1 1 19 member 10#usize rfl).1
  have fresh : ¬(0<(s03 s).n.val ∧ (s03 s).idx.val[(s03 s).n.val-1]! = 55377#u32) := by
    have last : (s03 s).idx.val[(s03 s).n.val-1]! = 42158#u32 :=
      JGk_TX2_LeafPush.last (s02 s) 42158#u32 (encodeState (JGk_TX2_NativeLeaves.value1 ⟨5,by decide⟩)) (by change (2:Nat)<16; decide)
    intro h
    exact (by decide : 42158#u32≠55377#u32) (last.symm.trans h.2)
  rw [decoded,JGk_TX2_LeafPush.step (s03 s) 55377#u32 (encodeState (JGk_TX2_NativeLeaves.value1 ⟨9,by decide⟩)) (by change (3:Nat)<16; decide) fresh] at native
  have advance : Usize.wrapping_add 3#usize 1#usize=4#usize := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment 3#usize (by decide)
  simpa only [bind_tc_ok,Port4B_LeafStep.project,advance,s04] using native
#print axioms body03
def s05 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_LeafPush.push (s04 s) 63860#u32 (encodeState (JGk_TX2_NativeLeaves.value1 ⟨8,by decide⟩)) (by change (4:Nat)<16; decide)

theorem body04 {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (root : Array U8 32#usize) (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof root 1#usize hash 10#usize 12#usize 4#usize (JGk_TX2_ScratchKeys.keys 1)
      (s04 s).idx (s04 s).val (s04 s).n 4#usize=
        ok (.cont ((s05 s).idx,(s05 s).val,(s05 s).n,5#usize)) := by
  have read := JGk_TX2_ScratchKeys.stream1 4#usize 4 (by decide) rfl
  have native := JGk_TX2_LeafIteration.source1 D hash ⟨8,by decide⟩
    4#usize (JGk_TX2_ScratchKeys.keys 1) root (s04 s) (by decide) (by change (4:Nat)<16; decide) read
  dsimp only [Fin.val_mk,Nat.reduceAdd] at native
  have member : 18 ∈ OraclePortSelectedDraft.batchPositions 1 := by decide
  have decoded : Port4B_NativeLeaf.decodedIndex
      (MultiproofConeSortOrder.packed JGk_TX2_FrontierOrder.q 1 1 18)=63860#u32 := by
    apply UScalar.eq_of_val_eq
    exact (Port4B_KeyDecode.packed JGk_TX2_FrontierOrder.q 1 1 18 member 10#usize rfl).1
  have fresh : ¬(0<(s04 s).n.val ∧ (s04 s).idx.val[(s04 s).n.val-1]! = 63860#u32) := by
    have last : (s04 s).idx.val[(s04 s).n.val-1]! = 55377#u32 :=
      JGk_TX2_LeafPush.last (s03 s) 55377#u32 (encodeState (JGk_TX2_NativeLeaves.value1 ⟨9,by decide⟩)) (by change (3:Nat)<16; decide)
    intro h
    exact (by decide : 55377#u32≠63860#u32) (last.symm.trans h.2)
  rw [decoded,JGk_TX2_LeafPush.step (s04 s) 63860#u32 (encodeState (JGk_TX2_NativeLeaves.value1 ⟨8,by decide⟩)) (by change (4:Nat)<16; decide) fresh] at native
  have advance : Usize.wrapping_add 4#usize 1#usize=5#usize := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment 4#usize (by decide)
  simpa only [bind_tc_ok,Port4B_LeafStep.project,advance,s05] using native
#print axioms body04
def s06 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_LeafPush.push (s05 s) 132355#u32 (encodeState (JGk_TX2_NativeLeaves.value1 ⟨0,by decide⟩)) (by change (5:Nat)<16; decide)

theorem body05 {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (root : Array U8 32#usize) (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof root 1#usize hash 10#usize 12#usize 4#usize (JGk_TX2_ScratchKeys.keys 1)
      (s05 s).idx (s05 s).val (s05 s).n 5#usize=
        ok (.cont ((s06 s).idx,(s06 s).val,(s06 s).n,6#usize)) := by
  have read := JGk_TX2_ScratchKeys.stream1 5#usize 5 (by decide) rfl
  have native := JGk_TX2_LeafIteration.source1 D hash ⟨0,by decide⟩
    5#usize (JGk_TX2_ScratchKeys.keys 1) root (s05 s) (by decide) (by change (5:Nat)<16; decide) read
  dsimp only [Fin.val_mk,Nat.reduceAdd] at native
  have member : 10 ∈ OraclePortSelectedDraft.batchPositions 1 := by decide
  have decoded : Port4B_NativeLeaf.decodedIndex
      (MultiproofConeSortOrder.packed JGk_TX2_FrontierOrder.q 1 1 10)=132355#u32 := by
    apply UScalar.eq_of_val_eq
    exact (Port4B_KeyDecode.packed JGk_TX2_FrontierOrder.q 1 1 10 member 10#usize rfl).1
  have fresh : ¬(0<(s05 s).n.val ∧ (s05 s).idx.val[(s05 s).n.val-1]! = 132355#u32) := by
    have last : (s05 s).idx.val[(s05 s).n.val-1]! = 63860#u32 :=
      JGk_TX2_LeafPush.last (s04 s) 63860#u32 (encodeState (JGk_TX2_NativeLeaves.value1 ⟨8,by decide⟩)) (by change (4:Nat)<16; decide)
    intro h
    exact (by decide : 63860#u32≠132355#u32) (last.symm.trans h.2)
  rw [decoded,JGk_TX2_LeafPush.step (s05 s) 132355#u32 (encodeState (JGk_TX2_NativeLeaves.value1 ⟨0,by decide⟩)) (by change (5:Nat)<16; decide) fresh] at native
  have advance : Usize.wrapping_add 5#usize 1#usize=6#usize := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment 5#usize (by decide)
  simpa only [bind_tc_ok,Port4B_LeafStep.project,advance,s06] using native
#print axioms body05
def s07 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_LeafPush.push (s06 s) 149624#u32 (encodeState (JGk_TX2_NativeLeaves.value1 ⟨3,by decide⟩)) (by change (6:Nat)<16; decide)

theorem body06 {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (root : Array U8 32#usize) (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof root 1#usize hash 10#usize 12#usize 4#usize (JGk_TX2_ScratchKeys.keys 1)
      (s06 s).idx (s06 s).val (s06 s).n 6#usize=
        ok (.cont ((s07 s).idx,(s07 s).val,(s07 s).n,7#usize)) := by
  have read := JGk_TX2_ScratchKeys.stream1 6#usize 6 (by decide) rfl
  have native := JGk_TX2_LeafIteration.source1 D hash ⟨3,by decide⟩
    6#usize (JGk_TX2_ScratchKeys.keys 1) root (s06 s) (by decide) (by change (6:Nat)<16; decide) read
  dsimp only [Fin.val_mk,Nat.reduceAdd] at native
  have member : 13 ∈ OraclePortSelectedDraft.batchPositions 1 := by decide
  have decoded : Port4B_NativeLeaf.decodedIndex
      (MultiproofConeSortOrder.packed JGk_TX2_FrontierOrder.q 1 1 13)=149624#u32 := by
    apply UScalar.eq_of_val_eq
    exact (Port4B_KeyDecode.packed JGk_TX2_FrontierOrder.q 1 1 13 member 10#usize rfl).1
  have fresh : ¬(0<(s06 s).n.val ∧ (s06 s).idx.val[(s06 s).n.val-1]! = 149624#u32) := by
    have last : (s06 s).idx.val[(s06 s).n.val-1]! = 132355#u32 :=
      JGk_TX2_LeafPush.last (s05 s) 132355#u32 (encodeState (JGk_TX2_NativeLeaves.value1 ⟨0,by decide⟩)) (by change (5:Nat)<16; decide)
    intro h
    exact (by decide : 132355#u32≠149624#u32) (last.symm.trans h.2)
  rw [decoded,JGk_TX2_LeafPush.step (s06 s) 149624#u32 (encodeState (JGk_TX2_NativeLeaves.value1 ⟨3,by decide⟩)) (by change (6:Nat)<16; decide) fresh] at native
  have advance : Usize.wrapping_add 6#usize 1#usize=7#usize := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment 6#usize (by decide)
  simpa only [bind_tc_ok,Port4B_LeafStep.project,advance,s07] using native
#print axioms body06
def s08 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_LeafPush.push (s07 s) 166165#u32 (encodeState (JGk_TX2_NativeLeaves.value1 ⟨4,by decide⟩)) (by change (7:Nat)<16; decide)

theorem body07 {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (root : Array U8 32#usize) (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof root 1#usize hash 10#usize 12#usize 4#usize (JGk_TX2_ScratchKeys.keys 1)
      (s07 s).idx (s07 s).val (s07 s).n 7#usize=
        ok (.cont ((s08 s).idx,(s08 s).val,(s08 s).n,8#usize)) := by
  have read := JGk_TX2_ScratchKeys.stream1 7#usize 7 (by decide) rfl
  have native := JGk_TX2_LeafIteration.source1 D hash ⟨4,by decide⟩
    7#usize (JGk_TX2_ScratchKeys.keys 1) root (s07 s) (by decide) (by change (7:Nat)<16; decide) read
  dsimp only [Fin.val_mk,Nat.reduceAdd] at native
  have member : 14 ∈ OraclePortSelectedDraft.batchPositions 1 := by decide
  have decoded : Port4B_NativeLeaf.decodedIndex
      (MultiproofConeSortOrder.packed JGk_TX2_FrontierOrder.q 1 1 14)=166165#u32 := by
    apply UScalar.eq_of_val_eq
    exact (Port4B_KeyDecode.packed JGk_TX2_FrontierOrder.q 1 1 14 member 10#usize rfl).1
  have fresh : ¬(0<(s07 s).n.val ∧ (s07 s).idx.val[(s07 s).n.val-1]! = 166165#u32) := by
    have last : (s07 s).idx.val[(s07 s).n.val-1]! = 149624#u32 :=
      JGk_TX2_LeafPush.last (s06 s) 149624#u32 (encodeState (JGk_TX2_NativeLeaves.value1 ⟨3,by decide⟩)) (by change (6:Nat)<16; decide)
    intro h
    exact (by decide : 149624#u32≠166165#u32) (last.symm.trans h.2)
  rw [decoded,JGk_TX2_LeafPush.step (s07 s) 166165#u32 (encodeState (JGk_TX2_NativeLeaves.value1 ⟨4,by decide⟩)) (by change (7:Nat)<16; decide) fresh] at native
  have advance : Usize.wrapping_add 7#usize 1#usize=8#usize := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment 7#usize (by decide)
  simpa only [bind_tc_ok,Port4B_LeafStep.project,advance,s08] using native
#print axioms body07
def s09 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_LeafPush.push (s08 s) 178080#u32 (encodeState (JGk_TX2_NativeLeaves.value1 ⟨2,by decide⟩)) (by change (8:Nat)<16; decide)

theorem body08 {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (root : Array U8 32#usize) (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof root 1#usize hash 10#usize 12#usize 4#usize (JGk_TX2_ScratchKeys.keys 1)
      (s08 s).idx (s08 s).val (s08 s).n 8#usize=
        ok (.cont ((s09 s).idx,(s09 s).val,(s09 s).n,9#usize)) := by
  have read := JGk_TX2_ScratchKeys.stream1 8#usize 8 (by decide) rfl
  have native := JGk_TX2_LeafIteration.source1 D hash ⟨2,by decide⟩
    8#usize (JGk_TX2_ScratchKeys.keys 1) root (s08 s) (by decide) (by change (8:Nat)<16; decide) read
  dsimp only [Fin.val_mk,Nat.reduceAdd] at native
  have member : 12 ∈ OraclePortSelectedDraft.batchPositions 1 := by decide
  have decoded : Port4B_NativeLeaf.decodedIndex
      (MultiproofConeSortOrder.packed JGk_TX2_FrontierOrder.q 1 1 12)=178080#u32 := by
    apply UScalar.eq_of_val_eq
    exact (Port4B_KeyDecode.packed JGk_TX2_FrontierOrder.q 1 1 12 member 10#usize rfl).1
  have fresh : ¬(0<(s08 s).n.val ∧ (s08 s).idx.val[(s08 s).n.val-1]! = 178080#u32) := by
    have last : (s08 s).idx.val[(s08 s).n.val-1]! = 166165#u32 :=
      JGk_TX2_LeafPush.last (s07 s) 166165#u32 (encodeState (JGk_TX2_NativeLeaves.value1 ⟨4,by decide⟩)) (by change (7:Nat)<16; decide)
    intro h
    exact (by decide : 166165#u32≠178080#u32) (last.symm.trans h.2)
  rw [decoded,JGk_TX2_LeafPush.step (s08 s) 178080#u32 (encodeState (JGk_TX2_NativeLeaves.value1 ⟨2,by decide⟩)) (by change (8:Nat)<16; decide) fresh] at native
  have advance : Usize.wrapping_add 8#usize 1#usize=9#usize := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment 8#usize (by decide)
  simpa only [bind_tc_ok,Port4B_LeafStep.project,advance,s09] using native
#print axioms body08
def s10 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_LeafPush.push (s09 s) 179622#u32 (encodeState (JGk_TX2_NativeLeaves.value1 ⟨6,by decide⟩)) (by change (9:Nat)<16; decide)

theorem body09 {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (root : Array U8 32#usize) (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof root 1#usize hash 10#usize 12#usize 4#usize (JGk_TX2_ScratchKeys.keys 1)
      (s09 s).idx (s09 s).val (s09 s).n 9#usize=
        ok (.cont ((s10 s).idx,(s10 s).val,(s10 s).n,10#usize)) := by
  have read := JGk_TX2_ScratchKeys.stream1 9#usize 9 (by decide) rfl
  have native := JGk_TX2_LeafIteration.source1 D hash ⟨6,by decide⟩
    9#usize (JGk_TX2_ScratchKeys.keys 1) root (s09 s) (by decide) (by change (9:Nat)<16; decide) read
  dsimp only [Fin.val_mk,Nat.reduceAdd] at native
  have member : 16 ∈ OraclePortSelectedDraft.batchPositions 1 := by decide
  have decoded : Port4B_NativeLeaf.decodedIndex
      (MultiproofConeSortOrder.packed JGk_TX2_FrontierOrder.q 1 1 16)=179622#u32 := by
    apply UScalar.eq_of_val_eq
    exact (Port4B_KeyDecode.packed JGk_TX2_FrontierOrder.q 1 1 16 member 10#usize rfl).1
  have fresh : ¬(0<(s09 s).n.val ∧ (s09 s).idx.val[(s09 s).n.val-1]! = 179622#u32) := by
    have last : (s09 s).idx.val[(s09 s).n.val-1]! = 178080#u32 :=
      JGk_TX2_LeafPush.last (s08 s) 178080#u32 (encodeState (JGk_TX2_NativeLeaves.value1 ⟨2,by decide⟩)) (by change (8:Nat)<16; decide)
    intro h
    exact (by decide : 178080#u32≠179622#u32) (last.symm.trans h.2)
  rw [decoded,JGk_TX2_LeafPush.step (s09 s) 179622#u32 (encodeState (JGk_TX2_NativeLeaves.value1 ⟨6,by decide⟩)) (by change (9:Nat)<16; decide) fresh] at native
  have advance : Usize.wrapping_add 9#usize 1#usize=10#usize := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment 9#usize (by decide)
  simpa only [bind_tc_ok,Port4B_LeafStep.project,advance,s10] using native
#print axioms body09
def s11 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_LeafPush.push (s10 s) 185637#u32 (encodeState (JGk_TX2_NativeLeaves.value1 ⟨10,by decide⟩)) (by change (10:Nat)<16; decide)

theorem body10 {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (root : Array U8 32#usize) (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof root 1#usize hash 10#usize 12#usize 4#usize (JGk_TX2_ScratchKeys.keys 1)
      (s10 s).idx (s10 s).val (s10 s).n 10#usize=
        ok (.cont ((s11 s).idx,(s11 s).val,(s11 s).n,11#usize)) := by
  have read := JGk_TX2_ScratchKeys.stream1 10#usize 10 (by decide) rfl
  have native := JGk_TX2_LeafIteration.source1 D hash ⟨10,by decide⟩
    10#usize (JGk_TX2_ScratchKeys.keys 1) root (s10 s) (by decide) (by change (10:Nat)<16; decide) read
  dsimp only [Fin.val_mk,Nat.reduceAdd] at native
  have member : 20 ∈ OraclePortSelectedDraft.batchPositions 1 := by decide
  have decoded : Port4B_NativeLeaf.decodedIndex
      (MultiproofConeSortOrder.packed JGk_TX2_FrontierOrder.q 1 1 20)=185637#u32 := by
    apply UScalar.eq_of_val_eq
    exact (Port4B_KeyDecode.packed JGk_TX2_FrontierOrder.q 1 1 20 member 10#usize rfl).1
  have fresh : ¬(0<(s10 s).n.val ∧ (s10 s).idx.val[(s10 s).n.val-1]! = 185637#u32) := by
    have last : (s10 s).idx.val[(s10 s).n.val-1]! = 179622#u32 :=
      JGk_TX2_LeafPush.last (s09 s) 179622#u32 (encodeState (JGk_TX2_NativeLeaves.value1 ⟨6,by decide⟩)) (by change (9:Nat)<16; decide)
    intro h
    exact (by decide : 179622#u32≠185637#u32) (last.symm.trans h.2)
  rw [decoded,JGk_TX2_LeafPush.step (s10 s) 185637#u32 (encodeState (JGk_TX2_NativeLeaves.value1 ⟨10,by decide⟩)) (by change (10:Nat)<16; decide) fresh] at native
  have advance : Usize.wrapping_add 10#usize 1#usize=11#usize := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment 10#usize (by decide)
  simpa only [bind_tc_ok,Port4B_LeafStep.project,advance,s11] using native
#print axioms body10
def s12 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_LeafPush.push (s11 s) 218094#u32 (encodeState (JGk_TX2_NativeLeaves.value1 ⟨1,by decide⟩)) (by change (11:Nat)<16; decide)

theorem body11 {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (root : Array U8 32#usize) (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof root 1#usize hash 10#usize 12#usize 4#usize (JGk_TX2_ScratchKeys.keys 1)
      (s11 s).idx (s11 s).val (s11 s).n 11#usize=
        ok (.cont ((s12 s).idx,(s12 s).val,(s12 s).n,12#usize)) := by
  have read := JGk_TX2_ScratchKeys.stream1 11#usize 11 (by decide) rfl
  have native := JGk_TX2_LeafIteration.source1 D hash ⟨1,by decide⟩
    11#usize (JGk_TX2_ScratchKeys.keys 1) root (s11 s) (by decide) (by change (11:Nat)<16; decide) read
  dsimp only [Fin.val_mk,Nat.reduceAdd] at native
  have member : 11 ∈ OraclePortSelectedDraft.batchPositions 1 := by decide
  have decoded : Port4B_NativeLeaf.decodedIndex
      (MultiproofConeSortOrder.packed JGk_TX2_FrontierOrder.q 1 1 11)=218094#u32 := by
    apply UScalar.eq_of_val_eq
    exact (Port4B_KeyDecode.packed JGk_TX2_FrontierOrder.q 1 1 11 member 10#usize rfl).1
  have fresh : ¬(0<(s11 s).n.val ∧ (s11 s).idx.val[(s11 s).n.val-1]! = 218094#u32) := by
    have last : (s11 s).idx.val[(s11 s).n.val-1]! = 185637#u32 :=
      JGk_TX2_LeafPush.last (s10 s) 185637#u32 (encodeState (JGk_TX2_NativeLeaves.value1 ⟨10,by decide⟩)) (by change (10:Nat)<16; decide)
    intro h
    exact (by decide : 185637#u32≠218094#u32) (last.symm.trans h.2)
  rw [decoded,JGk_TX2_LeafPush.step (s11 s) 218094#u32 (encodeState (JGk_TX2_NativeLeaves.value1 ⟨1,by decide⟩)) (by change (11:Nat)<16; decide) fresh] at native
  have advance : Usize.wrapping_add 11#usize 1#usize=12#usize := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment 11#usize (by decide)
  simpa only [bind_tc_ok,Port4B_LeafStep.project,advance,s12] using native
#print axioms body11
theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (root : Array U8 32#usize) (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof root 1#usize (s00 s).idx (s00 s).val hash 10#usize 12#usize 4#usize
      (JGk_TX2_ScratchKeys.keys 1) (s00 s).n 0#usize=
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof root 1#usize (s12 s).idx (s12 s).val hash 10#usize 12#usize 4#usize
      (JGk_TX2_ScratchKeys.keys 1) (s12 s).n 12#usize := by
  exact (JGk_TX2_ScratchKeys.advance_loop D hash root 1#usize 4#usize 0#usize 1#usize (s00 s) (s01 s) (body00 D hash root s)).trans (
    (JGk_TX2_ScratchKeys.advance_loop D hash root 1#usize 4#usize 1#usize 2#usize (s01 s) (s02 s) (body01 D hash root s)).trans (
    (JGk_TX2_ScratchKeys.advance_loop D hash root 1#usize 4#usize 2#usize 3#usize (s02 s) (s03 s) (body02 D hash root s)).trans (
    (JGk_TX2_ScratchKeys.advance_loop D hash root 1#usize 4#usize 3#usize 4#usize (s03 s) (s04 s) (body03 D hash root s)).trans (
    (JGk_TX2_ScratchKeys.advance_loop D hash root 1#usize 4#usize 4#usize 5#usize (s04 s) (s05 s) (body04 D hash root s)).trans (
    (JGk_TX2_ScratchKeys.advance_loop D hash root 1#usize 4#usize 5#usize 6#usize (s05 s) (s06 s) (body05 D hash root s)).trans (
    (JGk_TX2_ScratchKeys.advance_loop D hash root 1#usize 4#usize 6#usize 7#usize (s06 s) (s07 s) (body06 D hash root s)).trans (
    (JGk_TX2_ScratchKeys.advance_loop D hash root 1#usize 4#usize 7#usize 8#usize (s07 s) (s08 s) (body07 D hash root s)).trans (
    (JGk_TX2_ScratchKeys.advance_loop D hash root 1#usize 4#usize 8#usize 9#usize (s08 s) (s09 s) (body08 D hash root s)).trans (
    (JGk_TX2_ScratchKeys.advance_loop D hash root 1#usize 4#usize 9#usize 10#usize (s09 s) (s10 s) (body09 D hash root s)).trans (
    (JGk_TX2_ScratchKeys.advance_loop D hash root 1#usize 4#usize 10#usize 11#usize (s10 s) (s11 s) (body10 D hash root s)).trans (
    (JGk_TX2_ScratchKeys.advance_loop D hash root 1#usize 4#usize 11#usize 12#usize (s11 s) (s12 s) (body11 D hash root s)))))))))))))
#print axioms source
end AspisR1.JGk_TX2_Scratch1
end
