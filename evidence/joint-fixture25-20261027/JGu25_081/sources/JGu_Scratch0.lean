import JGu_Keys
import JGu_LeafIteration0
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGu_Scratch0
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
attribute [local irreducible] JFx_NativeBytes.proof JGu_Keys.keys

def s00 (s : reference.Scratch) : reference.Scratch := {s with n:=0#usize,«at»:=0#usize}
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_LeafPush.push (s00 s) 65593#u32 (encodeState (JGu_LeafIteration0.value ⟨6,by decide⟩)) (by change (0:Nat)<16; decide)

theorem body00 {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (root : Array U8 32#usize) (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof root 0#usize hash 0#usize 10#usize 0#usize (JGu_Keys.keys 0)
      (s00 s).idx (s00 s).val (s00 s).n 0#usize=
        ok (.cont ((s01 s).idx,(s01 s).val,(s01 s).n,1#usize)) := by
  have read := JGu_Keys.stream0 0#usize 0 (by decide) rfl
  have native := JGu_LeafIteration0.source D hash ⟨6,by decide⟩
    0#usize (JGu_Keys.keys 0) root (s00 s) (by decide) (by change (0:Nat)<16; decide) read
  dsimp only [Fin.val_mk,Nat.reduceAdd] at native
  have member : 6 ∈ OraclePortSelectedDraft.batchPositions 0 := by decide
  have decoded : Port4B_NativeLeaf.decodedIndex
      (MultiproofConeSortOrder.packed JGr_Keys.q 0 0 6)=65593#u32 := by
    apply UScalar.eq_of_val_eq
    exact (Port4B_KeyDecode.packed JGr_Keys.q 0 0 6 member 0#usize rfl).1
  have fresh : ¬(0<(s00 s).n.val ∧ (s00 s).idx.val[(s00 s).n.val-1]! = 65593#u32) := by
    intro h
    exact (Nat.lt_irrefl 0) h.1
  rw [decoded,JGk_TX2_LeafPush.step (s00 s) 65593#u32 (encodeState (JGu_LeafIteration0.value ⟨6,by decide⟩)) (by change (0:Nat)<16; decide) fresh] at native
  have advance : Usize.wrapping_add 0#usize 1#usize=1#usize := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment 0#usize (by decide)
  simpa only [bind_tc_ok,Port4B_LeafStep.project,advance,s01] using native
#print axioms body00
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_LeafPush.push (s01 s) 93499#u32 (encodeState (JGu_LeafIteration0.value ⟨0,by decide⟩)) (by change (1:Nat)<16; decide)

theorem body01 {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (root : Array U8 32#usize) (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof root 0#usize hash 0#usize 10#usize 0#usize (JGu_Keys.keys 0)
      (s01 s).idx (s01 s).val (s01 s).n 1#usize=
        ok (.cont ((s02 s).idx,(s02 s).val,(s02 s).n,2#usize)) := by
  have read := JGu_Keys.stream0 1#usize 1 (by decide) rfl
  have native := JGu_LeafIteration0.source D hash ⟨0,by decide⟩
    1#usize (JGu_Keys.keys 0) root (s01 s) (by decide) (by change (1:Nat)<16; decide) read
  dsimp only [Fin.val_mk,Nat.reduceAdd] at native
  have member : 0 ∈ OraclePortSelectedDraft.batchPositions 0 := by decide
  have decoded : Port4B_NativeLeaf.decodedIndex
      (MultiproofConeSortOrder.packed JGr_Keys.q 0 0 0)=93499#u32 := by
    apply UScalar.eq_of_val_eq
    exact (Port4B_KeyDecode.packed JGr_Keys.q 0 0 0 member 0#usize rfl).1
  have fresh : ¬(0<(s01 s).n.val ∧ (s01 s).idx.val[(s01 s).n.val-1]! = 93499#u32) := by
    have last : (s01 s).idx.val[(s01 s).n.val-1]! = 65593#u32 :=
      JGk_TX2_LeafPush.last (s00 s) 65593#u32 (encodeState (JGu_LeafIteration0.value ⟨6,by decide⟩)) (by change (0:Nat)<16; decide)
    intro h
    exact (by decide : 65593#u32≠93499#u32) (last.symm.trans h.2)
  rw [decoded,JGk_TX2_LeafPush.step (s01 s) 93499#u32 (encodeState (JGu_LeafIteration0.value ⟨0,by decide⟩)) (by change (1:Nat)<16; decide) fresh] at native
  have advance : Usize.wrapping_add 1#usize 1#usize=2#usize := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment 1#usize (by decide)
  simpa only [bind_tc_ok,Port4B_LeafStep.project,advance,s02] using native
#print axioms body01
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_LeafPush.push (s02 s) 147529#u32 (encodeState (JGu_LeafIteration0.value ⟨1,by decide⟩)) (by change (2:Nat)<16; decide)

theorem body02 {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (root : Array U8 32#usize) (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof root 0#usize hash 0#usize 10#usize 0#usize (JGu_Keys.keys 0)
      (s02 s).idx (s02 s).val (s02 s).n 2#usize=
        ok (.cont ((s03 s).idx,(s03 s).val,(s03 s).n,3#usize)) := by
  have read := JGu_Keys.stream0 2#usize 2 (by decide) rfl
  have native := JGu_LeafIteration0.source D hash ⟨1,by decide⟩
    2#usize (JGu_Keys.keys 0) root (s02 s) (by decide) (by change (2:Nat)<16; decide) read
  dsimp only [Fin.val_mk,Nat.reduceAdd] at native
  have member : 1 ∈ OraclePortSelectedDraft.batchPositions 0 := by decide
  have decoded : Port4B_NativeLeaf.decodedIndex
      (MultiproofConeSortOrder.packed JGr_Keys.q 0 0 1)=147529#u32 := by
    apply UScalar.eq_of_val_eq
    exact (Port4B_KeyDecode.packed JGr_Keys.q 0 0 1 member 0#usize rfl).1
  have fresh : ¬(0<(s02 s).n.val ∧ (s02 s).idx.val[(s02 s).n.val-1]! = 147529#u32) := by
    have last : (s02 s).idx.val[(s02 s).n.val-1]! = 93499#u32 :=
      JGk_TX2_LeafPush.last (s01 s) 93499#u32 (encodeState (JGu_LeafIteration0.value ⟨0,by decide⟩)) (by change (1:Nat)<16; decide)
    intro h
    exact (by decide : 93499#u32≠147529#u32) (last.symm.trans h.2)
  rw [decoded,JGk_TX2_LeafPush.step (s02 s) 147529#u32 (encodeState (JGu_LeafIteration0.value ⟨1,by decide⟩)) (by change (2:Nat)<16; decide) fresh] at native
  have advance : Usize.wrapping_add 2#usize 1#usize=3#usize := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment 2#usize (by decide)
  simpa only [bind_tc_ok,Port4B_LeafStep.project,advance,s03] using native
#print axioms body02
def s04 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_LeafPush.push (s03 s) 159813#u32 (encodeState (JGu_LeafIteration0.value ⟨9,by decide⟩)) (by change (3:Nat)<16; decide)

theorem body03 {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (root : Array U8 32#usize) (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof root 0#usize hash 0#usize 10#usize 0#usize (JGu_Keys.keys 0)
      (s03 s).idx (s03 s).val (s03 s).n 3#usize=
        ok (.cont ((s04 s).idx,(s04 s).val,(s04 s).n,4#usize)) := by
  have read := JGu_Keys.stream0 3#usize 3 (by decide) rfl
  have native := JGu_LeafIteration0.source D hash ⟨9,by decide⟩
    3#usize (JGu_Keys.keys 0) root (s03 s) (by decide) (by change (3:Nat)<16; decide) read
  dsimp only [Fin.val_mk,Nat.reduceAdd] at native
  have member : 9 ∈ OraclePortSelectedDraft.batchPositions 0 := by decide
  have decoded : Port4B_NativeLeaf.decodedIndex
      (MultiproofConeSortOrder.packed JGr_Keys.q 0 0 9)=159813#u32 := by
    apply UScalar.eq_of_val_eq
    exact (Port4B_KeyDecode.packed JGr_Keys.q 0 0 9 member 0#usize rfl).1
  have fresh : ¬(0<(s03 s).n.val ∧ (s03 s).idx.val[(s03 s).n.val-1]! = 159813#u32) := by
    have last : (s03 s).idx.val[(s03 s).n.val-1]! = 147529#u32 :=
      JGk_TX2_LeafPush.last (s02 s) 147529#u32 (encodeState (JGu_LeafIteration0.value ⟨1,by decide⟩)) (by change (2:Nat)<16; decide)
    intro h
    exact (by decide : 147529#u32≠159813#u32) (last.symm.trans h.2)
  rw [decoded,JGk_TX2_LeafPush.step (s03 s) 159813#u32 (encodeState (JGu_LeafIteration0.value ⟨9,by decide⟩)) (by change (3:Nat)<16; decide) fresh] at native
  have advance : Usize.wrapping_add 3#usize 1#usize=4#usize := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment 3#usize (by decide)
  simpa only [bind_tc_ok,Port4B_LeafStep.project,advance,s04] using native
#print axioms body03
def s05 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_LeafPush.push (s04 s) 183859#u32 (encodeState (JGu_LeafIteration0.value ⟨7,by decide⟩)) (by change (4:Nat)<16; decide)

theorem body04 {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (root : Array U8 32#usize) (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof root 0#usize hash 0#usize 10#usize 0#usize (JGu_Keys.keys 0)
      (s04 s).idx (s04 s).val (s04 s).n 4#usize=
        ok (.cont ((s05 s).idx,(s05 s).val,(s05 s).n,5#usize)) := by
  have read := JGu_Keys.stream0 4#usize 4 (by decide) rfl
  have native := JGu_LeafIteration0.source D hash ⟨7,by decide⟩
    4#usize (JGu_Keys.keys 0) root (s04 s) (by decide) (by change (4:Nat)<16; decide) read
  dsimp only [Fin.val_mk,Nat.reduceAdd] at native
  have member : 7 ∈ OraclePortSelectedDraft.batchPositions 0 := by decide
  have decoded : Port4B_NativeLeaf.decodedIndex
      (MultiproofConeSortOrder.packed JGr_Keys.q 0 0 7)=183859#u32 := by
    apply UScalar.eq_of_val_eq
    exact (Port4B_KeyDecode.packed JGr_Keys.q 0 0 7 member 0#usize rfl).1
  have fresh : ¬(0<(s04 s).n.val ∧ (s04 s).idx.val[(s04 s).n.val-1]! = 183859#u32) := by
    have last : (s04 s).idx.val[(s04 s).n.val-1]! = 159813#u32 :=
      JGk_TX2_LeafPush.last (s03 s) 159813#u32 (encodeState (JGu_LeafIteration0.value ⟨9,by decide⟩)) (by change (3:Nat)<16; decide)
    intro h
    exact (by decide : 159813#u32≠183859#u32) (last.symm.trans h.2)
  rw [decoded,JGk_TX2_LeafPush.step (s04 s) 183859#u32 (encodeState (JGu_LeafIteration0.value ⟨7,by decide⟩)) (by change (4:Nat)<16; decide) fresh] at native
  have advance : Usize.wrapping_add 4#usize 1#usize=5#usize := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment 4#usize (by decide)
  simpa only [bind_tc_ok,Port4B_LeafStep.project,advance,s05] using native
#print axioms body04
def s06 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_LeafPush.push (s05 s) 192317#u32 (encodeState (JGu_LeafIteration0.value ⟨5,by decide⟩)) (by change (5:Nat)<16; decide)

theorem body05 {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (root : Array U8 32#usize) (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof root 0#usize hash 0#usize 10#usize 0#usize (JGu_Keys.keys 0)
      (s05 s).idx (s05 s).val (s05 s).n 5#usize=
        ok (.cont ((s06 s).idx,(s06 s).val,(s06 s).n,6#usize)) := by
  have read := JGu_Keys.stream0 5#usize 5 (by decide) rfl
  have native := JGu_LeafIteration0.source D hash ⟨5,by decide⟩
    5#usize (JGu_Keys.keys 0) root (s05 s) (by decide) (by change (5:Nat)<16; decide) read
  dsimp only [Fin.val_mk,Nat.reduceAdd] at native
  have member : 5 ∈ OraclePortSelectedDraft.batchPositions 0 := by decide
  have decoded : Port4B_NativeLeaf.decodedIndex
      (MultiproofConeSortOrder.packed JGr_Keys.q 0 0 5)=192317#u32 := by
    apply UScalar.eq_of_val_eq
    exact (Port4B_KeyDecode.packed JGr_Keys.q 0 0 5 member 0#usize rfl).1
  have fresh : ¬(0<(s05 s).n.val ∧ (s05 s).idx.val[(s05 s).n.val-1]! = 192317#u32) := by
    have last : (s05 s).idx.val[(s05 s).n.val-1]! = 183859#u32 :=
      JGk_TX2_LeafPush.last (s04 s) 183859#u32 (encodeState (JGu_LeafIteration0.value ⟨7,by decide⟩)) (by change (4:Nat)<16; decide)
    intro h
    exact (by decide : 183859#u32≠192317#u32) (last.symm.trans h.2)
  rw [decoded,JGk_TX2_LeafPush.step (s05 s) 192317#u32 (encodeState (JGu_LeafIteration0.value ⟨5,by decide⟩)) (by change (5:Nat)<16; decide) fresh] at native
  have advance : Usize.wrapping_add 5#usize 1#usize=6#usize := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment 5#usize (by decide)
  simpa only [bind_tc_ok,Port4B_LeafStep.project,advance,s06] using native
#print axioms body05
def s07 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_LeafPush.push (s06 s) 193093#u32 (encodeState (JGu_LeafIteration0.value ⟨8,by decide⟩)) (by change (6:Nat)<16; decide)

theorem body06 {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (root : Array U8 32#usize) (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof root 0#usize hash 0#usize 10#usize 0#usize (JGu_Keys.keys 0)
      (s06 s).idx (s06 s).val (s06 s).n 6#usize=
        ok (.cont ((s07 s).idx,(s07 s).val,(s07 s).n,7#usize)) := by
  have read := JGu_Keys.stream0 6#usize 6 (by decide) rfl
  have native := JGu_LeafIteration0.source D hash ⟨8,by decide⟩
    6#usize (JGu_Keys.keys 0) root (s06 s) (by decide) (by change (6:Nat)<16; decide) read
  dsimp only [Fin.val_mk,Nat.reduceAdd] at native
  have member : 8 ∈ OraclePortSelectedDraft.batchPositions 0 := by decide
  have decoded : Port4B_NativeLeaf.decodedIndex
      (MultiproofConeSortOrder.packed JGr_Keys.q 0 0 8)=193093#u32 := by
    apply UScalar.eq_of_val_eq
    exact (Port4B_KeyDecode.packed JGr_Keys.q 0 0 8 member 0#usize rfl).1
  have fresh : ¬(0<(s06 s).n.val ∧ (s06 s).idx.val[(s06 s).n.val-1]! = 193093#u32) := by
    have last : (s06 s).idx.val[(s06 s).n.val-1]! = 192317#u32 :=
      JGk_TX2_LeafPush.last (s05 s) 192317#u32 (encodeState (JGu_LeafIteration0.value ⟨5,by decide⟩)) (by change (5:Nat)<16; decide)
    intro h
    exact (by decide : 192317#u32≠193093#u32) (last.symm.trans h.2)
  rw [decoded,JGk_TX2_LeafPush.step (s06 s) 193093#u32 (encodeState (JGu_LeafIteration0.value ⟨8,by decide⟩)) (by change (6:Nat)<16; decide) fresh] at native
  have advance : Usize.wrapping_add 6#usize 1#usize=7#usize := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment 6#usize (by decide)
  simpa only [bind_tc_ok,Port4B_LeafStep.project,advance,s07] using native
#print axioms body06
def s08 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_LeafPush.push (s07 s) 209371#u32 (encodeState (JGu_LeafIteration0.value ⟨4,by decide⟩)) (by change (7:Nat)<16; decide)

theorem body07 {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (root : Array U8 32#usize) (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof root 0#usize hash 0#usize 10#usize 0#usize (JGu_Keys.keys 0)
      (s07 s).idx (s07 s).val (s07 s).n 7#usize=
        ok (.cont ((s08 s).idx,(s08 s).val,(s08 s).n,8#usize)) := by
  have read := JGu_Keys.stream0 7#usize 7 (by decide) rfl
  have native := JGu_LeafIteration0.source D hash ⟨4,by decide⟩
    7#usize (JGu_Keys.keys 0) root (s07 s) (by decide) (by change (7:Nat)<16; decide) read
  dsimp only [Fin.val_mk,Nat.reduceAdd] at native
  have member : 4 ∈ OraclePortSelectedDraft.batchPositions 0 := by decide
  have decoded : Port4B_NativeLeaf.decodedIndex
      (MultiproofConeSortOrder.packed JGr_Keys.q 0 0 4)=209371#u32 := by
    apply UScalar.eq_of_val_eq
    exact (Port4B_KeyDecode.packed JGr_Keys.q 0 0 4 member 0#usize rfl).1
  have fresh : ¬(0<(s07 s).n.val ∧ (s07 s).idx.val[(s07 s).n.val-1]! = 209371#u32) := by
    have last : (s07 s).idx.val[(s07 s).n.val-1]! = 193093#u32 :=
      JGk_TX2_LeafPush.last (s06 s) 193093#u32 (encodeState (JGu_LeafIteration0.value ⟨8,by decide⟩)) (by change (6:Nat)<16; decide)
    intro h
    exact (by decide : 193093#u32≠209371#u32) (last.symm.trans h.2)
  rw [decoded,JGk_TX2_LeafPush.step (s07 s) 209371#u32 (encodeState (JGu_LeafIteration0.value ⟨4,by decide⟩)) (by change (7:Nat)<16; decide) fresh] at native
  have advance : Usize.wrapping_add 7#usize 1#usize=8#usize := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment 7#usize (by decide)
  simpa only [bind_tc_ok,Port4B_LeafStep.project,advance,s08] using native
#print axioms body07
def s09 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_LeafPush.push (s08 s) 216823#u32 (encodeState (JGu_LeafIteration0.value ⟨2,by decide⟩)) (by change (8:Nat)<16; decide)

theorem body08 {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (root : Array U8 32#usize) (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof root 0#usize hash 0#usize 10#usize 0#usize (JGu_Keys.keys 0)
      (s08 s).idx (s08 s).val (s08 s).n 8#usize=
        ok (.cont ((s09 s).idx,(s09 s).val,(s09 s).n,9#usize)) := by
  have read := JGu_Keys.stream0 8#usize 8 (by decide) rfl
  have native := JGu_LeafIteration0.source D hash ⟨2,by decide⟩
    8#usize (JGu_Keys.keys 0) root (s08 s) (by decide) (by change (8:Nat)<16; decide) read
  dsimp only [Fin.val_mk,Nat.reduceAdd] at native
  have member : 2 ∈ OraclePortSelectedDraft.batchPositions 0 := by decide
  have decoded : Port4B_NativeLeaf.decodedIndex
      (MultiproofConeSortOrder.packed JGr_Keys.q 0 0 2)=216823#u32 := by
    apply UScalar.eq_of_val_eq
    exact (Port4B_KeyDecode.packed JGr_Keys.q 0 0 2 member 0#usize rfl).1
  have fresh : ¬(0<(s08 s).n.val ∧ (s08 s).idx.val[(s08 s).n.val-1]! = 216823#u32) := by
    have last : (s08 s).idx.val[(s08 s).n.val-1]! = 209371#u32 :=
      JGk_TX2_LeafPush.last (s07 s) 209371#u32 (encodeState (JGu_LeafIteration0.value ⟨4,by decide⟩)) (by change (7:Nat)<16; decide)
    intro h
    exact (by decide : 209371#u32≠216823#u32) (last.symm.trans h.2)
  rw [decoded,JGk_TX2_LeafPush.step (s08 s) 216823#u32 (encodeState (JGu_LeafIteration0.value ⟨2,by decide⟩)) (by change (8:Nat)<16; decide) fresh] at native
  have advance : Usize.wrapping_add 8#usize 1#usize=9#usize := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment 8#usize (by decide)
  simpa only [bind_tc_ok,Port4B_LeafStep.project,advance,s09] using native
#print axioms body08
def s10 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_LeafPush.push (s09 s) 245899#u32 (encodeState (JGu_LeafIteration0.value ⟨3,by decide⟩)) (by change (9:Nat)<16; decide)

theorem body09 {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (root : Array U8 32#usize) (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof root 0#usize hash 0#usize 10#usize 0#usize (JGu_Keys.keys 0)
      (s09 s).idx (s09 s).val (s09 s).n 9#usize=
        ok (.cont ((s10 s).idx,(s10 s).val,(s10 s).n,10#usize)) := by
  have read := JGu_Keys.stream0 9#usize 9 (by decide) rfl
  have native := JGu_LeafIteration0.source D hash ⟨3,by decide⟩
    9#usize (JGu_Keys.keys 0) root (s09 s) (by decide) (by change (9:Nat)<16; decide) read
  dsimp only [Fin.val_mk,Nat.reduceAdd] at native
  have member : 3 ∈ OraclePortSelectedDraft.batchPositions 0 := by decide
  have decoded : Port4B_NativeLeaf.decodedIndex
      (MultiproofConeSortOrder.packed JGr_Keys.q 0 0 3)=245899#u32 := by
    apply UScalar.eq_of_val_eq
    exact (Port4B_KeyDecode.packed JGr_Keys.q 0 0 3 member 0#usize rfl).1
  have fresh : ¬(0<(s09 s).n.val ∧ (s09 s).idx.val[(s09 s).n.val-1]! = 245899#u32) := by
    have last : (s09 s).idx.val[(s09 s).n.val-1]! = 216823#u32 :=
      JGk_TX2_LeafPush.last (s08 s) 216823#u32 (encodeState (JGu_LeafIteration0.value ⟨2,by decide⟩)) (by change (8:Nat)<16; decide)
    intro h
    exact (by decide : 216823#u32≠245899#u32) (last.symm.trans h.2)
  rw [decoded,JGk_TX2_LeafPush.step (s09 s) 245899#u32 (encodeState (JGu_LeafIteration0.value ⟨3,by decide⟩)) (by change (9:Nat)<16; decide) fresh] at native
  have advance : Usize.wrapping_add 9#usize 1#usize=10#usize := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment 9#usize (by decide)
  simpa only [bind_tc_ok,Port4B_LeafStep.project,advance,s10] using native
#print axioms body09
theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (root : Array U8 32#usize) (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof root 0#usize (s00 s).idx (s00 s).val hash 0#usize 10#usize 0#usize
      (JGu_Keys.keys 0) (s00 s).n 0#usize=
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof root 0#usize (s10 s).idx (s10 s).val hash 0#usize 10#usize 0#usize
      (JGu_Keys.keys 0) (s10 s).n 10#usize := by
  exact (JGu_Keys.advance_loop (JGc_TX2_RealLeaves.dictionary D) hash root 0#usize 0#usize 0#usize 1#usize (s00 s) (s01 s) (body00 D hash root s)).trans (
    (JGu_Keys.advance_loop (JGc_TX2_RealLeaves.dictionary D) hash root 0#usize 0#usize 1#usize 2#usize (s01 s) (s02 s) (body01 D hash root s)).trans (
    (JGu_Keys.advance_loop (JGc_TX2_RealLeaves.dictionary D) hash root 0#usize 0#usize 2#usize 3#usize (s02 s) (s03 s) (body02 D hash root s)).trans (
    (JGu_Keys.advance_loop (JGc_TX2_RealLeaves.dictionary D) hash root 0#usize 0#usize 3#usize 4#usize (s03 s) (s04 s) (body03 D hash root s)).trans (
    (JGu_Keys.advance_loop (JGc_TX2_RealLeaves.dictionary D) hash root 0#usize 0#usize 4#usize 5#usize (s04 s) (s05 s) (body04 D hash root s)).trans (
    (JGu_Keys.advance_loop (JGc_TX2_RealLeaves.dictionary D) hash root 0#usize 0#usize 5#usize 6#usize (s05 s) (s06 s) (body05 D hash root s)).trans (
    (JGu_Keys.advance_loop (JGc_TX2_RealLeaves.dictionary D) hash root 0#usize 0#usize 6#usize 7#usize (s06 s) (s07 s) (body06 D hash root s)).trans (
    (JGu_Keys.advance_loop (JGc_TX2_RealLeaves.dictionary D) hash root 0#usize 0#usize 7#usize 8#usize (s07 s) (s08 s) (body07 D hash root s)).trans (
    (JGu_Keys.advance_loop (JGc_TX2_RealLeaves.dictionary D) hash root 0#usize 0#usize 8#usize 9#usize (s08 s) (s09 s) (body08 D hash root s)).trans (
    (JGu_Keys.advance_loop (JGc_TX2_RealLeaves.dictionary D) hash root 0#usize 0#usize 9#usize 10#usize (s09 s) (s10 s) (body09 D hash root s)))))))))))
#print axioms source
end AspisR1.JGu_Scratch0
end
