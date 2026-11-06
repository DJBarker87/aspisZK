import NJP_ScratchCarrier
import NJE_CountArithmetic
import NJA_CountStep

set_option autoImplicit false
noncomputable section
namespace NJP_WriteCarrier
open Aeneas Aeneas.Std Result NJP_RowModel NJP_DigestCarrier NJP_ScratchCarrier NJP_ScalarCarrier
open MultiproofConeRef

theorem small_size (n : Nat) (bound : n ≤ 9216) : (size n).val=n := by
 apply size_value
 have capacity := (9217#usize).hSize
 change 9217 < 2^System.Platform.numBits at capacity
 omega

theorem index_set (a : Array U32 16#usize) (w : Usize) (x : U32)
    (bound : w.val < 16) (k : Fin 16) :
 decodeIndices (a.set w x) k=if k.val=w.val then x.val else decodeIndices a k := by
 have len : a.val.length=16 := a.property
 by_cases same : k.val=w.val
 · simp [decodeIndices,Array.set_val_eq,same]
 · simp [decodeIndices,Array.set_val_eq,same]

theorem value_set (s : reference.Scratch) (w : Usize) (reply : RefDigest)
    (bound : w.val < 16) (k : Fin 16) :
 decodeValues (s.val.set w reply) k=if k.val=w.val then decode reply else decodeValues s.val k := by
 have law := AspisR1.MultiproofConePhysicalDigest.set_digest s w reply bound k.val k.isLt
 have before : s.val.val.length=16 := s.val.property
 have after : (s.val.set w reply).val.length=16 := (s.val.set w reply).property
 rw [getElem!_pos _ _ (by omega),getElem!_pos _ _ (by omega)] at law
 unfold decodeValues
 by_cases same : k.val=w.val
 · simpa only [if_pos same] using congrArg decode law
 · simpa only [if_neg same] using congrArg decode law

theorem complete_write (s : reference.Scratch) (i w cursor : Usize) (parent : U32) (reply : RefDigest)
    (bound : w.val < 16) (parent_value : parent.val=index (raw s) i.val/2) :
 raw {s with idx:=s.idx.set w parent,val:=s.val.set w reply,«at»:=cursor}=
 write (raw s) i.val w.val cursor.val (decode reply) := by
 apply Scratch.ext
 · funext k
   exact (index_set s.idx w parent bound k).trans (by simp only [write,raw,parent_value])
 · funext k
   exact (value_set s w reply bound k).trans (by simp only [write,raw])
 · rfl
 · rfl

#print small_size
#print axioms small_size
#print index_set
#print axioms index_set
#print value_set
#print axioms value_set
#print complete_write
#print axioms complete_write
end NJP_WriteCarrier
end
