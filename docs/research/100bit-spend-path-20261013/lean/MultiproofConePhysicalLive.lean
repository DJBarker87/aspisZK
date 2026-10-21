import MultiproofConePhysicalDigest

set_option autoImplicit false
namespace AspisR1.MultiproofConePhysicalLive
open Aeneas Aeneas.Std Result MultiproofConeRef
open MultiproofConePhysicalDigest

abbrev Digest := Array U8 32#usize
abbrev Entry := Nat × Digest

def cell (s : reference.Scratch) (j : Nat) : Entry :=
  (s.idx.val[j]!.val,s.val.val[j]!)

def view (s : reference.Scratch) (start count : Nat) : List Entry :=
  (List.range count).map (fun j => cell s (start+j))

/-- One simultaneous index/digest write on the actual extracted arrays. -/
theorem write_cell (s : reference.Scratch) (w : Usize) (parent : U32)
    (digest : Digest) (cursor : Usize) (wb : w.val<16)
    (j : Nat) (jb : j<16) :
    cell {s with idx:=s.idx.set w parent,val:=s.val.set w digest,«at»:=cursor} j =
      if j=w.val then (parent.val,digest) else cell s j := by
  have ilen : s.idx.val.length=16 := s.idx.property
  have deq := set_digest s w digest wb j jb
  unfold cell
  simp only [deq]
  by_cases eq : j=w.val
  · subst j
    simp [Array.set_val_eq,List.getElem!_eq_getElem?_getD,
      List.getElem?_set_self (by omega : w.val<s.idx.val.length)]
  · simp [Array.set_val_eq,List.getElem!_eq_getElem?_getD,
      List.getElem?_set_ne (Ne.symm eq),eq]

set_option backward.isDefEq.respectTransparency false in
/-- The written parent prefix is extended with the exact observed digest. -/
theorem write_prefix (s : reference.Scratch) (w : Usize) (parent : U32)
    (digest : Digest) (cursor : Usize) (wb : w.val<16) :
    view {s with idx:=s.idx.set w parent,val:=s.val.set w digest,«at»:=cursor} 0 (w.val+1) =
      view s 0 w.val ++ [(parent.val,digest)] := by
  have prefixEq : view {s with idx:=s.idx.set w parent,val:=s.val.set w digest,«at»:=cursor} 0 w.val =
      view s 0 w.val := by
    apply List.map_congr_left
    intro j mem
    have jb := List.mem_range.mp mem
    simpa only [Nat.zero_add] using
      (write_cell s w parent digest cursor wb j (by omega)).trans (if_neg (by omega))
  have lastEq := write_cell s w parent digest cursor wb w.val wb
  simp only [↓reduceIte] at lastEq
  simp only [view,List.range_succ,List.map_append,List.map_cons,List.map_nil,Nat.zero_add]
  simp only [view,Nat.zero_add] at prefixEq
  rw [prefixEq,lastEq]

/-- Safe overwrite preserves every unread child, including its full digest. -/
theorem unread (s : reference.Scratch) (w : Usize) (parent : U32)
    (digest : Digest) (cursor : Usize) (wb : w.val<16)
    (start count : Nat) (safe : w.val<start) (last : start+count≤16) :
    view {s with idx:=s.idx.set w parent,val:=s.val.set w digest,«at»:=cursor} start count =
      view s start count := by
  apply List.map_congr_left
  intro j mem
  have jb := List.mem_range.mp mem
  rw [write_cell s w parent digest cursor wb (start+j) (by omega),if_neg (by omega)]

#print axioms write_cell
#print axioms write_prefix
#print axioms unread
end AspisR1.MultiproofConePhysicalLive
