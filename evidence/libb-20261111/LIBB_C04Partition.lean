import LIBB_ProtocolBytes
import NNC_C04Events
set_option autoImplicit false
namespace LIBB_C04Partition
open Aeneas Aeneas.Std
/-- Recover exactly the physical hashv partition from a C04 source address.
Node and leaf domain tags are disjoint; no query is merged or reordered. -/
def partition (b : RSL.Bytes) : List RSL.Bytes :=
 if b.take 1 = [18] then
  [b.take 1,(b.drop 1).take 32,(b.drop 33).take 32]
 else
  let n := if b.take 2 = [16,113] then 480 else 128
  [b.take 2,(b.drop 2).take n,(b.drop (2+n)).take 32]

theorem node (left right : RSL.Bytes) (hl : left.length = 32) (hr : right.length = 32) :
 partition ([18] ++ left ++ right) = [[18],left,right] := by
 have tl : left.take 32 = left := List.take_of_length_le (by omega)
 have tr : right.take 32 = right := List.take_of_length_le (by omega)
 simp [partition,List.take_append,List.drop_append,hl,hr,tl,tr]

/-- Leaf113 has480 value bytes; leaves241/114 have128. Salt is always32. -/
theorem leaf (tag : UInt8) (n : Nat) (value salt : RSL.Bytes)
 (size : n = if tag = 113 then 480 else 128)
 (hv : value.length = n) (hs : salt.length = 32) :
 partition ([16,tag] ++ value ++ salt) = [[16,tag],value,salt] := by
 by_cases ht : tag = 113
 · have hn : n = 480 := by simpa only [ht,if_true] using size
   have hv' : value.length = 480 := hv.trans hn
   have tv : value.take 480 = value := List.take_of_length_le (by omega)
   have ts : salt.take 32 = salt := List.take_of_length_le (by omega)
   simp [partition,List.take_append,List.drop_append,ht,hv',hs,tv,ts]
 · have hn : n = 128 := by simpa only [ht,if_false] using size
   have hv' : value.length = 128 := hv.trans hn
   have tv : value.take 128 = value := List.take_of_length_le (by omega)
   have ts : salt.take 32 = salt := List.take_of_length_le (by omega)
   simp [partition,List.take_append,List.drop_append,ht,hv',hs,tv,ts]

#print axioms node
#print axioms leaf
end LIBB_C04Partition
