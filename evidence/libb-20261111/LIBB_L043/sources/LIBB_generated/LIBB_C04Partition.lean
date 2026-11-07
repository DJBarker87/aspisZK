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
 simp only [partition,List.take_append,List.take_cons,List.take_nil,List.take_zero,
  List.length_cons,List.length_nil,Nat.sub_self,List.nil_append,List.append_nil,
  if_true,List.drop_append,List.drop_cons,List.drop_zero]
 simp only [hl,hr,List.take_of_length_le (by omega : left.length ≤ 32),
   List.take_of_length_le (by omega : right.length ≤ 32)]
 simp [hl,hr,List.take_append,List.drop_append]

/-- Leaf113 has480 value bytes; leaves241/114 have128. Salt is always32. -/
theorem leaf (tag : UInt8) (n : Nat) (value salt : RSL.Bytes)
 (size : n = if tag = 113 then 480 else 128)
 (hv : value.length = n) (hs : salt.length = 32) :
 partition ([16,tag] ++ value ++ salt) = [[16,tag],value,salt] := by
 subst n
 simp [partition,List.take_append,List.drop_append,hv,hs]
#print axioms node
#print axioms leaf
end LIBB_C04Partition
