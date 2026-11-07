import LIBB_C04Partition
set_option autoImplicit false
namespace LIBB_C04PartialPartition
/-- Truncated source slices still have a unique split: salt cannot begin
until the complete preceding value window has been reached. -/
theorem recover (n : Nat) (value salt : RSL.Bytes)
 (hv : value.length ≤ n) (hs : salt.length ≤ 32)
 (full : salt ≠ [] → value.length = n) :
 [(value ++ salt).take n,((value ++ salt).drop n).take 32] = [value,salt] := by
 have tv : value.take n = value := List.take_of_length_le hv
 have dv : value.drop n = [] := List.drop_eq_nil_of_le hv
 have ts : salt.take 32 = salt := List.take_of_length_le hs
 by_cases he : salt = []
 · simp only [he,List.append_nil,tv,dv,List.take_nil]
 · have hn := full he
   simp only [List.take_append,List.drop_append,hn,Nat.sub_self,List.take_zero,
     List.drop_zero,List.append_nil,List.nil_append,tv,dv,ts]

theorem leaf (tag : UInt8) (n : Nat) (value salt : RSL.Bytes)
 (size : n = if tag = 113 then 480 else 128)
 (hv : value.length ≤ n) (hs : salt.length ≤ 32)
 (full : salt ≠ [] → value.length = n) :
 LIBB_C04Partition.partition ([16,tag] ++ value ++ salt) = [[16,tag],value,salt] := by
 have h := congrArg (List.cons [16,tag]) (recover n value salt hv hs full)
 subst n
 by_cases ht : tag = 113
 · simpa [LIBB_C04Partition.partition,ht] using h
 · simpa [LIBB_C04Partition.partition,ht] using h
#print axioms recover
#print axioms leaf
end LIBB_C04PartialPartition
