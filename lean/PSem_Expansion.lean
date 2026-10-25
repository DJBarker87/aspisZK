import PSem_Loop
set_option autoImplicit false
namespace AspisR1.PSem_Expansion
open Aeneas Aeneas.Std Result PSem_Control PSem_Iterator
open AspisS1NativeCompact AspisS1NativeCompactBodyFrame
open AspisS1ValuesOwnedInstallation MultiproofConeCanonical
open AspisV8R19.DuplexFrames

/-- The actual complete semantic expansion produces exactly the frozen
expansion-stage rows on its original compact input. No row-list, buffer
identity, loop completion or value-leaf agreement is assumed. -/
theorem source_rows (input out expanded : Slice U8)
    (success : compact.expand_semantic nativeValues input out=ok (.Ok (),expanded)) :
    ∃ rs : List Bytes,
      PSem_Rows.expandRows 27 0 (bytesOf (input.val.drop 32))=some rs ∧
      bytesOf (expanded.val.drop 32)=rs.flatten := by
  unfold compact.expand_semantic at success
  obtain ⟨compactLength,hcompactLength,success⟩ := bind_success _ _ _ success
  split at success
  · cases success
  · obtain ⟨logicalLength,hlogicalLength,success⟩ := bind_success _ _ _ success
    split at success
    · cases success
    · obtain ⟨header,back,hheader,success⟩ := pair_success _ _ _ success
      obtain ⟨sourceHeader,hsourceHeader,success⟩ := bind_success _ _ _ success
      obtain ⟨replacement,hreplacement,success⟩ := bind_success _ _ _ success
      have loopCall : compact.expand_semantic_loop nativeValues (iter 0#u8)
        input (back replacement) 32#usize 32#usize=ok (.Ok (),expanded) := success
      obtain ⟨rs,rows,joined⟩ := PSem_Loop.loop_rows 27 0#u8 rfl input
        (back replacement) expanded 32#usize 32#usize loopCall
      have bound : 32 ≤ out.length := by
        simp only [Slice.index_mut_SliceIndexRangeToUsizeSliceInst] at hheader
        unfold core.slice.index.SliceIndexRangeToUsizeSlice.index_mut at hheader
        split at hheader
        · assumption
        · cases hheader
      have length := AspisS1NativeCompactLengths.rangeTo_length out header back 32#usize hheader replacement
      have prefixLength : (bytesOf ((back replacement).val.take 32)).length=32 := by
        simp only [bytesOf,List.length_map,List.length_take]
        change min 32 (back replacement).length=32
        omega
      have dropped := congrArg (fun b : Bytes => b.drop 32) joined
      change (bytesOf expanded.val).drop 32=
        (bytesOf ((back replacement).val.take 32) ++ rs.flatten).drop 32 at dropped
      rw [List.drop_append,prefixLength,Nat.sub_self,List.drop_zero,
        List.drop_eq_nil_of_le (by omega : (bytesOf ((back replacement).val.take 32)).length ≤ 32),
        List.nil_append] at dropped
      exact ⟨rs,rows,by simpa only [bytesOf,List.map_drop] using dropped⟩

#print axioms source_rows
end AspisR1.PSem_Expansion
