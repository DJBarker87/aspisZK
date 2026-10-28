import NDO_JFw_Loop
set_option autoImplicit false
namespace AspisR1.JFw_Entry
open Aeneas Aeneas.Std Result WP
open AspisS1NativeCompact AspisS1ValuesOwnedInstallation PSem_Iterator

@[local step] theorem loop_spec (input out : Slice U8)
    (hi : input.length = 7015) (ho : out.length = 13831) :
    compact.expand_semantic_loop nativeValues
      {start:=0#u8,«end»:=compact.SEMANTIC_ROWS} input out 32#usize 32#usize
      ⦃ result => result.1 = .Ok () ⦄ := by
  obtain ⟨updated,call⟩ := JFw_Loop.success 27 0#u8 rfl input out 32#usize 32#usize hi ho rfl rfl
  unfold iter at call
  rw [call]
  rfl

theorem success (input out : Slice U8)
    (hi : input.length = 7015) (ho : out.length = 13831) :
    ∃ expanded, compact.expand_semantic nativeValues input out = ok (.Ok (),expanded) := by
  have hs : compact.expand_semantic nativeValues input out ⦃ result => result.1 = .Ok () ⦄ := by
    unfold compact.expand_semantic compact.COMPACT_SEMANTIC compact.SEMANTIC_COMPACT_VALUES
      compact.LOGICAL_SEMANTIC verifier.SEMANTIC_BYTES
    step* <;> first | scalar_tac | simp_all [Slice.length,List.length_setSlice!]

  obtain ⟨result,call,status⟩ := spec_imp_exists hs
  rcases result with ⟨status',expanded⟩
  change status' = .Ok () at status
  subst status'
  exact ⟨expanded,call⟩

#print axioms loop_spec
#print axioms success
end AspisR1.JFw_Entry
