import NEX_TerminalOracle
import S6NativeForestDecodeHelpersV1
set_option autoImplicit false
noncomputable section
namespace NEX_TerminalDomain
open Aeneas Aeneas.Std Result WP AspisR1TerminalDecoder
open pool_v1.pair_forest_terminal

theorem byte_count : POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES=ok 1880#usize := by
  obtain ⟨n,run,value⟩ := spec_imp_exists AspisS6NativeForestDecodeHelpers.size_spec
  have same : n=1880#usize := by scalar_tac
  simpa only [same] using run

/-- Other lengths reject before any payload read or child call. -/
theorem wrong_length (bytes : Slice U8) (wrong : bytes.val.length≠1880) :
    decode_pool_v1_pair_forest_terminal_statement_v1 bytes =
    ok (.Err .WrongLength) := by
  unfold decode_pool_v1_pair_forest_terminal_statement_v1
  rw [byte_count]
  simp only [bind_tc_ok]
  split
  · rfl
  · rename_i same
    exfalso
    apply wrong
    unfold Slice.len at same
    scalar_tac

/-- The other branch supplies the exact fixed carrier used by the native body
certificate; this imposes no restriction on the root's input domain. -/
theorem fixed_carrier (bytes : Slice U8) (size : bytes.val.length=1880) :
    ∃ fixed : Array U8 1880#usize, fixed.to_slice=bytes := by
  refine ⟨⟨bytes.val,size⟩,?_⟩
  apply Subtype.ext
  rfl

#print axioms byte_count
#print axioms wrong_length
#print axioms fixed_carrier
end NEX_TerminalDomain
