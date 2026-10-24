import S6NativeLateDecodeTotalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6NativeLateWordCast
open AspisR1TerminalDecoder
open pool_v1.pair_tree_profile

theorem word16_frame (raw : Array U8 2#usize) (expected : U16)
    (guard : ¬(UScalar.cast .Usize (core.num.U16.from_le_bytes raw) != UScalar.cast .Usize expected)=true) :
    core.num.U16.to_le_bytes expected=raw := by
  have word : core.num.U16.from_le_bytes raw=expected := by scalar_tac
  rw [←word]
  exact AspisS6NativeLateWordRead.u16_to_from raw

theorem word32_frame (raw : Array U8 4#usize) (expected : U32)
    (guard : ¬(UScalar.cast .Usize (core.num.U32.from_le_bytes raw) != UScalar.cast .Usize expected)=true) :
    core.num.U32.to_le_bytes expected=raw := by
  have word : core.num.U32.from_le_bytes raw=expected := by scalar_tac
  rw [←word]
  exact AspisS6ByteInverse.u32_to_from raw

@[step] theorem late_size : POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES ⦃ result => result=1520#usize ⦄ := by
  obtain ⟨result,run,size⟩ := spec_imp_exists AspisS6NativeLateEncodeTotal.size_spec
  apply exists_imp_spec
  refine ⟨result,run,?_⟩
  scalar_tac

@[step] theorem afterstate_size : pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
    ⦃ result => result=688#usize ⦄ := by
  unfold pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
    pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_PAYLOAD_BYTES
  step*

#print axioms word16_frame
#print axioms word32_frame
#print axioms late_size
#print axioms afterstate_size
end AspisS6NativeLateWordCast
