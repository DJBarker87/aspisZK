import NDO_JFt_Afterstate00
set_option autoImplicit false
namespace AspisR1.JFs_AfterstateSize
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_terminal

theorem bytes : POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES=ok 688#usize := by
  unfold POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES POOL_V1_PAIR_VERIFIED_AFTERSTATE_PAYLOAD_BYTES
  obtain ⟨z,call,value⟩:=WP.spec_imp_exists
    (Usize.add_spec (x:=8#usize) (y:=680#usize) (by scalar_tac))
  have same : z=688#usize := by scalar_tac
  exact same ▸ call

theorem length : Slice.len JFu_PublicRange.afterstate=688#usize := by
  have h : JFu_PublicRange.afterstate.length=688 := JFu_PublicRange.length 976 688 (by decide)
  scalar_tac

#print axioms bytes
#print axioms length
end AspisR1.JFs_AfterstateSize
