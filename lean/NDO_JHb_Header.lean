import NDO_JFs_AfterstateDecode
import NDO_JGx_ProofAccount
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHb_Header
open Aeneas Aeneas.Std Result
/-- Exact candidate header retained in the physical public, not an independent
selected successful encoder return. -/
def value : Array U8 688#usize :=
  ⟨JFu_PublicRange.afterstate.val,JFu_PublicRange.length 976 688 (by decide)⟩
attribute [local irreducible] JFu_PublicRange.afterstate
def account : Slice U8 := JGx_ProofAccount.value value

theorem candidate : AspisR1TerminalDecoder.pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1
    value.to_slice = ok (.Ok JFt_AfterstateValue.value) := by
  have same : value.to_slice = JFu_PublicRange.afterstate := by
    apply Subtype.ext
    rfl
  rw [same]
  exact JFs_AfterstateDecode.source
#print axioms candidate

theorem suffix : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    account {start:=688#usize,«end»:=58295#usize}=ok JFx_NativeBytes.proof :=
  JGx_ProofAccount.suffix value
#print axioms suffix

theorem length : account.length=58295 := JGx_ProofAccount.length value
#print axioms length
end AspisR1.JHb_Header
end
