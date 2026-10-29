import NED_LateReadWindows
import NEC_AfterstateWindows
import NEC_PureReplyAssociation
set_option autoImplicit false
namespace NED_AfterBoxDomain
open Aeneas Aeneas.Std Result

/-- The actual late decoder's afterstate window, with its SAME selected bytes. -/
theorem selected (bytes : Array U8 1520#usize) :
    (NBP_Read.chunk (W:=688#usize) bytes 832 (by decide)).val = bytes.val.drop 832 := by
  rw [NED_ReadDomains.bytes_retained]
  apply List.take_of_length_le
  have length := bytes.property
  simp only [List.length_drop]
  scalar_tac

/-- Discharge both imported native envelopes at the caller's precise window. -/
theorem domains (bytes : Array U8 1520#usize) :
    NEC_AfterstateBox.PacketDomain
      (NBP_Read.chunk (W:=688#usize) bytes 832 (by decide)).to_slice ∧
    NEC_PureReplyAssociation.PacketDomain
      (NBP_Read.chunk (W:=688#usize) bytes 832 (by decide)).to_slice := by
  have length : (NBP_Read.chunk (W:=688#usize) bytes 832 (by decide)).to_slice.val.length = 688 := by
    have h := (NBP_Read.chunk (W:=688#usize) bytes 832 (by decide)).property
    simpa [Array.to_slice] using h
  exact ⟨length,NEC_PureReplyAssociation.caller_domain _ length⟩

#print axioms selected
#print axioms domains
end NED_AfterBoxDomain
