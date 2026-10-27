import XRn_Join_ByteFields
import AspisR1WideToBytesIndexedCandidate.ToBytesGeneratedOutputV11
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XRs_ByteSteps
/-- Explicit width-decreasing expansions avoid recursive simp. -/
theorem bytes32 (b : BitVec 32) : b.toLEBytes =
 [b.setWidth 8, ((b >>> 8).setWidth 24).setWidth 8,
 (((((b >>> 8).setWidth 24) >>> 8).setWidth 16)).setWidth 8,
 (((((((b >>> 8).setWidth 24) >>> 8).setWidth 16) >>> 8).setWidth 8)).setWidth 8] := by
 rw [BitVec.toLEBytes.eq_1 (w:=32)]
 rw [if_pos (by decide : 32>0)]
 rw [BitVec.toLEBytes.eq_1 (w:=24)]
 rw [if_pos (by decide : 24>0)]
 rw [BitVec.toLEBytes.eq_1 (w:=16)]
 rw [if_pos (by decide : 16>0)]
 rw [BitVec.toLEBytes.eq_1 (w:=8)]
 rw [if_pos (by decide : 8>0)]
 rw [BitVec.toLEBytes.eq_1 (w:=0)]
 rw [if_neg (by decide : ¬(0>0))]
#print axioms bytes32
end XRs_ByteSteps
