import NFC_KmxFrames
set_option autoImplicit false
namespace NFC_OpeningFrame
/-- Frozen compact constants: OFF_NODES28359 - 22*832 = OFF_OPENINGS10055.
The source pins and native window are separate evidence, not inferred here. -/
def start (query : Nat) : Nat := 10055+query*832

theorem geometry (query offset : Nat) (inside : query<22) (byte : offset<608) :
    start query+608≤start query+832 ∧ start query+832≤28359 ∧
    start query+offset<57607 := by unfold start; omega

/-- A window at any of the22 actual query offsets survives all three
receiver copies when physical disjointness is admitted. -/
theorem frame (a b c heap : Nat → UInt8) (receiver size query offset : Nat)
    (disjoint : start query+832≤receiver ∨ receiver+size≤start query)
    (byte : offset<608) :
    NFC_KmxFrames.three a b c heap receiver size (start query+offset)=heap (start query+offset) := by
  exact NFC_KmxFrames.source_window a b c heap receiver size (start query) 832 disjoint offset (by omega)
#print axioms geometry
#print axioms frame
end NFC_OpeningFrame
