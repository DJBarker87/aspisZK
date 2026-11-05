import NHV_TailWindows
import NHV_NET_WideModel
import NHT_PacketOps
set_option autoImplicit false
noncomputable section
namespace NHV_InactivePacket
open Aeneas Aeneas.Std Result AspisR1
abbrev E := AspisR1Stage2.aspis_core.field.wide_exact.WideExact
/-- Full Option and nonreturn carrier, mapped only by the retained coordinate port. -/
def packet (bytes : Slice U8) : Result (Option E) := do
 let decoded ← NET_WideModel.wide bytes
 ok (Option.map FIo_Install.fromE decoded)

def emitted (bytes : Slice U8) : Result (Option E) := do
 let decoded ← FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes bytes
 ok (Option.map FIo_Install.fromE decoded)

theorem source (bytes : Slice U8) : packet bytes=emitted bytes := by
 unfold packet emitted
 rw [NET_WideModel.result]

/-- The actual inactive call window on SAME proof, without a fresh byte witness. -/
theorem exact_window (proof : Slice U8) (bound : 7527≤proof.val.length) :
 ∃ range : 7495+32≤proof.val.length,
 let bytes := NEO_FixedWindow.window proof 7495 32#usize range
 bytes.val=(proof.val.drop 7495).take 32 ∧
 packet bytes.to_slice=emitted bytes.to_slice := by
 have range : 7495+32≤proof.val.length := by omega
 exact ⟨range,rfl,source _⟩

/-- Native callee rejection is retained verbatim, not a success premise. -/
theorem reject (bytes : Slice U8)
 (call : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes bytes=ok none) :
 packet bytes=ok none := by
 rw [source]
 unfold emitted
 rw [call]
 rfl
#print axioms source
#print axioms exact_window
#print axioms reject
end NHV_InactivePacket
