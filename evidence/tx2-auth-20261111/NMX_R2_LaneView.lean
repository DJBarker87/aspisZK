import NMX_R2_InverseSliceProps
import NMX_R2_RawChildren
set_option autoImplicit false
noncomputable section
namespace NMX_R2_LaneView
open Aeneas Aeneas.Std RSL NMX_R2_Carrier
/-- Total canonical interface for the same typed native child. A list too
large for a Rust slice is rejected by the same first length test. -/
def view (native : NMX_R2_RawChildren.LaneNative)
 (b : Bytes) (env : Env) : Obs (Except ProgramError LaneState) :=
 match NMX_R2_InverseSlice.fromBytes b with
 | none => ⟨.ret (.error .invalidAccountData),[]⟩
 | some raw => NMX_R2_RawChildren.mapObs (fun box => lane box.payload) (native raw env)

theorem wrong_length (b : Bytes) (wrong : b.length ≠ LANE_ACCOUNT_BYTES) :
 TX2_217.Ref b = RS.throw .invalidAccountData := by
 have header : TX2_217.headerBad b = true := by
  simp only [TX2_217.headerBad,show (b.length != LANE_ACCOUNT_BYTES) = true by simp [wrong],Bool.true_or]
 simp only [TX2_217.Ref,TX2_217.laneDecode,header,↓reduceIte]

/-- Exact canonical RowSpec is consumed at the SAME native slice. -/
theorem raw (native : NMX_R2_RawChildren.LaneNative)
 (packet : TX2_217.RowSpec_217 (view native)) : NMX_R2_RawChildren.RowSpec_217 native := by
 intro b env
 have result := packet (bytes b) env trivial
 simpa only [view,NMX_R2_InverseSlice.roundtrip] using result

/-- This is an interface equivalence, not a new native217 root. In particular
no 768-only native certificate is generalized to every native length here. -/
theorem canonical (native : NMX_R2_RawChildren.LaneNative)
 (packet : NMX_R2_RawChildren.RowSpec_217 native) : TX2_217.RowSpec_217 (view native) := by
 intro b env _
 unfold view
 cases represented : NMX_R2_InverseSlice.fromBytes b with
 | none =>
   have large := NMX_R2_InverseSliceProps.too_large b represented
   have wrong : b.length ≠ LANE_ACCOUNT_BYTES := by
    intro same
    have fits : LANE_ACCOUNT_BYTES ≤ Usize.max := NMX_R2_InverseSliceProps.lane_fits
    rw [same] at large
    omega
   rw [wrong_length b wrong]
   rfl
 | some raw =>
   have same := NMX_R2_InverseSliceProps.image b raw represented
   have result := packet raw env
   rwa [same] at result
#print axioms wrong_length
#print axioms raw
#print axioms canonical
end NMX_R2_LaneView
end
