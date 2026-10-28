import R1Z.PV_AL_CircleCarriers
import R1Z.PV_AL_CircleNative
import R1Z.ProverRwFullExternalFuns
open Aeneas Aeneas.Std Result
noncomputable section
namespace R1Z.PV_AL_CircleSelected
open ProverRwFull PV_AL_CircleCarriers
set_option autoImplicit false
variable [ExternalTypes]

@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ops with op259 := fun block row => do
    let point ← PV_AL_CircleOwned.circle_owned block (encodeRow row)
    ok (decodePoint point)}

/-- Exact selected callback, all byte blocks and both rows, complete Result. -/
theorem native_source (ops : ExternalFuns) (block : Array U8 32#usize) (row : NR) :
    (selected ops).op259 block row=(do
      let point ← PV_AL_CircleNative.nativeCircle block (encodeRow row)
      ok (decodePoint point)) := by
  rw [PV_AL_CircleNative.source_reference]
  rfl

theorem consumed (ops : ExternalFuns) (block : Array U8 32#usize) (row : NR) :
    @sampler.circle_sample _ (selected ops) block row=(do
      let point ← PV_AL_CircleNative.nativeCircle block (encodeRow row)
      ok (decodePoint point)) := native_source ops block row

/-- Both source row values are reachable; the carrier is not an empty type. -/
theorem row_images : encodeRow (.First : NR)=(.First : RR) ∧ encodeRow (.Second : NR)=(.Second : RR) := ⟨rfl,rfl⟩

#print axioms selected
#print axioms native_source
#print axioms consumed
#print axioms row_images
end R1Z.PV_AL_CircleSelected
