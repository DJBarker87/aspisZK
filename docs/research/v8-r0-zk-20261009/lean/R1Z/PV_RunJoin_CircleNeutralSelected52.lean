import R1Z.ProverRwFullExternalFuns
import R1Z.PV_RunJoin_CircleRawMap52
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace R1Z.PV_RunJoin_CircleNeutralSelected52
open ProverRwFull
abbrev Q := (U32 × U32) × (U32 × U32)
def point (p : Q × Q) : aspis_core.circle.SecureCirclePoint :=
  ⟨⟨⟨p.1.1.1,p.1.1.2⟩,⟨p.1.2.1,p.1.2.2⟩⟩,
   ⟨⟨p.2.1.1,p.2.1.2⟩,⟨p.2.2.1,p.2.2.2⟩⟩⟩
def row : aspis_core.r0_transcript.CircleRow → Bool | .First => false | .Second => true

def selected [ExternalTypes] (ops : ExternalFuns) : ExternalFuns :=
  {ops with op259 := fun b r => do
    let p ← PV_RunJoin_CircleRawMap52.circle_owned b (row r)
    ok (point p)}

theorem source [ExternalTypes] (ops : ExternalFuns) (b : Array U8 32#usize)
    (r : aspis_core.r0_transcript.CircleRow) :
    (selected ops).op259 b r = (do
      let p ← PV_RunJoin_CircleRawMap52.circle_owned b (row r)
      ok (point p)) := rfl

#print axioms point
#print axioms row
#print axioms selected
#print axioms source
end R1Z.PV_RunJoin_CircleNeutralSelected52
