import ART_QueryCylinder
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARV_LogChange
open Aeneas Aeneas.Std Result SdkC_Source
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge

theorem agrees (native : Bytes → State) (address : Bytes) (value : State) (log : Log)
    (original : ARS_QueryTransport.Agrees native log)
    (fresh : address ∉ log.map (fun q => flatten q.parts)) :
    ARS_QueryTransport.Agrees (ART_QueryCylinder.change native address value) log := by
  intro q member digest returned
  have different : flatten q.parts ≠ address := by
    intro same
    exact fresh (same ▸ List.mem_map.mpr ⟨q,member,rfl⟩)
  rw [ART_QueryCylinder.change,if_neg different]
  exact original q member digest returned

#print axioms agrees
end AspisR1.ARV_LogChange
end
