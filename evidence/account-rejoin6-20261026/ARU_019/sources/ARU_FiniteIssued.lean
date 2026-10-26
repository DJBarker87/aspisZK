import ARU_OracleLog
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARU_FiniteIssued
open Aeneas Aeneas.Std Result SdkC_Source
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge

def addresses (log : Log) : Finset Bytes := (log.map (fun q => flatten q.parts)).toFinset

theorem finite (log : Log) : (↑(addresses log) : Set Bytes).Finite := Finset.finite_toSet _

theorem transport (native H : Bytes → State) (log : Log)
    (original : ARS_QueryTransport.Agrees native log)
    (consistent : ∀ address ∈ addresses log, H address = native address) :
    ARS_QueryTransport.Agrees H log := by
  intro q member digest returned
  have issued : flatten q.parts ∈ addresses log := by
    simp only [addresses,List.mem_toFinset]
    exact List.mem_map.mpr ⟨q,member,rfl⟩
  exact (original q member digest returned).trans (consistent _ issued).symm

#print axioms finite
#print axioms transport
end AspisR1.ARU_FiniteIssued
end
