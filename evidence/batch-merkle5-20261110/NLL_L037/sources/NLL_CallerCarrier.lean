import NLL_TreeReturning
import CheckpointBytes4SavedFields
set_option autoImplicit false
noncomputable section
namespace NLL_CallerCarrier
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1 MultiproofConeRef NLL
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- Canonical physical query words follow from SAME returned Prepared fields;
modulo conversion is not being used to weaken the native query domain. The
external parent must install BodyMatches from its CLOSED resume/prepare packet.
This theorem discharges the batch helper's primitive query bound only. -/
theorem canonical (p : verifier.Prepared) (a : verifier.Accumulator)
 (pm : OraclePortCheckpointAbiC5.Prepared)
 (am : QueryAccumulator.State OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E)
 (fields : CheckpointBytes4SavedFields.BodyMatches p a pm am) :
 ∀ j,j<22 → p.queries.val[j]!.val<262144 := by
 intro j hj
 have rawLen : p.queries.val.length=22 := p.queries.property
 have valid : j<p.queries.val.length := by omega
 have physical:=congrArg (fun xs : List Nat => xs[j]?) fields.queries
 simp only [List.getElem?_map,List.getElem?_eq_getElem valid,Option.map_some,List.getElem?_ofFn,hj,↓reduceDIte] at physical
 have same:=Option.some.inj physical
 simpa only [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem valid,Option.getD_some,same]
   using (pm.queries ⟨j,hj⟩).isLt

set_option pp.proofs false
#print canonical
#print axioms canonical
end NLL_CallerCarrier
end
