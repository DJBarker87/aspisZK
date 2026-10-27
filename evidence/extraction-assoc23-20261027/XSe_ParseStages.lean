import XSe_RecordAt
import XSe_StageMap
import XRz_ParseFold
open Aeneas Aeneas.Std Result XRn_Join_Release
open XRo_Join_Carriers XRo_Join_ResultTransport
set_option autoImplicit false
namespace XSe_ParseStages

def oldStep (bytes : Slice U8) (i : Nat) (s : XRz_ParseFold.State) :
 Result (core.result.Result XRz_ParseFold.State AspisR1PrefixAggregateParser.r1_wire.Error) := do
 let r ← AspisR1PrefixAggregateParser.r1_wire.parse_record_at bytes (XRz_ParseFold.row i) s.2
 match r with
 | .Err e => ok (.Err e)
 | .Ok pair => ok (.Ok (s.1++[pair.1],pair.2))
/-- Every literal parser stage has the complete associated old Result. -/
theorem step (bytes : Slice U8) (i : Nat) (s : XRz_ParseFold.State) :
 mapR (inner id XRu_ParserShapes.error) (XRz_ParseFold.step bytes i s)=oldStep bytes i s := by
 unfold XRz_ParseFold.step oldStep
 rw [←XSe_RecordAt.source]
 simp only [mapR_bind,bind_map]
 congr 1
 funext result
 cases result <;> rfl
/-- Full27-record ordered driver, preserving the actual list/offset state,
first error and every outer Result constructor on arbitrary byte inputs. -/
theorem source (bytes : Slice U8) (state : core.result.Result XRz_ParseFold.State r1_wire.Error) :
 mapR (inner id XRu_ParserShapes.error)
  (XRx_StageFold.fold (XRz_ParseFold.step bytes) (List.range' 0 27) state)=
 XRx_StageFold.fold (oldStep bytes) (List.range' 0 27) (inner id XRu_ParserShapes.error state) :=
 XSe_StageMap.source XRu_ParserShapes.error _ _ (step bytes) _ state
#print axioms step
#print axioms source
end XSe_ParseStages
