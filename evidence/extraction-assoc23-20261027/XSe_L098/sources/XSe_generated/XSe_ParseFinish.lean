import XSe_ParseStages
import XSc_ParseDriver
open Aeneas Aeneas.Std Result XRn_Join_Release
open XRo_Join_Carriers XRo_Join_ResultTransport
set_option autoImplicit false
namespace XSe_ParseFinish

def prefix (p : r1_wire.Prefix) : AspisR1PrefixAggregateParser.r1_wire.Prefix :=
 ⟨p.c1_root,p.records⟩
def finish (bytes : Slice U8) (root : Array U8 32#usize) (s : XRz_ParseFold.State) :
 Result (core.result.Result AspisR1PrefixAggregateParser.r1_wire.Prefix AspisR1PrefixAggregateParser.r1_wire.Error) :=
 if s.2 != Slice.len bytes then ok (.Err .TrailingBytes)
 else if h:s.1.length=27 then ok (.Ok ⟨root,⟨s.1,h⟩⟩) else fail .panic

theorem source (bytes : Slice U8) (root : Array U8 32#usize) (s : XRz_ParseFold.State) :
 mapR (inner prefix XRu_ParserShapes.error) (XRz_ParseFold.finish bytes root s)=finish bytes root s := by
 unfold XRz_ParseFold.finish finish
 split
 · rfl
 · split <;> rfl
/-- The literal finishing continuation composes with all27 associated record
stages, preserving rejected states as well as the complete returned prefix. -/
theorem driver (bytes : Slice U8) (root : Array U8 32#usize)
 (state : core.result.Result XRz_ParseFold.State r1_wire.Error) :
 mapR (inner prefix XRu_ParserShapes.error) (do
   let out ← XRx_StageFold.fold (XRz_ParseFold.step bytes) (List.range' 0 27) state
   match out with | .Err e => ok (.Err e) | .Ok s => XRz_ParseFold.finish bytes root s)=
 (do
   let out ← XRx_StageFold.fold (XSe_ParseStages.oldStep bytes) (List.range' 0 27)
    (inner id XRu_ParserShapes.error state)
   match out with | .Err e => ok (.Err e) | .Ok s => finish bytes root s) := by
 rw [←XSe_ParseStages.source bytes state]
 simp only [mapR_bind,bind_map]
 congr 1
 funext out
 cases out with
 | Err e => rfl
 | Ok s => exact source bytes root s
#print axioms source
#print axioms driver
end XSe_ParseFinish
