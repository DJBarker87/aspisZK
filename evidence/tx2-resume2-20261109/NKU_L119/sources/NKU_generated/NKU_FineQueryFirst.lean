import NKU_FineWords
import NKU_QueryFirst
set_option autoImplicit false
noncomputable section
namespace NKU_FineQueryFirst
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
open NKU_Chronology
/-- One raw4 occurrence at a time on the parent State, at the native window. -/
def run : Stage Unit := fun s=>do
 let reply ← NKU_FineWords.run 8 ({s with decoded := {s.decoded with queries := []}})
 NKK_Try.emitted reply (fun (_,post)=>pure (.Ok ((),{post with phase := .queries})))
theorem installed (s : NKU.State) : run s=NKU_QueryFirst.run s := by
 unfold run
 rw [NKU_FineWords.installed]
 unfold NKU_FineWords.source NKU_QueryFirst.run NKK_QueryStage.model8
 simp only [NKK_LogAlgebra.bind_assoc,NKK_LogReduce.pure_bind,NKK_Try.branch,NKU_FineWords.post,NKU_QueryFirst.post,List.nil_append]
#print axioms installed
end NKU_FineQueryFirst
