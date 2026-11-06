import NKU_FineRead
import NKK_RawPrefix
set_option autoImplicit false
noncomputable section
namespace NKU_FineWords
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
open NKU_Chronology
def write (v : Array U8 4#usize) (s : NKU.Decoded) : NKU.Decoded :=
 {s with queries := s.queries++[core.num.U32.from_le_bytes v]}
def post (s : NKU.State) (bs : List (Array U8 4#usize)) (r : verifier.Reader) : NKU.State :=
 {s with reader := r,decoded := {s.decoded with queries := s.decoded.queries++bs.map core.num.U32.from_le_bytes}}
/-- One arbitrary native raw4 pre-state per step, induction over chronology. -/
def run : Nat → Stage Unit
 | 0 => fun s=>pure (.Ok ((),s))
 | n+1 => fun s=>do
   let reply ← NKU_FineRead.raw 4#usize write s
   NKK_Try.emitted reply (fun (_,next)=>run n next)
def source (n : Nat) (s : NKU.State) : Run (core.result.Result (Unit × NKU.State) verifier.Error) := do
 let (bs,last) ← NKK_RawPrefix.literal 4#usize n s.reader
 pure (.Ok ((),post s bs last))
theorem installed (n : Nat) (s : NKU.State) : run n s=source n s := by
 induction n generalizing s with
 | zero => simp only [run,source,NKK_RawPrefix.literal,NKK_LogReduce.pure_bind,post,List.map_nil,List.append_nil]
 | succ n ih =>
  unfold run NKU_FineRead.raw
  simp only [NKK_LogAlgebra.bind_assoc,NKK_LogReduce.pure_bind,NKK_Try.branch]
  simp_rw [ih]
  unfold source
  simp only [NKK_RawPrefix.literal,NKK_LogAlgebra.bind_assoc,NKK_LogReduce.pure_bind,NJU_Log.prod_cases]
  apply NKK_LogAlgebra.bind_congr
  rintro ⟨b,next⟩
  apply NKK_LogAlgebra.bind_congr
  rintro ⟨bs,last⟩
  simp only [post,write,List.map_cons,List.append_assoc,List.singleton_append]
#print axioms installed
end NKU_FineWords
