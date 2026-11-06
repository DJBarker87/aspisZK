import NKU_FineRead
import NKU_Roots
set_option autoImplicit false
noncomputable section
namespace NKU_FineRoots
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
open NKU_Chronology
def first (v : Array U8 32#usize) (s : NKU.Decoded) : NKU.Decoded := {s with roots := [v]}
def more (v : Array U8 32#usize) (s : NKU.Decoded) : NKU.Decoded := {s with roots := s.roots++[v]}
def run : Stage Unit := fun s=>do
 let a ← NKU_FineRead.raw 32#usize first {s with reader := NKU_Roots.entry s}
 NKK_Try.emitted a fun (_,s1)=>do
 let b ← NKU_FineRead.raw 32#usize more s1
 NKK_Try.emitted b fun (_,s2)=>do
 let c ← NKU_FineRead.raw 32#usize more s2
 NKK_Try.emitted c fun (_,s3)=>pure (.Ok ((),{s3 with phase := .fields}))
theorem installed (s : NKU.State) : run s=NKU_Roots.run s := by
 rw [←NKU_Roots.source_eq_run]
 unfold run NKU_Roots.source
 simp_rw [NKU_FineRead.raw_bind]
 simp only [NKK_RawPrefix.literal,NKK_LogAlgebra.bind_assoc,NKK_LogReduce.pure_bind,NJU_Log.prod_cases,first,more,NKU_Roots.post,List.cons_append,List.nil_append]
 rfl
#print axioms installed
end NKU_FineRoots
