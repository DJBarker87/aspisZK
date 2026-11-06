import NKU_FineRead
import NKU_Gamma
set_option autoImplicit false
noncomputable section
namespace NKU_FineGamma
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
open NKU_Chronology
def first (v : NKU.E) (s : NKU.Decoded) : NKU.Decoded := {s with gammaAlpha := [v]}
def more (v : NKU.E) (s : NKU.Decoded) : NKU.Decoded := {s with gammaAlpha := s.gammaAlpha++[v]}
def rho (v : NKU.K) (s : NKU.Decoded) : NKU.Decoded := {s with rho := some v}
/-- Five single-occurrence steps on ONE parent carrier (events8–12). -/
def run : Stage Unit := fun s=>do
 let a ← NKU_FineRead.e first s
 NKK_Try.emitted a fun (_,s1)=>do
 let b ← NKU_FineRead.e more s1
 NKK_Try.emitted b fun (_,s2)=>do
 let c ← NKU_FineRead.e more s2
 NKK_Try.emitted c fun (_,s3)=>do
 let d ← NKU_FineRead.e more s3
 NKK_Try.emitted d fun (_,s4)=>do
 let e ← NKU_FineRead.k rho s4
 NKK_Try.emitted e fun (_,s5)=>pure (.Ok ((),{s5 with phase := .queries}))
theorem installed (s : NKU.State) : run s=NKU_Gamma.run s := by
 rw [←NKU_Gamma.source_eq_run]
 unfold run NKU_Gamma.source NKK_FieldStages.gamma NKU_FineRead.e NKU_FineRead.k NKK_FieldStages.withE NKK_FieldStages.withK
 repeat' first
 | rfl
 | (fail_if_no_progress simp only [NKK_LogAlgebra.bind_assoc,NKK_LogReduce.pure_bind,NKK_Try.branch,first,more,rho,NKU_Gamma.reply,NKU_Gamma.post,List.cons_append,List.nil_append])
 | (apply NKK_LogAlgebra.bind_congr;rintro ⟨reply,r⟩;cases reply)

#print axioms installed
end NKU_FineGamma
