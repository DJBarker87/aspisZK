import NKU_FineRead
import NKU_ZClaim
set_option autoImplicit false
noncomputable section
namespace NKU_FineZ
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
open NKU_Chronology
def first (v : NKU.K) (s : NKU.Decoded) : NKU.Decoded := {s with z := [v]}
def more (v : NKU.K) (s : NKU.Decoded) : NKU.Decoded := {s with z := s.z++[v]}
def claim (v : NKU.E) (s : NKU.Decoded) : NKU.Decoded := {s with claim := some v}
def rhs (v : NKU.E) (s : NKU.Decoded) : NKU.Decoded := {s with rhs := some v}
def power (v : NKU.K) (s : NKU.Decoded) : NKU.Decoded := {s with power := some v}
def run : Stage Unit := fun s=>do
 let a ← NKU_FineRead.k first s
 NKK_Try.emitted a fun (_,s1)=>do
 let b ← NKU_FineRead.k more s1
 NKK_Try.emitted b fun (_,s2)=>do
 let c ← NKU_FineRead.k more s2
 NKK_Try.emitted c fun (_,s3)=>do
 let d ← NKU_FineRead.k more s3
 NKK_Try.emitted d fun (_,s4)=>do
 let e ← NKU_FineRead.e claim s4
 NKK_Try.emitted e fun (_,s5)=>do
 let f ← NKU_FineRead.e rhs s5
 NKK_Try.emitted f fun (_,s6)=>do
 let g ← NKU_FineRead.k power s6
 NKK_Try.emitted g fun (_,s7)=>pure (.Ok ((),{s7 with phase := .filled}))
theorem installed (s : NKU.State) : run s=NKU_ZClaim.run s := by
 rw [←NKU_ZClaim.source_eq_run]
 unfold run NKU_ZClaim.source NKK_ZStage.source NKU_FineRead.e NKU_FineRead.k NKK_FieldStages.withE NKK_FieldStages.withK
 repeat' first
 | rfl
 | (fail_if_no_progress simp only [NKK_LogAlgebra.bind_assoc,NKK_LogReduce.pure_bind,NKK_Try.branch,first,more,claim,rhs,power,NKU_ZClaim.reply,NKU_ZClaim.post,List.cons_append,List.nil_append])
 | (apply NKK_LogAlgebra.bind_congr;rintro ⟨reply,r⟩;cases reply)

#print axioms installed
end NKU_FineZ
