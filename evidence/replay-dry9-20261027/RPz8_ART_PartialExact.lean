import RPz8_ART_QueryAgreement
set_option autoImplicit false
noncomputable section
namespace AspisR1.ART_PartialExact
open Aeneas Aeneas.Std Result SdkC_Source
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open ART_PartialProgram

/-- Original result, raw attempted-syscall log, and exact original query cost.
The returned raw log distinguishes failed attempts from successful answers. -/
theorem execution {A : Type} (hashv : Parts → Result Digest) (H : Bytes → State)
    (code : Code A) (agrees : ARS_QueryTransport.Agrees H (run hashv code []).2) :
    eval H (program hashv code []) = (attempted H (run hashv code []).2,run hashv code []) := by
  obtain ⟨out,log⟩ := ART_PartialProgram.exact hashv H code []
    (ART_QueryAgreement.compatible hashv H code [] agrees)
  exact Prod.ext (by simpa only [attempted,List.map_nil,List.nil_append] using log) out

theorem cost {A : Type} (hashv : Parts → Result Digest) (H : Bytes → State)
    (code : Code A) (agrees : ARS_QueryTransport.Agrees H (run hashv code []).2) :
    (eval H (program hashv code [])).1.length = (run hashv code []).2.length := by
  rw [execution hashv H code agrees]
  exact List.length_map _

theorem addresses {A : Type} (hashv : Parts → Result Digest) (H : Bytes → State)
    (code : Code A) (agrees : ARS_QueryTransport.Agrees H (run hashv code []).2) :
    (eval H (program hashv code [])).1.map Prod.fst = RPx_AttemptPrefix.addresses (run hashv code []).2 := by
  rw [execution hashv H code agrees]
  simp only [attempted,RPx_AttemptPrefix.addresses,List.map_map,Function.comp_def]

theorem law {A V : Type} (hashv : Parts → Result Digest) (H : Bytes → State)
    (code : Code A) (agrees : ARS_QueryTransport.Agrees H (run hashv code []).2)
    (observe : Result A → Log → Nat → V) :
    observe (eval H (program hashv code [])).2.1 (eval H (program hashv code [])).2.2
      (eval H (program hashv code [])).1.length =
    observe (run hashv code []).1 (run hashv code []).2 (run hashv code []).2.length := by
  rw [execution hashv H code agrees]
  simp only [attempted,List.length_map]

#print axioms execution
#print axioms cost
#print axioms addresses
#print axioms law
end AspisR1.ART_PartialExact
end
