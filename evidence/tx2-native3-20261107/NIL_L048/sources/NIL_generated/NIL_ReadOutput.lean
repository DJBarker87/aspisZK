import NIL_FreshOps
import NID_ResumeCallerDomain
set_option autoImplicit false
noncomputable section
namespace NIL_ReadOutput
open Aeneas Aeneas.Std Result NIL_Carriers AspisR1

theorem k (r out : Fresh.R) (x : Fresh.K)
 (bound : r.at.val+16≤r.bytes.val.length)
 (call : NIL_FreshOps.readK r=ok (.Ok x,out)) :
 NID_ResumeCanonical.KCanonical (NIL_Carriers.k x) ∧
 out.at.val=r.at.val+16 ∧ out.bytes=r.bytes ∧
 ∃ model, ExactLeafFieldCodec.decodeQM31
  (OraclePortCompactDraft.slice (MultiproofConeCanonical.bytesOf r.bytes.val) r.at.val 16)=some model ∧
  CheckpointBytes4ReaderFields.sourceK model=NIL_Carriers.k x := by
 have transported : CheckpointBytes3Reader.readK (reader r)=ok (.Ok (NIL_Carriers.k x),reader out) := by
  rw [←NIL_FreshOps.k_port r,call]
  rfl
 obtain ⟨model,decode,value,cursor,backing⟩ := CheckpointBytes4ReaderFields.k_success
  (reader r) (reader out) (NIL_Carriers.k x) bound transported
 refine ⟨?_,cursor,backing,model,decode,value⟩
 rw [←value]
 exact NID_ResumeCanonical.sourceK_canonical model

theorem e (r out : Fresh.R) (x : Fresh.E)
 (bound : r.at.val+32≤r.bytes.val.length)
 (call : NIL_FreshOps.readE r=ok (.Ok x,out)) :
 NID_ResumeCanonical.ECanonical (NIL_Carriers.e x) ∧
 out.at.val=r.at.val+32 ∧ out.bytes=r.bytes ∧
 ∃ model, FoldedLeafCodec.decodeWide
  (OraclePortCompactDraft.slice (MultiproofConeCanonical.bytesOf r.bytes.val) r.at.val 32)=some model ∧
  CheckpointBytes4ReaderFields.sourceE model=NIL_Carriers.e x := by
 have transported : CheckpointBytes3Reader.readE (reader r)=ok (.Ok (NIL_Carriers.e x),reader out) := by
  rw [←NIL_FreshOps.e_port r,call]
  rfl
 obtain ⟨model,decode,value,cursor,backing⟩ := CheckpointBytes4ReaderFields.e_success
  (reader r) (reader out) (NIL_Carriers.e x) bound transported
 refine ⟨?_,cursor,backing,model,decode,value⟩
 rw [←value]
 exact NID_ResumeCanonical.sourceE_canonical model

#print axioms k
#print axioms e
end NIL_ReadOutput
