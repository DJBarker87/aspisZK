from pathlib import Path
p=Path(__file__).resolve().parent
for name,frame,field,raw,nextRaw,boundary in [
 ('CheckpointData','Selected','checkpointAccount','raw03','raw04','boundaryCheckpointData'),
 ('PublicData','CheckpointData','publicAccount','raw05','raw06','boundaryPublicData'),
 ('ProofData','Candidate','proofAccount','raw09','raw10','boundaryProofData')]:
 s=f'''import NMT_345Boundary{name}
import NMT_R2_GetterEquality
set_option autoImplicit false
noncomputable section
namespace NMT_R2_345At{name}
open Aeneas Aeneas.Std NMT_345 RSL

def install (keep : Bool) (c : Calls) : Calls :=
 {{c with c10 := NMT_R2_EmittedData.clone keep}}

/-- One exact E003 getter occurrence; every outer/inner Result is retained. -/
theorem boundary {{W : Type}} (keep : Bool) (c : Calls) (s : {frame} W) :
 {raw} (install keep c) s =
 tryStep (NMT_stage1_owned.r1_pool_adapter.owned.OwnedAccount.data
  (NMT_R2_EmittedData.clone keep) s.{field})
  (fun bytes => {nextRaw} (install keep c) ⟨s,bytes⟩) := {boundary} _ s

theorem observation {{W : Type}} (keep : Bool) (s : {frame} W) (env : Env) :
 NMT_R2.data (account s.{field}) env (NMT_R2_EmittedData.run keep s.{field}) :=
 NMT_R2_EmittedData.emitted_data keep s.{field} env
#print axioms boundary
#print axioms observation
end NMT_R2_345At{name}
end
'''
 (p/f'NMT_R2_345At{name}.lean').write_text(s)
