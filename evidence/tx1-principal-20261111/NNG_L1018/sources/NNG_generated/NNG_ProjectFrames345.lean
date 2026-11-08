import NNG_Tree345
import NNG_NativeCaller345
import NNG_Model345
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ProjectFrames345
open Aeneas Aeneas.Std NMT_345 RSL

def original {W : Type} (s : NMT_345.Parent W) : TX1_345.Args :=
 ⟨key s.program,s.accounts.val.map account,LIB_Carriers.bytes s.data⟩
def selected {W : Type} (s : Selected W) : NNG_Phases345.Parent :=
 ⟨original s.toParent,account s.proofAccount,account s.publicAccount,account s.checkpointAccount⟩
def checkpoint {W : Type} (s : NMT_345.CheckpointData W) : NNG_Phases345.CheckpointData :=
 ⟨selected s.toSelected,LIB_Carriers.bytes s.checkpointData⟩
def publicData {W : Type} (s : NMT_345.PublicData W) : NNG_Phases345.PublicData :=
 ⟨checkpoint s.toCheckpointData,LIB_Carriers.bytes s.publicData⟩
def decoded {W : Type} (s : NMT_345.Decoded W)
 (hd : decodeCall s.publicData=.ok (.Ok s.statement)) :
 NNG_Phases345.Decoded LIB_Instances.VL LIB_Instances.C :=
 ⟨publicData s.toPublicData,s.statement,NNG_NativeCaller345.decoded _ _ hd⟩
def validated {W : Type} (s : NMT_345.Decoded W)
 (hd : decodeCall s.publicData=.ok (.Ok s.statement))
 (hv : validateCall s.statement=.ok (.Ok ())) :
 NNG_Phases345.Validated LIB_Instances.VL LIB_Instances.C :=
 ⟨decoded s hd,(LIBC_S1.valid_iff s.statement).mpr hv⟩
def candidate {W : Type} (s : NMT_345.Candidate W)
 (hd : decodeCall s.publicData=.ok (.Ok s.statement))
 (hv : validateCall s.statement=.ok (.Ok ())) :
 NNG_Phases345.Candidate LIB_Instances.VL LIB_Instances.C :=
 ⟨validated s.toDecoded hd hv,s.candidate.val.map byte⟩
def proofData {W : Type} (s : NMT_345.ProofData W)
 (hd : decodeCall s.publicData=.ok (.Ok s.statement))
 (hv : validateCall s.statement=.ok (.Ok ())) :
 NNG_Phases345.ProofData LIB_Instances.VL LIB_Instances.C :=
 ⟨candidate s.toCandidate hd hv,LIB_Carriers.bytes s.proofData⟩

theorem original_data {W : Type} (s : NMT_345.Parent W) :
 (original s).data=LIB_Carriers.bytes s.data := rfl
#print axioms original_data
end AspisR1.NNG_ProjectFrames345
