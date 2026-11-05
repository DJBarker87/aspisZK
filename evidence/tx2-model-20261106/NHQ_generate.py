"""Factor retained generated drivers without changing any inherited declaration."""
from pathlib import Path
import subprocess,hashlib,json
E=Path(__file__).resolve().parent
path='docs/research/100bit-spend-path-20261013/lean/VTop_Model.lean'
raw=subprocess.check_output(['git','show','HEAD:'+path],text=True)
start=raw.index('def verifier.candidate.tx2_common');end=raw.index('/-- [aspis_r1_cost_probe::verifier::candidate::tx2_authenticated]',start)
body=raw[start:end];tail=body[body.index('  let cf ←'):].rstrip()
common='''import VTop_Model
set_option autoImplicit false
noncomputable section
namespace NHQ_Tx2CommonModel
open Aeneas Aeneas.Std Result VTop_Stages
abbrev R (A : Type) := core.result.Result A verifier.Error
variable {H : Type}
variable (ops : Ops) (digest : aspis_core.digest.Digest32 H)
variable (pub proof checkpoint : Slice U8) (hash : H)
variable (obs : Option (verifier.Phase → Result Unit))
/-- Retained emitted continuation. All runtime failures, divergence and errors remain. -/
def afterResume (r : R (verifier.Prepared × verifier.Accumulator)) : Result (R Unit) := do
'''+tail+'''

def run : Result (R Unit) := do
 let r ← ops.op18 digest checkpoint proof pub AspisR1Stage2.transport.Variant.S2 hash
 afterResume ops digest proof hash obs r

theorem source : verifier.candidate.tx2_common ops digest pub proof checkpoint hash obs =
 run ops digest pub proof checkpoint hash obs := by rfl

theorem resume_reply (reply : R (verifier.Prepared × verifier.Accumulator))
 (resume_packet : ops.op18 digest checkpoint proof pub AspisR1Stage2.transport.Variant.S2 hash = ok reply) :
 run ops digest pub proof checkpoint hash obs = afterResume ops digest proof hash obs reply := by
 unfold run
 rw [resume_packet]
 rfl

theorem resume_error (error : verifier.Error)
 (resume_packet : ops.op18 digest checkpoint proof pub AspisR1Stage2.transport.Variant.S2 hash = ok (.Err error)) :
 run ops digest pub proof checkpoint hash obs = ok (.Err error) := by
 rw [resume_reply ops digest pub proof checkpoint hash obs (.Err error) resume_packet]
 rfl
#print axioms source
#print axioms resume_reply
#print axioms resume_error
end NHQ_Tx2CommonModel
'''
# generated continuation uses the original digest variable name
common=common.replace('aspis_coredigestDigest32Inst','digest')
(E/'NHQ_Tx2CommonModel.lean').write_text(common)
(E/'NHQ_Tx2AuthModel.lean').write_text('''import NHQ_Tx2CommonModel
set_option autoImplicit false
noncomputable section
namespace NHQ_Tx2AuthModel
open Aeneas Aeneas.Std Result VTop_Stages
abbrev R (A : Type) := core.result.Result A verifier.Error
variable {H : Type}
variable (ops : Ops) (digest : aspis_core.digest.Digest32 H)
variable (pub proof checkpoint : Slice U8) (hash : H)
variable (obs : Option (verifier.Phase → Result Unit))

def afterShape (reply : R transport.Variant) : Result (R Unit) := do
 let cf ← core.result.Result.Insts.CoreOpsTry.branch reply
 match cf with
 | .Continue _ =>
   ops.op13 obs AdapterRw.aspis_r1_cost_probe.verifier.Phase.Parsed
   NHQ_Tx2CommonModel.run ops digest pub proof checkpoint hash obs
 | .Break residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
    Unit (core.convert.FromSame verifier.Error) residual

def run : Result (R Unit) := do
 let reply ← ops.op3 proof
 afterShape ops digest pub proof checkpoint hash obs reply

theorem source : verifier.candidate.tx2_authenticated ops digest pub proof checkpoint hash obs =
 run ops digest pub proof checkpoint hash obs := by rfl

theorem parsed (variant : transport.Variant) (shape_packet : ops.op3 proof=ok (.Ok variant)) :
 run ops digest pub proof checkpoint hash obs =
 (do ops.op13 obs AdapterRw.aspis_r1_cost_probe.verifier.Phase.Parsed
     NHQ_Tx2CommonModel.run ops digest pub proof checkpoint hash obs) := by
 unfold run
 rw [shape_packet]
 rfl

theorem shape_error (error : verifier.Error) (shape_packet : ops.op3 proof=ok (.Err error)) :
 run ops digest pub proof checkpoint hash obs = ok (.Err error) := by
 unfold run
 rw [shape_packet]
 rfl
#print axioms source
#print axioms parsed
#print axioms shape_error
end NHQ_Tx2AuthModel
''')
(E/'NHQ_RETAINED_MODEL_PIN.json').write_text(json.dumps(dict(path=path,revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),sha256=hashlib.sha256(raw.encode()).hexdigest(),classification='inherited generated model; NOT fresh E001 output'),indent=2)+'\n')
