"""Reinterpret ONE existing emitted body; no Rust/extractor/source changes."""
from pathlib import Path
import subprocess,re,hashlib,json
p='docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean'
s=subprocess.check_output(['git','show','HEAD:'+p],text=True)
name='aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body'
start=s.index('def\n  '+name);end=s.index('\n/--',start)
body=s[start:end]
assert body.count('getrandom.fill s')==1
body=body.replace('def\n  '+name,'def entropyBody (answers : EntropyAnswers)')
body=body.replace('  Result (ControlFlow','  M (ControlFlow',1).replace('getrandom.fill s','draw answers s')
body=re.sub(r'\bok \(', 'pure (',body)
header='''import PV_EVH_World
set_option autoImplicit false
noncomputable section
namespace PV_EVH_Entropy
open Aeneas Aeneas.Std ProverRwFull ControlFlow
open PV_EVH_World
variable [ExternalTypes] [ExternalFuns]

abbrev FillReply := Result ((core.result.Result Unit getrandom.error.Error) × Slice U8)
abbrev EntropyAnswers := Nat → Slice U8 → FillReply

def ascii (s : String) : PV_RJ4IDB.Bytes :=
  s.toList.map (fun c => UInt8.ofNat c.toNat)

def draw (answers : EntropyAnswers) (buffer : Slice U8) : M
    ((core.result.Result Unit getrandom.error.Error) × Slice U8) := fun w =>
  ⟨answers w.entropyCursor buffer,{w with entropyCursor := w.entropyCursor + 1},
    [.side (ascii "entropy-request") (ascii (toString w.entropyCursor)),
     .side (ascii "entropy-delivery") (ascii (toString w.entropyCursor))]⟩

instance : MonadLift Result M where
  monadLift := PV_EVH_World.lift

theorem draw_fixed (answers : EntropyAnswers)
    (h : ∀ n s, answers n s = getrandom.fill s) (buffer : Slice U8) :
    FixedView (draw answers buffer) (getrandom.fill buffer) :=
  fun w => h w.entropyCursor buffer

/- Exact emitted body, only monad lift / entropy primitive interpretation.
Every other helper remains a fixed Result call: whole-prover event credit is
NOT claimed. The structural diff and original hash are recorded separately. -/
'''
footer='''
#print axioms draw_fixed
end PV_EVH_Entropy
'''
Path('lean/PV_EVH_Entropy.lean').write_text(header+body+footer)
Path('evidence/pv-evh4-20261029/entropy-generation.json').write_text(json.dumps(dict(source=p,revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_sha256=hashlib.sha256(s.encode()).hexdigest(),body_sha256=hashlib.sha256(s[start:end].encode()).hexdigest(),changes=['Result return interpreted as M','one getrandom.fill replaced by draw','ok terminals interpreted as pure','other Result actions lifted by MonadLift'],source_body=s[start:end],status='single-body reinterpretation; other helpers still Result-only'),indent=2)+'\n')
