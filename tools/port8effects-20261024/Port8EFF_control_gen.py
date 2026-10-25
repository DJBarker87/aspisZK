import sys
def emit(path, content):
 if "--check" in sys.argv:
  assert path.read_text()==content,str(path)
 else:path.write_text(content)
from pathlib import Path
R=Path(__file__).resolve().parents[2];L=R/'docs/research/100bit-spend-path-20261013/lean'
s=(L/'VTop_Flow.lean').read_text().split('def tx2_common ',1)[1].split('\ndef tx2_authenticated',1)[0]
s=s[s.index('  let cf ←'):].replace('effects.','VTop_Flow.traceEffects.').replace('aspis_coredigestDigest32Inst','D')
out='''import VTop_OracleCode
import VTop_Flow
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port8EFF_Control
open Aeneas Aeneas.Std Result VTop_Stages VTop_Trace VTop_OracleCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
-- Exact suffix of VTop_Flow.tx2_common, only effects dictionary specialized.
def commonTail {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (public_bytes proof : Slice U8) (hash : Hash)
    (obs : Option (verifier.Phase → Result Unit))
    (r : core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) :
    Code (core.result.Result Unit verifier.Error) := do
'''+s+'''
theorem common_source {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (pub proof ck : Slice U8) (hash : Hash) :
    VTop_Flow.tx2_common VTop_Flow.traceEffects D pub proof ck hash none=
      .call (.op18 D ck proof pub .S2 hash) (commonTail D pub proof hash none) := rfl

theorem rejected (impl : Implementation) {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (pub proof : Slice U8) (hash : Hash) (e : verifier.Error) (H : Bytes → State) :
    eval H (interpret impl (commonTail D pub proof hash none (.Err e)))=([],ok (.Err e)) := rfl

#print axioms common_source
#print axioms rejected
end AspisR1.Port8EFF_Control
end
'''
suffix=s[s.index('      VTop_Flow.traceEffects.op13'):]
# Ends of the outer branch tree are omitted: take exactly the successful
# branch at indentation six, before commonTail's final Break alternative.
suffix=suffix.rsplit('  | core.ops.control_flow.ControlFlow.Break residual =>',1)[0]
suffix='\n'.join(line[6:] if line.startswith('      ') else line for line in suffix.splitlines())
extra="""
def afterPowers {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (proof : Slice U8) (hash : Hash) (obs : Option (verifier.Phase → Result Unit))
    (p : verifier.Prepared) (a : verifier.Accumulator) (i : Usize)
    (g : Array aspis_core.field.wide_exact.WideExact 29#usize) :
    Code (core.result.Result Unit verifier.Error) := do
"""+'\n'.join('  '+line for line in suffix.splitlines())+"""

def afterSplit {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (proof : Slice U8) (hash : Hash) (obs : Option (verifier.Phase → Result Unit))
    (p : verifier.Prepared) (a : verifier.Accumulator) (i : Usize) :
    Code (core.result.Result Unit verifier.Error) :=
  if a.next != i then .done (.Err .Checkpoint)
  else .call (.op17 29#usize p.gamma) (afterPowers D proof hash obs p a i)

theorem common_ok (impl : Implementation) {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (pub proof : Slice U8) (hash : Hash) (p : verifier.Prepared) (a : verifier.Accumulator)
    (H : Bytes → State) :
    eval H (interpret impl (commonTail D pub proof hash none (.Ok (p,a))))=
      eval H (interpret impl (.call .op16 (afterSplit D proof hash none p a))) := rfl

#print axioms common_ok
"""
# Share named source suffixes before interpreting them; never normalize a
# duplicated full continuation under eval (failed attempt019).
start=out.index('-- Exact suffix')
finish=out.index('theorem common_source')
header=out[:start]
rest=out[finish:]
common="""
def commonTail {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (_pub proof : Slice U8) (hash : Hash)
    (obs : Option (verifier.Phase → Result Unit))
    (r : core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) :
    Code (core.result.Result Unit verifier.Error) := do
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | .Continue pair =>
    let (p,a) := pair
    let i ← VTop_Flow.traceEffects.op16
    afterSplit D proof hash obs p a i
  | .Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit (core.convert.FromSame verifier.Error) residual
"""
cut=extra.index('theorem common_ok')
extra=extra[:cut]+common+'\n'+extra[cut:]
tailEnd=extra.index('def afterSplit')
emit(L/'Port8EFF_PowersTail.lean',header+extra[:tailEnd]+'\n#print axioms afterPowers\nend AspisR1.Port8EFF_Control\nend\n')
header=header.replace('import VTop_Flow','import VTop_Flow\nimport Port8EFF_PowersTail')
out=header+extra[tailEnd:]+'\n'+rest
emit(L/'Port8EFF_Control.lean',out)
