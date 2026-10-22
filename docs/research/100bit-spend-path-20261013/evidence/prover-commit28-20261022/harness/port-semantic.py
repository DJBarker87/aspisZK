"""Lift semantic and circle callers without replacing the retained validators."""
from pathlib import Path
import re,sys,json,hashlib
root=Path('docs/research/v8-r0-zk-20261009/lean')
manifest=[]
for kind,owner,names in [('Semantic','AspisR1SimSemantic20',{'r1_wire.SemanticTranscript.sample_block_validated':'sample','r1_wire.semantic20.semantic':'semantic'}),('Circle','AspisR1CircleCaller25',{'r1_wire.SemanticTranscript.sample_block_validated':'sample','r1_wire.circle25.point':'point'})]:
 src=root/owner/'Funs.lean';s=src.read_text();pieces=[]
 for old,new in names.items():
  start=s.index('def '+old+'\n');end=s.find('\n/--',start)
  if end<0:end=s.index('\nend '+owner,start)
  b=s[start:end]
  b=re.sub(r'\(aspis_coredigestDigest32Inst :\s*aspis_core.digest.Digest32 H\)', '(effect : H → Parts → M Bytes32)',b)
  b=b.replace('sampler.qm31_sample',owner+'.sampler.qm31_sample')
  b=b.replace('aspis_coredigestDigest32Inst.digest','effect').replace('aspis_coredigestDigest32Inst','effect')
  for a,c in names.items():b=b.replace(a,c)
  b,n=re.subn(r'\n  Result ', '\n  M ',b,count=1);assert n==1
  b=re.sub(r'\bok\b','pure',b)
  pieces.append(b)
 header=f'''import {owner}.Funs
import R1Z.ProverCommitStateLift28
/-! Generic monadic lift of the retained {kind.lower()} caller. Pure validation
and decoding use the original retained functions. -/
set_option autoImplicit false
namespace R1Z.ProverCommit{kind}Program28
open Aeneas Aeneas.Std Result {owner} ProverCommitStateLift28
variable {{M : Type → Type}} [Monad M] [MonadLiftT Result M]
'''
 out=header+'\n\n'.join(pieces)+f'\nend R1Z.ProverCommit{kind}Program28\n'
 dst=root/f'R1Z/ProverCommit{kind}Program28.lean'
 if '--check' in sys.argv:assert dst.read_text()==out
 else:dst.write_text(out)
 manifest.append(dict(source=str(src),source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),output=str(dst),output_sha256=hashlib.sha256(out.encode()).hexdigest(),functions=names))
(Path(__file__).resolve().parent.parent/'semantic-port.json').write_text(json.dumps(manifest,indent=2)+'\n')
