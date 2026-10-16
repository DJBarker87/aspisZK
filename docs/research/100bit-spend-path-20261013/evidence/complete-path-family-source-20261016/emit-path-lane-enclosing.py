from pathlib import Path
import hashlib,json,re
repo=Path('/Users/dominic/ZK/.worktrees/100bit-spend-path')
p=repo/'docs/research/100bit-spend-path-20261013/evidence/terminal-indexed-source-candidate-20261016/Funs.lean'
s=p.read_text();prefix='pool_v1.pair_forest_semantic_terminal.'
start=s.index('def '+prefix+'add_path_lanes\n');end=s.index('\n/-- ',start);body=s[start:end].rstrip()+'\n'
mapping={prefix+'sum_high':'AspisR1SumHighCandidate.'+prefix+'sum_high',prefix+'path_lanes_literal':'AspisR1PathLaneCandidate.'+prefix+'path_lanes_literal',prefix+'add_preweighted':'AspisR1PreweightedCandidate.'+prefix+'add_preweighted'}
pattern=re.compile('|'.join(re.escape(k) for k in sorted(mapping,key=len,reverse=True)));adapted=pattern.sub(lambda m:mapping[m.group()],body)
rev={v:k for k,v in mapping.items()};inverse=re.compile('|'.join(re.escape(v) for v in sorted(rev,key=len,reverse=True)));assert inverse.sub(lambda m:rev[m.group()],adapted)==body
header='''import SumHighGeneratedSlice
import PathLaneGeneratedSlice
import PreweightedLoopSlice

/-! Whole actual generated enclosing add_path_lanes candidate declaration.
Only helper-reference qualification and the namespace are adapted; the
inverse map recovers every original declaration byte. -/
open Aeneas Aeneas.Std Result ControlFlow Error
namespace AspisR1PathEnclosingCandidate
open AspisR1SelectedMaskProbe

'''
q=Path('/tmp/PathLaneEnclosingSlice.lean');q.write_text(header+adapted+'\nend AspisR1PathEnclosingCandidate\n');sha=lambda b:hashlib.sha256(b).hexdigest()
Path('/tmp/PathLaneEnclosingSlice.manifest.json').write_text(json.dumps({'raw_generated_path':str(p.relative_to(repo)),'raw_generated_sha256':sha(p.read_bytes()),'raw_declaration_sha256':sha(body.encode()),'adapted_declaration_sha256':sha(adapted.encode()),'module_sha256':sha(q.read_bytes()),'namespace':'AspisR1PathEnclosingCandidate','helper_reference_map':mapping,'inverse_recovers_exact_declaration':True,'generator_sha256':sha(Path(__file__).read_bytes())},indent=2)+'\n');print(sha(q.read_bytes()))
