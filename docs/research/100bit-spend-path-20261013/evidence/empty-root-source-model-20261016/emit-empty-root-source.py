from pathlib import Path
import re,hashlib,json
repo=Path('/Users/dominic/ZK/.worktrees/100bit-spend-path');p=repo/'docs/research/100bit-spend-path-20261013/evidence/terminal-indexed-source-candidate-20261016/Funs.lean';s=p.read_text();blocks=[];entries=[]
for name in ['field.M31_constructor','pool_v1.pair_forest_semantic_terminal.constants.POOL_V1_PAIR_EMPTY_ROOTS_V1','pool_v1.pair_forest_semantic_terminal.empty_root']:
 m=re.search(r'\bdef\s+'+re.escape(name)+r'(?=\s|:)',s);a=s.rfind('/-- ',0,m.start());b=s.index('\n/-- ',m.start());block=s[a:b].rstrip()+'\n';blocks.append(block);entries.append({'name':name,'start_byte':len(s[:a].encode()),'end_byte':len(s[:b].encode()),'sha256':hashlib.sha256(block.encode()).hexdigest()})
q=Path('/tmp/EmptyRootSource.lean');q.write_text('''import OccupancyGeneratedSlice
import SelectorArrayMapSuccess

/-! Exact frozen table and empty_root helper from the sealed candidate.
Namespace framing only; original source declarations are byte-for-byte. -/
open Aeneas Aeneas.Std Result
namespace AspisR1EmptyRootCandidate
open AspisR1SelectedMaskProbe

'''+ '\n'.join(blocks)+'\nend AspisR1EmptyRootCandidate\n')
Path('/tmp/EmptyRootSource.manifest.json').write_text(json.dumps({'raw_source':str(p.relative_to(repo)),'raw_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'namespace':'AspisR1EmptyRootCandidate','body_substitutions':{},'blocks':entries,'output_sha256':hashlib.sha256(q.read_bytes()).hexdigest()},indent=2)+'\n')
print(hashlib.sha256(q.read_bytes()).hexdigest())
