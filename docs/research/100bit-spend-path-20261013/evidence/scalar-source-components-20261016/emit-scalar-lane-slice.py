from pathlib import Path
import hashlib,json,re
repo=Path('/Users/dominic/ZK/.worktrees/100bit-spend-path');p=repo/'docs/research/100bit-spend-path-20261013/evidence/terminal-indexed-source-candidate-20261016/Funs.lean';s=p.read_text();name='pool_v1.pair_forest_semantic_terminal.scalar_lanes';m=re.search(r'\bdef\s+'+re.escape(name)+r'(?=\s|:)',s);a=s.rfind('/-- ',0,m.start());b=s.index('\n/-- ',m.start());block=s[a:b].rstrip()+'\n'
out='''import OccupancyGeneratedSlice

/-! Whole actual generated scalar_lanes helper, preserving both variant and
withdrawal-presence branches. Namespace/module framing only. -/
open Aeneas Aeneas.Std Result ControlFlow Error
namespace AspisR1ScalarCandidate
open AspisR1SelectedMaskProbe

'''+block+'\nend AspisR1ScalarCandidate\n';q=Path('/tmp/ScalarLaneSlice.lean');q.write_text(out);sha=lambda b:hashlib.sha256(b).hexdigest()
Path('/tmp/ScalarLaneSlice.manifest.json').write_text(json.dumps({'raw_source':str(p.relative_to(repo)),'raw_sha256':sha(p.read_bytes()),'name':name,'start_byte':len(s[:a].encode()),'end_byte':len(s[:b].encode()),'retained_sha256':sha(block.encode()),'body_substitutions':{},'namespace':'AspisR1ScalarCandidate','module_sha256':sha(q.read_bytes())},indent=2)+'\n');print(sha(q.read_bytes()))
