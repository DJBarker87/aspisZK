from pathlib import Path
import re,json,hashlib
repo=Path('/Users/dominic/ZK/.worktrees/100bit-spend-path');p=repo/'docs/research/100bit-spend-path-20261013/evidence/terminal-indexed-source-candidate-20261016/Funs.lean';s=p.read_text();name='pool_v1.pair_forest_semantic_terminal.initial_variant_selectors'
m=re.search(r'\bdef\s+'+re.escape(name)+r'(?=\s|:)',s);a=s.rfind('/-- ',0,m.start());b=s.index('\n/-- ',m.start());block=s[a:b].rstrip()+'\n'
out='''import OccupancyGeneratedSlice

/-! Exact generated initial-variant selector helper, sharing the already
retained actual CompiledVariant type. Namespace/module framing only. -/
open Aeneas Aeneas.Std Result ControlFlow Error
namespace AspisR1InitialVariantCandidate
open AspisR1SelectedMaskProbe

'''+block+'\nend AspisR1InitialVariantCandidate\n';q=Path('/tmp/InitialVariantSlice.lean');q.write_text(out)
Path('/tmp/InitialVariantSlice.manifest.json').write_text(json.dumps({'source':str(p.relative_to(repo)),'source_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'name':name,'start_byte':len(s[:a].encode()),'end_byte':len(s[:b].encode()),'retained_sha256':hashlib.sha256(block.encode()).hexdigest(),'namespace':'AspisR1InitialVariantCandidate','body_substitutions':{},'module_sha256':hashlib.sha256(q.read_bytes()).hexdigest()},indent=2)+'\n');print(hashlib.sha256(q.read_bytes()).hexdigest())
