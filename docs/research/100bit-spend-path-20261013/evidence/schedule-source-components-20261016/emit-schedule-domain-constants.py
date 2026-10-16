from pathlib import Path
import re,json,hashlib
repo=Path('/Users/dominic/ZK/.worktrees/100bit-spend-path');p=repo/'docs/research/100bit-spend-path-20261013/evidence/terminal-indexed-source-candidate-20261016/Funs.lean';s=p.read_text();blocks=[];rows=[]
for name in ['spend.DOMAIN_OWNER_KEY','spend.DOMAIN_NOTE','spend.DOMAIN_NULLIFIER']:
 m=re.search(r'\bdef\s+'+re.escape(name)+r'(?=\s|:)',s);a=s.rfind('/-- ',0,m.start());b=s.index('\n/-- ',m.start());block=s[a:b].rstrip()+'\n';blocks.append(block);rows.append({'name':name,'start_byte':len(s[:a].encode()),'end_byte':len(s[:b].encode()),'retained_sha256':hashlib.sha256(block.encode()).hexdigest()})
out='''import SelectorValueLaneGeneratedSlice

/-! Exact generated domain constants used by initial schedule lanes.
Only the module framing and isolating namespace are changed. -/
open Aeneas Aeneas.Std Result
namespace AspisR1ScheduleDomainCandidate
open AspisR1SelectedMaskProbe

'''+ '\n'.join(blocks)+'\nend AspisR1ScheduleDomainCandidate\n';q=Path('/tmp/ScheduleDomainConstants.lean');q.write_text(out)
Path('/tmp/ScheduleDomainConstants.manifest.json').write_text(json.dumps({'raw_source':str(p.relative_to(repo)),'raw_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'declarations':rows,'body_substitutions':{},'namespace':'AspisR1ScheduleDomainCandidate','module_sha256':hashlib.sha256(q.read_bytes()).hexdigest()},indent=2)+'\n');print(hashlib.sha256(q.read_bytes()).hexdigest())
