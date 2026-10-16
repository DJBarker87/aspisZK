from pathlib import Path
import re,hashlib,json
repo=Path('/Users/dominic/ZK/.worktrees/100bit-spend-path');p=repo/'docs/research/100bit-spend-path-20261013/evidence/terminal-indexed-source-candidate-20261016/Funs.lean';s=p.read_text();name='pool_v1.pair_forest_semantic_terminal.public_digest_lanes';m=re.search(r'\bdef\s+'+re.escape(name)+r'(?=\s|\()',s);a=s.rfind('/-- ',0,m.start());b=s.index('\n/-- ',m.start());raw=s[a:b].rstrip()+'\n'
subs={'pool_v1.pair_forest_semantic_terminal.add_digest_binding':'AspisR1TerminalDigestBindingCandidate.add_digest_binding','pool_v1.pair_forest_semantic_terminal.public_digest_lanes_loop':'AspisR1TerminalDigestPublicLoop.Source.public_digest_lanes_loop'}
body=raw
for k,v in subs.items():body=body.replace(k,v)
q=Path('/tmp/DigestWrapperSource.lean');q.write_text('''import TerminalDigestPublicLoopSource

/-! Whole candidate public_digest_lanes wrapper. Only helper qualifications
are changed, with an inverse source map in the accompanying manifest. -/
open Aeneas Aeneas.Std Result
namespace AspisR1DigestWrapperCandidate
open AspisR1SelectedMaskProbe

'''+body+'\nend AspisR1DigestWrapperCandidate\n')
recovered=body
for k,v in sorted(subs.items(),key=lambda x:len(x[1]),reverse=True):recovered=recovered.replace(v,k)
assert recovered==raw
Path('/tmp/DigestWrapperSource.manifest.json').write_text(json.dumps({'raw_source':str(p.relative_to(repo)),'raw_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'declaration':name,'start_byte':len(s[:a].encode()),'end_byte':len(s[:b].encode()),'raw_block_sha256':hashlib.sha256(raw.encode()).hexdigest(),'substitutions':subs,'inverse_check':True,'output_sha256':hashlib.sha256(q.read_bytes()).hexdigest()},indent=2)+'\n');print(hashlib.sha256(q.read_bytes()).hexdigest())
