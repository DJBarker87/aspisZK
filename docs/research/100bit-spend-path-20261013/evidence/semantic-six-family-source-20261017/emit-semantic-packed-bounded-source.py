from pathlib import Path
import re,json,hashlib
repo=Path('/Users/dominic/ZK/.worktrees/100bit-spend-path');p=repo/'docs/research/100bit-spend-path-20261013/evidence/terminal-indexed-source-candidate-20261016/Funs.lean';s=p.read_text();name='pool_v1.pair_forest_semantic_terminal.semantic_packed';m=re.search(r'\bdef '+re.escape(name)+r'\s',s);a=m.start();b=s.index('\n/-- ',a);raw=s[a:b].strip()+'\n'
subs={
'pool_v1.pair_forest_semantic_terminal.add_schedule_lanes':'AspisR1ScheduleEnclosingCandidate.pool_v1.pair_forest_semantic_terminal.add_schedule_lanes',
'pool_v1.pair_forest_semantic_terminal.add_path_lanes':'AspisR1PathEnclosingCandidate.pool_v1.pair_forest_semantic_terminal.add_path_lanes',
'pool_v1.pair_forest_semantic_terminal.add_value_lanes':'AspisR1ValueLaneCandidate.pool_v1.pair_forest_semantic_terminal.add_value_lanes',
'pool_v1.pair_forest_semantic_terminal.public_digest_lanes':'AspisR1DigestWrapperBoundedCandidate.pool_v1.pair_forest_semantic_terminal.public_digest_lanes',
'pool_v1.pair_forest_semantic_terminal.add_preweighted':'AspisR1PreweightedCandidate.pool_v1.pair_forest_semantic_terminal.add_preweighted',
'pool_v1.pair_forest_semantic_terminal.scalar_lanes':'AspisR1ScalarCandidate.pool_v1.pair_forest_semantic_terminal.scalar_lanes'}
body=raw
for old,new in subs.items():body=body.replace(old,new)
inverse=body
for old,new in sorted(subs.items(),key=lambda kv:len(kv[1]),reverse=True):inverse=inverse.replace(new,old)
assert inverse==raw
out=Path('/tmp/SemanticPackedBoundedSource.lean');out.write_text('''import SemanticPackedPrefix
import ScalarSuffixPacking
import DigestWrapperComposition

/-! Full semantic_packed caller with shared proved helper owners. The digest
callee is the explicit bounded implementation candidate; full modified-Rust
re-extraction and release correspondence remain separate. -/
open Aeneas Aeneas.Std Result
namespace AspisR1SemanticPackedBoundedCandidate
open AspisR1SelectedMaskProbe

'''+body+'\nend AspisR1SemanticPackedBoundedCandidate\n')
Path('/tmp/SemanticPackedBoundedSource.manifest.json').write_text(json.dumps({'raw_source':str(p.relative_to(repo)),'raw_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'declaration':name,'start_byte':len(s[:a].encode()),'end_byte':len(s[:b].encode()),'raw_block_sha256':hashlib.sha256(raw.encode()).hexdigest(),'substitutions':subs,'inverse_check':True,'digest_callee_is_bounded_candidate_not_original_intrinsic':True,'whole_modified_rust_reextraction_proved':False,'output_sha256':hashlib.sha256(out.read_bytes()).hexdigest()},indent=2)+'\n');print(hashlib.sha256(out.read_bytes()).hexdigest())
