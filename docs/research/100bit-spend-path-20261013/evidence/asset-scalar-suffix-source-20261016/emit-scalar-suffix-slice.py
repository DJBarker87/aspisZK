from pathlib import Path
import json,hashlib
repo=Path('/Users/dominic/ZK/.worktrees/100bit-spend-path');p=repo/'docs/research/100bit-spend-path-20261013/evidence/terminal-indexed-source-candidate-20261016/Funs.lean';s=p.read_text()
a=s.index('  let q ← Array.index_usize openings.z 1#usize',s.index('def pool_v1.pair_forest_semantic_terminal.semantic_packed'));b=s.index('\n/-- ',a)
raw=s[a:b].rstrip()+'\n'
replacements={'pool_v1.pair_forest_semantic_terminal.scalar_lanes':'AspisR1ScalarCandidate.pool_v1.pair_forest_semantic_terminal.scalar_lanes','pool_v1.pair_forest_semantic_terminal.add_preweighted':'AspisR1PreweightedCandidate.pool_v1.pair_forest_semantic_terminal.add_preweighted','packed5':'packed'}
body=raw
for x,y in replacements.items():body=body.replace(x,y)
params='''  (public1 : pool_v1.pair_forest_semantic_terminal.SemanticPublic)
  (openings : state_only_poseidon.StateOnlyPoseidonOpenings)
  (selectors : pool_v1.pair_forest_copy_terminal.Selectors)'''
cut=body.index('  AspisR1PreweightedCandidate.pool_v1.pair_forest_semantic_terminal.add_preweighted packed 92#usize')
values=body[:cut]+'  ok scalars\n'
header='''import ScalarLaneSlice
import SelectorValueLaneGeneratedSlice
import PreweightedWrapperSemantic

/-! Source-order suffix cut from the sealed generated semantic_packed body.
The scalar_suffix body retains the exact suffix, with recorded name changes.
scalar_values cuts only the final packing call; its relation is proved separately. -/
open Aeneas Aeneas.Std Result ControlFlow Error
namespace AspisR1ScalarSuffixCandidate
open AspisR1SelectedMaskProbe

'''
out=header+'def scalar_values\n'+params+' : Result (Array field.QM31 2#usize) := do\n'+values+'\ndef scalar_suffix\n  (packed : Array field.QM31 24#usize)\n'+params+' : Result (Array field.QM31 24#usize) := do\n'+body+'\nend AspisR1ScalarSuffixCandidate\n'
q=Path('/tmp/ScalarSuffixSlice.lean');q.write_text(out);sha=lambda x:hashlib.sha256(x).hexdigest()
Path('/tmp/ScalarSuffixSlice.manifest.json').write_text(json.dumps({'raw_source':str(p.relative_to(repo)),'raw_sha256':sha(p.read_bytes()),'source_declaration':'pool_v1.pair_forest_semantic_terminal.semantic_packed','start_byte':len(s[:a].encode()),'end_byte':len(s[:b].encode()),'retained_suffix_sha256':sha(raw.encode()),'suffix_substitutions':replacements,'values_cut':'replace final add_preweighted packed5 92#usize scalars with ok scalars','module_sha256':sha(q.read_bytes())},indent=2)+'\n')
print(sha(q.read_bytes()))
