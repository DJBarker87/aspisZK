from pathlib import Path
import re, hashlib, json
root=Path('/tmp/terminal-indexed-loops-candidate-20261016-v3-local')

def blocks(path):
 s=Path(path).read_text()
 # header and namespace framing
 n=s.index('namespace AspisR1SelectedMaskProbe')
 body=s[n+len('namespace AspisR1SelectedMaskProbe'):]
 # each generated declaration block starts at comment marker
 starts=[m.start() for m in re.finditer(r'/--',body)]
 out=[]
 for j,a in enumerate(starts):
  b=starts[j+1] if j+1<len(starts) else body.find('\nend AspisR1SelectedMaskProbe',a)
  chunk=body[a:b]
  # select target via fully-qualified Rust declaration comment or actual declaration
  out.append(chunk)
 return out

def choose(path, names):
 out=[]
 for nm in names:
  matches=[b for b in blocks(path) if nm in b.split('\n',1)[0] or re.search(r'\b(?:def|structure|inductive)\s+'+re.escape(nm)+r'\b',b)]
  if len(matches)!=1:
   raise RuntimeError((nm,len(matches),[x[:180] for x in matches]))
  out.append(matches[0].rstrip())
 return out
T=root/'Types.lean'; F=root/'Funs.lean'
types=['pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1','pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1','pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1','pool_v1.pair_forest_semantic_terminal.CompiledVariant','pool_v1.pair_forest_semantic_terminal.SemanticPublic']
funs=['field.M31.ZERO','field.CM31.ZERO','field.CM31.from_m31','field.QM31.from_cm31','poseidon2.DIGEST_ELEMS','pool_v1.pair_forest_semantic_terminal.lift_m31','pool_v1.pair_forest_semantic_terminal.occupancy_lanes_literal_loop','pool_v1.pair_forest_semantic_terminal.occupancy_lanes_literal','pool_v1.pair_forest_semantic_terminal.variant_expected_output','pool_v1.pair_forest_semantic_terminal.OUTPUT_OCCUPANCY_ROW','pool_v1.pair_forest_semantic_terminal.INPUT_OCCUPANCY_ROW','pool_v1.pair_forest_semantic_terminal.add_occupancy_lanes']
tb=choose(T,types); fb=choose(F,funs)
header='''import Aeneas.Std\nimport Aeneas.Tactic.RustAttributes\nimport Aeneas.Data.Discriminant\nimport AspisR1SelectedMaskProbe.Types\nimport AspisR1SelectedMaskProbe.Funs\nimport SelectorSourceSlice\nimport SelectorValueLaneLoops012Slice\nimport PreweightedWrapperSemantic\n\nopen Aeneas Aeneas.Std Result ControlFlow Error\nset_option linter.dupNamespace false\nset_option linter.hashCommand false\nset_option linter.unusedVariables false\nnoncomputable section\nnamespace AspisR1SelectedMaskProbe\n\n'''
# alias gives isolated extraction module the generated same-name target from the already-proved indexed candidate.
alias='''/-- Module-split adapter: occupancy source calls the existing separately sliced add_preweighted target. -/\ndef pool_v1.pair_forest_semantic_terminal.add_preweighted {N : Std.Usize}\n  (packed : Array field.QM31 24#usize) (start : Std.Usize)\n  (values : Array field.QM31 N) : Result (Array field.QM31 24#usize) :=\n  AspisR1PreweightedCandidate.pool_v1.pair_forest_semantic_terminal.add_preweighted\n    packed start values\n\n'''
out=header+'\n\n'.join(tb)+'\n\n'+alias+'\n\n'.join(fb)+'\n\nend AspisR1SelectedMaskProbe\nend\n'
Path('/tmp/OccupancyGeneratedSlice.lean').write_text(out)
manifest={'source':str(F),'source_sha256':hashlib.sha256(F.read_bytes()).hexdigest(),'types_source':str(T),'types_sha256':hashlib.sha256(T.read_bytes()).hexdigest(),'selected_types':types,'selected_funs':funs,'output':'/tmp/OccupancyGeneratedSlice.lean','output_sha256':hashlib.sha256(out.encode()).hexdigest(),'note':'Selected declaration blocks copied byte-for-byte; imports/prelude and one explicit module-split adapter are glue.'}
Path('/tmp/OccupancyGeneratedSlice.manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(manifest['output_sha256'])
