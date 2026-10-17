from pathlib import Path
import hashlib,json
p=Path('/Users/dominic/ZK/.worktrees/100bit-spend-path/docs/research/100bit-spend-path-20261013/evidence/terminal-indexed-source-candidate-20261016/Funs.lean');s=p.read_text();fn=s.index('def pool_v1.pair_forest_semantic_terminal.composition_parts\n');a=s.index('      let prepared_theta ←',fn);b=s.index('\n    | core.ops.control_flow.ControlFlow.Break',a);raw=s[a:b];body='\n'.join(line[6:] for line in raw.splitlines())+'\n';body=body.replace('copy.residual','seed').replace('copy.active','active');inv='\n'.join('      '+line for line in body.rstrip('\n').replace('seed','copy.residual').replace('active','copy.active').splitlines());assert inv==raw
header='''import Aeneas
import Aeneas.Tactic.RustAttributes
import TerminalCompositionPolynomial
import SelectedClaimProofs

/-! Exact post-copy tail of the retained composition_parts source. Local
parameters are the values bound before the source cut; reachability and source
binding of those inputs are separate enclosing-caller obligations. -/
set_option autoImplicit false
namespace AspisR1.CompositionPartsTail
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
abbrev QM := field.QM31
abbrev Error := pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1
abbrev Output := QM × (Array QM 16#usize) × (Array QM 10#usize) × QM × QM × QM

def run (semantic : Array QM 24#usize) (poseidon : Array QM 4#usize)
    (theta seed active : QM) (claims : Array QM 84#usize)
    (a : Array QM 16#usize) (mask_only : Array QM 10#usize) (h1_z : QM) :
    Result (core.result.Result Output Error) := do
'''
types_path=p.with_name('Types.lean');ts=types_path.read_text();ta=ts.index('@[discriminant isize]\ninductive pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1');tb=ts.index('\n/--',ta);ty=ts[ta:tb].strip()+'\n';header=header.replace('namespace AspisR1.CompositionPartsTail', 'namespace AspisR1CompositionTailCandidateTypes\nopen Aeneas Aeneas.Std Result\n'+ty+'end AspisR1CompositionTailCandidateTypes\n\nnamespace AspisR1.CompositionPartsTail').replace('abbrev Error := pool_v1.', 'abbrev Error := AspisR1CompositionTailCandidateTypes.pool_v1.')
out=Path('/tmp/CompositionPartsTailSource.lean');out.write_text(header+'\n'.join('  '+line for line in body.rstrip('\n').splitlines())+'\n\nend AspisR1.CompositionPartsTail\n');Path('/tmp/CompositionPartsTailSource.manifest.json').write_text(json.dumps({'raw_types_sha256':hashlib.sha256(types_path.read_bytes()).hexdigest(),'error_type_block_sha256':hashlib.sha256(ty.encode()).hexdigest(),'error_type_exact_copy':True,'error_type_namespace':'AspisR1CompositionTailCandidateTypes','raw_funs_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'declaration':'pool_v1.pair_forest_semantic_terminal.composition_parts','source_start_byte':len(s[:a].encode()),'source_end_byte':len(s[:b].encode()),'raw_block_sha256':hashlib.sha256(raw.encode()).hexdigest(),'substitutions':{'copy.residual':'seed','copy.active':'active'},'inverse_check':True,'reachability_proved':False,'output_sha256':hashlib.sha256(out.read_bytes()).hexdigest()},indent=2)+'\n');print(hashlib.sha256(out.read_bytes()).hexdigest())
