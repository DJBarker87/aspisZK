from pathlib import Path
import re,hashlib,json,argparse
ap=argparse.ArgumentParser();ap.add_argument("--repo",required=True,type=Path);ap.add_argument("--output",required=True,type=Path);ap.add_argument("--check",action="store_true");args=ap.parse_args()
repo=args.repo;p=repo/'docs/research/100bit-spend-path-20261013/evidence/terminal-indexed-source-candidate-20261016';f=(p/'Funs.lean').read_text();t=(p/'Types.lean').read_text()
def block(s,pattern):
 m=re.search(pattern,s);assert m,pattern;return s[m.start():s.index('\n/--',m.start())].strip()+'\n'
ty=block(t,r'structure pool_v1\.pair_forest_copy_terminal\.PoolV1PairForestCompiledCopyTerminalV1\b')
eval=block(f,r'def pool_v1\.pair_forest_copy_terminal\.evaluate_with_selectors\b');raw=eval
owner_map={'pool_v1.pair_forest_copy_terminal.Selectors)':'AspisR1SelectedMaskProbe.pool_v1.pair_forest_copy_terminal.Selectors)','pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1':'AspisR1CopyLinkWeightCandidate.pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1','pool_v1.pair_forest_copy_terminal.pattern_values':'AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.pattern_values','pool_v1.pair_forest_copy_terminal.evaluate_with_selectors_loop':'AspisR1CopyLinkLoopCandidate.pool_v1.pair_forest_copy_terminal.evaluate_with_selectors_loop','pool_v1.pair_forest_copy_terminal.copy_residual':'AspisR1CopyResidualCandidate.pool_v1.pair_forest_copy_terminal.copy_residual'}
for old,new in owner_map.items():eval=eval.replace(old,new)
text='''import AspisR1.CopyEvaluateRowExact
import AspisR1SelectedMaskProbe.ActiveMaskBasisSourceSlice

/-! Candidate Copy evaluator with the selected active-basis feature route.
All source evaluator operations/order are retained; helper owners are shared. -/
set_option autoImplicit false
namespace AspisR1.CopyEvaluatorSource
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe

'''+ty+'''
/-- The active route selected by the candidate's existing basis feature. -/
def pool_v1.pair_forest_copy_terminal.Selectors.active
    (self : AspisR1SelectedMaskProbe.pool_v1.pair_forest_copy_terminal.Selectors) :
    Result field.QM31 := do
  AspisR1SelectedMaskProbe.pool_v1.pair_forest_copy_terminal.Selectors.active_mask_basis self

'''+eval+'\nend AspisR1.CopyEvaluatorSource\n'
p=args.output/'CopyEvaluatorSource.lean'
if args.check:assert p.read_text()==text
else:p.parent.mkdir(parents=True,exist_ok=True);p.write_text(text)
manifest_text=json.dumps({'raw_funs_sha256':hashlib.sha256(f.encode()).hexdigest(),'raw_types_sha256':hashlib.sha256(t.encode()).hexdigest(),'raw_evaluator_block_sha256':hashlib.sha256(raw.encode()).hexdigest(),'source_sha256':hashlib.sha256(text.encode()).hexdigest(),'owner_map':owner_map,'selected_feature':'pool-v1-pair-forest-active-mask-basis-audit','scope':'Candidate source route; feature adoption, rebuilt artifact and CU gate remain open. No production Rust edits.'},indent=2)+'\n'
mp=args.output/'source-map.json'
if args.check:assert mp.read_text()==manifest_text
else:mp.write_text(manifest_text)
print(hashlib.sha256(text.encode()).hexdigest())
