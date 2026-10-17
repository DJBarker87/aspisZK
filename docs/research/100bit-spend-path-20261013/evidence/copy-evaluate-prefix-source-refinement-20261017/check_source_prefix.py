from pathlib import Path
import re,json,hashlib,argparse
ap=argparse.ArgumentParser();ap.add_argument('--repo',type=Path,required=True);ap.add_argument('--row-source',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
funs=args.repo/'docs/research/100bit-spend-path-20261013/evidence/terminal-indexed-source-candidate-20261016/Funs.lean';raw=funs.read_text();a=raw.index('def pool_v1.pair_forest_copy_terminal.evaluate_with_selectors\n');b=raw.index('\n/--',a);block=raw[a:b];prefix=block[block.index('  let patterns ←'):block.index('  let active ←')]
s=args.row_source.read_text();a=s.index('def rowPrefix ');b=s.index('\ndef retainedRow ',a);definition=s[a:b];candidate=definition[definition.index('  let patterns ←'):definition.index('  ok {')]
owner_map={'AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.pattern_values':'pool_v1.pair_forest_copy_terminal.pattern_values','AspisR1CopyLinkLoopCandidate.pool_v1.pair_forest_copy_terminal.evaluate_with_selectors_loop':'pool_v1.pair_forest_copy_terminal.evaluate_with_selectors_loop'}
for new,old in owner_map.items():candidate=candidate.replace(new,old)
renames={'append_index':'index','a4':'pv','a5':'pw','a6':'cv','a7':'cw'}
for old,new in renames.items():prefix=re.sub(r'\b'+old+r'\b',new,prefix)
norm=lambda x:re.sub(r'\s+','',x)
assert norm(prefix)==norm(candidate),(prefix,candidate)
result={'raw_funs_sha256':hashlib.sha256(funs.read_bytes()).hexdigest(),'raw_evaluate_block_sha256':hashlib.sha256(block.encode()).hexdigest(),'row_source_sha256':hashlib.sha256(args.row_source.read_bytes()).hexdigest(),'owner_map':owner_map,'local_hygienic_rename_map':renames,'normalized_pre_active_prefix_identical':True,'scope':'Exact pre-active monadic fragment only. rowPrefix returns the same four arrays in the existing source row carrier. residualPrefix composes the actual checked copy_residual. Enclosing active call, error ordering, full exported evaluator and production runtime correspondence remain separate.'}
args.output.write_text(json.dumps(result,indent=2)+'\n');print('Exact pre-active source prefix matches after explicit owner/local-name map')
