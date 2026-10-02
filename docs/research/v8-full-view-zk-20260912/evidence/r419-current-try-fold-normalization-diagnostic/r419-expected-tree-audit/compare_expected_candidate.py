"""Compare the frozen original-derived expected tree with the native candidate."""
import hashlib, importlib.util, json, pathlib, resource, subprocess, sys, time

start=time.monotonic()
here=pathlib.Path(__file__).resolve().parent
root=here.parents[2]
candidate=here.parent/'runs/aspis-r419-candidate-1790967913444473000/candidate.llbc'
tree=here/'expected-delta-v2/R419ExpectedDecodedFromOriginalR396-v2.json'
manifest_path=here/'expected-delta-v2/manifest.json'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads(manifest_path.read_text())
assert manifest['candidate_read'] is False
assert manifest['original_sha256']=='399020435e94aaa7135c06d68445e9b936bd22fe6d1e1d197ee708d448d584ae'
assert sha(tree)==manifest['expected_tree_sha256']=='5867c46c3fed0a126381415a139bf08a7dcd1717dc06dcef032571b72d4c7d6e'
assert sha(candidate)=='7f82eaabe855e89d735b21f9af5f6a983abea6b2f4d93d4b8bae747abd2829e2'
spec=importlib.util.spec_from_file_location('compare_hardened',here/'compare_llbc_hardened.py')
cmp=importlib.util.module_from_spec(spec);spec.loader.exec_module(cmp)
expected=json.loads(tree.read_text())
raw=json.loads(candidate.read_text());table={}
cmp.collect_hashcons(raw,table)
actual=cmp.decode(raw,table)
diffs=cmp.diff_paths(expected,actual)
usage=resource.getrusage(resource.RUSAGE_SELF)
evidence=[manifest_path,tree,here/'expected-delta-v2/operation-trace.json',
          here/'expected_from_original_v2.py',here/'expected-delta-v2-audit.json',
          here/'expected-visitor-v2-negative-cases.json',here/'compare_llbc_hardened.py',
          candidate,pathlib.Path(__file__)]
result={'classification':'Exact full decoded AST equality with the lead-prescribed, original-derived type transformation; not a source execution or security theorem',
        'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),
        'target':'R419 independent expected decoded tree vs fresh native candidate copy',
        'baseline_sha256':manifest['original_sha256'],'candidate_sha256':sha(candidate),
        'independent_expected_tree_sha256':sha(tree),'expected_equals_candidate':not diffs,
        'remaining_diff_count':len(diffs),'remaining_diffs':diffs,
        'exit_status':0 if not diffs else 1,'wall_time_seconds':time.monotonic()-start,
        'peak_rss_bytes':usage.ru_maxrss if sys.platform=='darwin' else usage.ru_maxrss*1024,
        'swaps':usage.ru_nswap,'print_axioms':'Not applicable: structural audit, no Lean theorem.',
        'expected_generation_read_candidate':False,
        'evidence_sha256':{str(p.relative_to(root)):sha(p) for p in evidence},
        'proved_boundary':'The candidate has exactly the prescribed capture-avoiding type substitution/reindexing, constrained binder/equality removal and corresponding nine generic argument deletions across the entire decoded AST. No other decoded data differ.',
        'first_remaining_proposition':'Justify admissible original/new generic instantiation correspondence and consume the normalized actual fold in translation and a focused source execution proof; full freeze callback, probability, privacy and soundness remain open.'}
out=here/'expected-candidate-comparison.json'
assert not out.exists(),'preserve prior comparison; use a new version if inputs change'
out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['expected_equals_candidate','remaining_diff_count','exit_status','wall_time_seconds','peak_rss_bytes','swaps']},indent=2))
raise SystemExit(result['exit_status'])
