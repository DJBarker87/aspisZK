#!/usr/bin/env python3
"""Offline integrity checks for the saved R374 polynomial API inventory."""
import hashlib,json,re
from pathlib import Path
ROOT=Path(__file__).resolve().parent
fail=[]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def check(cond,msg):
 if not cond:fail.append(msg)
inv=json.loads((ROOT/'inventory.json').read_text())
check(inv['start_module']=='AspisV8R19.SourceStatementPoints','wrong root module')
check(inv['local_recursive_aspis_module_count']==63,'recursive module count differs')
check(not inv['missing_local_modules'],'missing local modules')
check(inv['all_host_sources_byte_match_local'],'pinned host Aspis sources differ from local')
check(inv['all_aspis_olean_present'],'one or more Aspis cache objects missing')
check(inv['external_import_count']==25,'external import count differs')
check(all(x['source_exists'] and x['olean_exists'] for x in inv['external_direct_imports']),'external dependency source/cache missing')
for row in inv['aspis_modules']:
 p=Path('/Users/dominic/ZK/.worktrees/ZK-v8-r21-public-arithmetic-20260922')/row['path']
 check(p.is_file() and sha(p)==row['sha256'],f'local Aspis source mismatch: {row["module"]}')
 check(row['host_source_matches_local'] and row['host_olean_exists'],f'host source/cache audit mismatch: {row["module"]}')
expected={
 'Mathlib.Algebra.Polynomial.BigOperators':('3855de2b1a1f005bb6769a8e6c3813a2220881457d43fe0a2604a3b2f7d94b55','61cedfb72e1df9e710242f654d5b05434ae5df7fcdbc16d2f0820fcd460fb989'),
 'Mathlib.Algebra.Polynomial.Degree.Operations':('6cf6ab951454822af7f2e4a926dc326078ef2431ed579b8b02ac7442c82b84a3','5afab05643ab5eec60f9740a23c12c4d3190ebb12568d2f03dcfbfeeef81fa97'),
 'Mathlib.Algebra.Polynomial.Degree.Defs':('f804f89872524b7559eccc71a39fb082c497e8a7fd8cf2c50aeb7a0a48255b82','dc3c8c56bf1adecb02a0c5645119855f3ffc1f19f33fb171619b20379b728e87'),
 'Mathlib.Algebra.Polynomial.Eval.Defs':('324a019feeb6134861ed550dcbdff5425ff062b8894024ef852643d5dc873a7b','3dd44d30060a79b4546309de79711ab1b630ee5701e01524d2d496df7928f40f')}
api={r['module']:r for r in inv['mathlib_api_sources']}
check(set(api)==set(expected),'API module set mismatch')
for name,(src_hash,olean_hash) in expected.items():
 row=api[name];p=ROOT/row['local_copy']
 check(p.is_file() and sha(p)==src_hash==row['source_sha256'],f'Mathlib source copy mismatch: {name}')
 check(row['olean_sha256']==olean_hash,f'Mathlib cache hash mismatch: {name}')
source=(ROOT/'mathlib-source/Mathlib/Algebra/Polynomial/BigOperators.lean').read_text()
for name in ('natDegree_sum_le','natDegree_sum_le_of_forall_le','natDegree_prod_le'):
 check(re.search(r'\b(?:theorem|lemma)\s+'+name+r'\b',source) is not None,f'expected actual API absent: {name}')
for absent in ('natDegree_finset_prod','natDegree_finset_sum_le'):
 check(re.search(r'\b(?:theorem|lemma|def)\s+'+absent+r'\b',source) is None,f'unexpected named API: {absent}')
summary={'status':'PASS' if not fail else 'FAIL','local_aspis_modules':len(inv['aspis_modules']),'external_imports':len(inv['external_direct_imports']),'mathlib_api_sources':len(inv['mathlib_api_sources']),'failures':fail}
print(json.dumps(summary,indent=2))
if fail:raise SystemExit(1)
