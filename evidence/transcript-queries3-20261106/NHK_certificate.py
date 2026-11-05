"""Additive closure checks over the retained native/Lean/source/scan evidence."""
from pathlib import Path
import json,hashlib,re
E=Path(__file__).resolve().parent
STD={'propext','Classical.choice','Quot.sound'}
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def check(c):
 assert c['row']=='TX1:168' and c['status']=='CLOSED under (ah)'
 assert c['frozen_revision']=='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
 assert c['route']=='ah' and c['cohort']=='NGK_COMBINED_IMPORT'
 assert c['headline']=='AspisR1.RPx_Deployed.deployed' and c['semantic_slots']=={'digest':43,'error':44}
 assert c['export']=='AspisR1.NGP_TRANSCRIPT.actual_queries'
 assert c['producer']=='AspisR1.NHK_Invocation.producer'
 assert c['source_correspondence'] and c['native_environment']['graph_checked'] and c['native_environment']['lock_unchanged']
 assert c['native_environment']['offline'] and c['native_environment']['core_features']==['r0']
 assert c['native_environment']['kmx_sha256']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
 assert c['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64','lean_M':7000}
 assert 0<c['budget_used']['kani']<=70 and 0<c['budget_used']['lean_support']<=70 and c['budget_used']['extraction']==0
 assert c['domain']=={'row_max':95,'payload_max':8192,'native_state':'safe frozen Rust carriers; bounded scan; canonical masked words; inactive zeros'}
 assert c['trust']['classification']=='RECLASSIFICATION' and c['trust']['removed']==[] and c['trust']['added']==[]
 assert c['trust']['reviewed_transcription']=='queries_from_pairs / NHK_word_ref'
 assert c['audit']['raw_roots']==42 and c['audit']['fixtures']==8
 assert c['audit']['scan_exit']==0 and c['audit']['dangling']==c['audit']['incompatible_owners']==c['audit']['import_mismatches']==0
 assert set(c['audit']['axioms'])<=STD and not c['cold_release_replay'] and not c['security_target_established']
 assert c['native_contract']['positive']=='NHK_K034' and c['native_contract']['control']=='NHK_K035'
 assert c['native_contract']['modifies']==['scan','local log'] and c['native_contract']['same_poststate']
 assert c['membership']['lengths']==list(range(22)) and not c['membership']['missing_lengths']
 assert all(r['status']=='CHECKED_LOCAL_CALLEE' for r in c['membership']['cases'])
 assert len(c['membership']['cases'])==22 and [r['length'] for r in c['membership']['cases']]==list(range(22))
 for r in c['membership']['cases']:assert r['positive']!=r['control']
 assert c['invariants']==['validState','canonical18','inactive-zero','same cursor','same survivor list','same draw count']
 schedule=c['schedule'];assert schedule=={'same_invocation':True,'absorb_calls':1,'eager_pairs':8,'digest_attempts_returning':17,'post_last_word_stop':False,'block_end_success_selects_next_advance':True,'fallback_advance':7,'ordered_survivors':True,'unsuccessful_call_kept':True,'ideal_suffix_retained':True,'outcomes':['absorb fail','absorb div','pair fail','pair div','sampler success','sampler rejection']}
 assert c['boundary_producers']=='caller obligations; not replaced by success or whole-output hypotheses'
 for name,h in c['artifacts'].items():assert sha(E/name)==h,('artifact hash',name)
 membership=json.loads((E/'NHK_MEMBERSHIP_CALLEES.json').read_text());assert membership['cases']==c['membership']['cases'] and membership['missing_lengths']==[]
 contract=json.loads((E/'NHK_CONTRACT_PAIRS.json').read_text())[0];assert contract['positive']==c['native_contract']['positive'] and contract['control']==c['native_contract']['control']
 for a,positive in [('NHK_K034',True),('NHK_K035',False)]:
  r=json.loads((E/a/'receipt.json').read_text());raw=(E/a/'stdout.log').read_text()
  assert r['exit_status']==(0 if positive else 1) and 'timed out' not in raw and 'CBMC failed' not in raw
  assert ('VERIFICATION:- SUCCESSFUL' in raw) if positive else ('Failed Checks: |out|' in raw and re.search(r'\*\* 1 of \d+ failed',raw))
  s=(E/a/'sources/NHK_src/crates/aspis-core/src/NHK_harness.rs').read_text();assert '#[kani::modifies(scan,log)]' in s and '#[kani::proof_for_contract(NHK_word_step)]' in s
  assert 'static mut' not in s and 'stub_verified' not in s
 reused=json.loads((E/'NHK_REVALIDATED_REUSE.json').read_text());assert reused['status']=='PASS' and reused['pairs']==35 and reused['new_tool_attempts']==0
 edges=json.loads((E/'NHK_EDGES.json').read_text());assert edges['root']=='TX1:168' and len(edges['internal_edges'])==8 and all(r['status']=='CLOSED' for r in edges['internal_edges'])
 matrix=json.loads((E/'NHK_NATIVE_MATRIX.json').read_text());assert matrix['no_writable_static'] and matrix['no_function_pointer_property'] and matrix['no_field_multiplication'] and matrix['no_sha_unwinding']
 audit=json.loads((E/'NHK_AUDIT.json').read_text());assert audit['status']=='PASS' and audit['all_raw_roots_standard'] and audit['raw_roots']==42
 for mode,n in [('batch0',1),('batch1',41)]:
  r=json.loads(next((E/'NHK_audit'/mode).glob('*.json')).read_text());assert r['exit_status']==0 and len(r['results'])==n
  for row in r['results']:assert set(row['walked_axioms'])<=STD and row['equal']
 rows=[json.loads(l) for l in (E/'NHK_LOADED_scan.jsonl').read_text().splitlines()]
 assert len(rows)==c['audit']['modules']
 assert all(not r['dangling'] and not r['duplicate_owners'] and r['imports_match'] for r in rows)
 manifest=json.loads((E/'NHK_AUDIT_ROOTS.json').read_text());assert c['export'] in manifest['groups'][1] and c['producer'] in manifest['groups'][1]
 correspondence=json.loads((E/'NHK_CORRESPONDENCE.json').read_text());assert correspondence['source_checks'] and len(correspondence['checks'])==23
 # Every listed theorem source is exactly a successful archived compilation,
 # rather than edited after its printed audit.
 for module,attempt in c['successful_modules'].items():
  p=E/attempt/'receipt.json';r=json.loads(p.read_text());assert r['exit_status']==0
  assert sha(E/(module+'.lean'))==r['source_hashes']['NHK_generated/'+module+'.lean']
 return True
if __name__=='__main__':
 c=json.loads((E/'NHK_CLOSED.json').read_text());assert check(c);print(json.dumps(dict(status='PASS',row=c['row'],route=c['route'])))
