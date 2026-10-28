from pathlib import Path
import json,hashlib,re,subprocess
E=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
pairs=[(4,5,'parts_store'),(6,7,'powers_final_iteration'),(8,9,'powers_continue_prefix'),(10,11,'LPo_decode_words'),(12,13,'LPk_byte_decode'),(14,15,'LPk_from_fn_order_word')]
rows=[]
for pos,neg,h in pairs:
 a=f'KNF_K{pos:03}';b=f'KNF_K{neg:03}'
 sa=(E/'sources'/(a+'.rs')).read_text();sb=(E/'sources'/(b+'.rs')).read_text()
 assert sa.replace('const KNF_XOR:u32=0;','const KNF_XOR:u32=1;')==sb
 logs=[(E/x/'stdout.log').read_text() for x in [a,b]]
 assert 'VERIFICATION:- SUCCESSFUL' in logs[0]
 assert 'Failed Checks: assertion failed: actual == expected ^ KNF_XOR' in logs[1]
 assert len(re.findall(r'Failed Checks:',logs[1]))==1
 assert re.search(r'\*\* 1 of \d+ failed',logs[1])
 rows.append(dict(harness=h,positive=a,control=b,positive_source_sha256=sha(sa.encode()),control_source_sha256=sha(sb.encode()),sole_failure='assertion failed: actual == expected ^ KNF_XOR'))
(E/'KNF_PAIRS.json').write_text(json.dumps(rows,indent=2)+'\n')
receipts=[]
for n in range(1,16):
 a=f'KNF_K{n:03}';rc=json.loads((E/a/'receipt.json').read_text());g=json.loads((E/(a+'-graph.json')).read_text());ad=json.loads((E/(a+'-reservation.json')).read_text())
 assert ad['allowed'] is True
 assert g['allowed'] and g['unchanged'] and g['lock_before']==g['lock_after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
 assert g['resolved_features']
 assert rc['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert int(rc['swaps'])==0
 receipts.append(dict(attempt=a,harness=rc['selected_harness'],exit=rc['exit_status'],wall_seconds=rc['wall_seconds'],peak_rss_kib=int(rc['peak_rss_kib']),swap=rc['swaps'],revision=rc['source_revision'],classification=json.loads((E/a/'classification.json').read_text())['result']))
(E/'KNF_RUNS.json').write_text(json.dumps(dict(kani_attempts=15,kani_budget=50,lean_attempts=0,lean_budget=30,optimized_rust_attempts=0,optimized_rust_budget=5,rows=receipts),indent=2)+'\n')
canonical=[]
for line in (E.parent/'native-featparity-20261028/NCS_I002-stdout.log').read_text().splitlines():
 try:j=json.loads(line)
 except ValueError:continue
 if j.get('label')=='library-deployed':canonical=j['nodes']
assert canonical
core=next(n for n in canonical if n['name']=='aspis-core');assert core['features']==['r0']
file_audits=[]
for src,dst in [('crates/aspis-core/src/field.rs','KNF_field.rs'),('crates/aspis-core/src/field/wide_exact.rs','KNF_wide_exact.rs')]:
 frozen=subprocess.check_output(['git','show',rev+':'+src]);actual=(E/dst).read_bytes()
 assert actual== (frozen.replace(b'mod wide_exact;',b'#[path="KNF_wide_exact.rs"] mod wide_exact;') if dst=='KNF_field.rs' else frozen)
 predicates=sorted(set(re.findall(r'feature\s*=\s*"([^"]+)"',actual.decode())))
 assert not set(predicates)&set(core['features'])
 file_audits.append(dict(source=src,frozen_sha256=sha(frozen),snapshot=dst,snapshot_sha256=sha(actual),all_feature_predicates=predicates,standalone_features=[],deployed_features=core['features'],same_selected_bodies=True,reason='no predicate references any feature in the symmetric difference'))
(E/'KNF_FEATURE_BODY_AUDIT.json').write_text(json.dumps(dict(canonical_graph_source='../native-featparity-20261028/NCS_I002-stdout.log',canonical_graph_sha256=sha((E.parent/'native-featparity-20261028/NCS_I002-stdout.log').read_bytes()),canonical_deployed_nodes=canonical,body_identity=file_audits,scope='standalone core helpers only; no verifier or statement code compiled'),indent=2)+'\n')
print('six matched pairs; fifteen terminal capped attempts; feature body identity checked')
