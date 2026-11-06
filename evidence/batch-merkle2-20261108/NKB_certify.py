"""Validate native evidence associations without launching a prover."""
from pathlib import Path
import json,sys,hashlib
sys.dont_write_bytecode=True
import NKB_resolve
E=Path(__file__).resolve().parent
pairs=[(1,2,'count rejection diagnostic'),(5,6,'key/opening/leaf argument prefix'),(13,14,'dedup/full frame'),(15,16,'eight-byte padding predicate'),(17,18,'std iterator next'),(19,20,'entered Parse exit'),(21,22,'std any differential')]
rows=[]
for a,b,scope in pairs:
 ids=[f'NKB_K{n:03d}' for n in [a,b]];receipts=[json.loads((E/x/'receipt.json').read_text()) for x in ids]
 assert receipts[0]['exit_status']==0 and receipts[1]['exit_status']==1,ids
 assert receipts[0]['source_hashes']==receipts[1]['source_hashes'],ids
 pins=[]
 for name,r in zip(ids,receipts):
  admission=json.loads((E/(name+'-admission.json')).read_text());assert admission['exit']==0 and admission['reservation']['allowed'] is True
  log=NKB_resolve.read(name+'/stdout.log').decode();assert not any(x in log.lower() for x in ['cbmc timed out','timed out','time limit exceeded'])
  expected='VERIFICATION:- SUCCESSFUL' if r['exit_status']==0 else 'VERIFICATION:- FAILED';assert expected in log
  assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'} and str(r['swaps'])=='0'
  graph=json.loads(NKB_resolve.read(name+'_validation/NHR_GRAPH_CHECK.json'));lock=json.loads(NKB_resolve.read(name+'_validation/NKB_LOCK.json'))
  assert graph['graph_matches_frozen'] and lock['unchanged'];assert r['env']['CARGO_NET_OFFLINE']=='true'
  assert r['source_hashes']['NKB_KMX.patch']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
  for source,sha in r['source_hashes'].items():assert hashlib.sha256(NKB_resolve.read(name+'/sources/'+source)).hexdigest()==sha
  pins.append(dict(attempt=name,exit=r['exit_status'],wall=r['wall_seconds'],rss_kib=r['peak_rss_kib'],swaps=r['swaps'],source_revision=r['source_revision'],features=graph['features'],cargo_target=r['env']['CARGO_TARGET_DIR']))
 rows.append(dict(pair=ids,scope=scope,source_hashes=receipts[0]['source_hashes'],metrics=pins,credit='DIAGNOSTIC ONLY' if a==1 else 'LOCAL SUPPORT ONLY; no parent row admitted'))
(E/'NKB_NATIVE_PAIRS.json').write_text(json.dumps(rows,indent=2)+'\n')
with (E/'NKB_CERTIFICATES.md').open('w') as f:
 f.write('# NKB certificate associations\n\nTarget not yet established. No parent row is CLOSED.\n\n')
 for row in rows:
  a,b=row['pair'];h=row['source_hashes'];f.write('## '+a+' / '+b+' — '+row['scope']+'\n\nPositive exit0, matched semantic control exit1, identical source inputs and exact KMX patch. '+row['credit']+'.\n\n')
  f.write('Harness snapshot `'+a+'/sources/NKB_harness.rs`, SHA256 `'+h['NKB_harness.rs']+'`; fragments SHA256 `'+h['NKB_fragments.rs']+'`. Frozen graph/features, unchanged lock, full argv, cgroup, source revision, wall/RSS/swap and output are retained per attempt and indexed in NKB_NATIVE_PAIRS.json.\n\n')
 f.write('## Reviewed transcription items\n\nNKB_DedupCut.Cut: K013/K014 exact duplicate/append/error poststate with all16 indices/all512 digest bytes and unchanged cursor; NKB_DedupCut.source and NKB_LeafChain.source establish the forward local native-G-to-cohort direction and finite frame chain.\n\nNKB_ParseCut.Cut: K019/K020 entered Parse-return block and complete array frame; NKB_ParseCut.mismatch proves a local Result-carrier mismatch with the reused pending-none boundary, not a whole-parent theorem. The preceding guard must be derived, never assumed at a positive parent root.\n\nNKB_AnyModel: hand std model under (au)(3), documented Rust semantics, pinned Aeneas body equations, K015/K016 and K017/K018, plus actual any K021/K022 zero/one-chunk differential. Complete finite scan/state proof is NKB_AnyModel.total. See NKB_STD_MODEL.md.\n\nAll are existing P6/D188/P7 option-A RECLASSIFICATION, not removal of trust. No new trust row or extraction is used. Source/core models and shipped artifacts are unchanged.\n\nEvery new top theorem has a focused #print axioms receipt; final proof/source inventory and the combined raw ax2/NFX gate are indexed separately. NJS and NJV candidate credit depends on ledger17. There is no positive full batch_tree/batch_merkle_values/batch_merkle/canonical_scan root to promote.\n')
print('NKB certificate consistency PASS: '+str(len(rows))+' paired local windows, no admitted parent rows')
