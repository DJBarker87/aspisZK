from pathlib import Path
import json,re,lzma,hashlib,subprocess
E=Path(__file__).resolve().parent
rows=[json.loads(p.read_text())for p in sorted(E.glob('NLR_[LK][0-9][0-9][0-9]/receipt.json'))]
assert sum(r['attempt'][4]=='L'for r in rows)==140
assert sum(r['kind']=='kani'for r in rows)==40
assert len(rows)==180 and len({r['attempt']for r in rows})==180
x=json.loads((E/'NLR_GATE_AUDIT.json').read_text());x['retention']=json.loads((E/'NLR_RETENTION.json').read_text())
x['budget']=dict(lean_support=140,kani=40,extraction=0)
x['failed_lean_support_scopes']=[dict(attempt=r['attempt'],kind=r['kind'],module=r['module'],exit=r['exit_status'])for r in rows if r['attempt'][4]=='L'and r['exit_status']]
x['retired_packaging_timeout']=dict(attempt='NLR_L122',outer_exit=124,inner_walker_exit=0,proof_replayed=False,packaging_split_to='NLR_L139')
x['status'] += '_WITH_RETAINED_OUTER_PACKAGING_TIMEOUT'
x['metrics']=dict(total_wall_seconds=sum(r['wall_seconds']for r in rows),peak_rss_kib=max(int(r['peak_rss_kib'])for r in rows),swaps=sum(int(r['swaps'])for r in rows))
x['source_proof_modules']=json.loads((E/'NLR_MODULES.json').read_text())
x['native_scope']=json.loads((E/'NLR_NATIVE_SCOPE.json').read_text())
x['target_established']=False;x['closed_rows']=[];x['candidate_roots']=[]
(E/'NLR_AUDIT.json').write_text(json.dumps(x,indent=2)+'\n')
(E/'NLR_CLOSED.json').write_text(json.dumps(dict(baseline='evidence/ledger22-20261110/NLO_LEDGER.json.xz',status='target not yet established',rows=[],row_roots=[],closed=[],candidates=[],promotions=0,native_parent_realization=False,full_child136_packet=False,schemas_source_value_only=True),indent=2)+'\n')
(E/'NLR_LEDGER_DELTA.json').write_text(json.dumps(dict(baseline='evidence/ledger22-20261110/NLO_LEDGER.json.xz',before=dict(CLOSED=576,QUALIFIED=0,OPEN=23,total=599),after=dict(CLOSED=576,QUALIFIED=0,OPEN=23,total=599),delta=dict(CLOSED=0,QUALIFIED=0,OPEN=0),row_roots=[],credit='none; source support only; next ledger gate required for any future root'),indent=2)+'\n')
(E/'NLR_METRICS.json.xz').write_bytes(lzma.compress(json.dumps(rows).encode()))
(E/'NLR_METRICS.json.sha256').write_text(hashlib.sha256(json.dumps(rows).encode()).hexdigest()+'\n')
# Failed drafts are retained but never imported as positive evidence.
selected=set(x['source_proof_modules']['modules']);drafts=[]
for p in (E/'NLR_generated').glob('*.lean'):
 if p.stem not in selected and p.stem not in ['NLR_COMBINED_IMPORT','NLR_Driver','NLR_ProofDriver','NLR_Inspect']:
  drafts.append(dict(module=p.stem,sha256=hashlib.sha256(p.read_bytes()).hexdigest(),reason='not selected successful current-source evidence'))
(E/'NLR_EXCLUDED_DRAFTS.json').write_text(json.dumps(drafts,indent=2)+'\n')
print(json.dumps(dict(status=x['status'],scopes=len(rows),raw_roots=x['raw_roots'],scan_modules=x['scan_modules'],closed_rows=0,peak_rss_kib=x['metrics']['peak_rss_kib'],swaps=x['metrics']['swaps'])))
