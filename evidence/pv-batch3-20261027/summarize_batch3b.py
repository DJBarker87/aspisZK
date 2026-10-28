from pathlib import Path
import json,hashlib,re,subprocess
D=Path(__file__).resolve().parent;t=json.loads((D/'TALLY-batch3b.json').read_text());records=[];coverage={}
allowed={'propext','Classical.choice','Quot.sound'}
for item in t['receipts']:
 a=item['attempt'];R=D/'receipts'/f'lean-{a}';r=json.loads((R/'receipt/receipt.json').read_text());log=(R/'receipt/stdout.log').read_text()+(R/'receipt/stderr.log').read_text();groups=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',log,re.S);axs=sorted(set(q.strip()for g in groups for q in g.split(',')if q.strip()));r['axiom_union']=axs;r['accepted']=r['exit_status']==0
 if r['accepted']:
  assert set(axs)<=allowed,(a,axs)
  p=D/'lean'/(item['module']+'.lean');sha=hashlib.sha256(p.read_bytes()).hexdigest()
  if sha==r['source_sha256']:coverage[item['module']]=dict(attempt=a,source_sha256=sha,axioms=axs)
 records.append(r)
assert len(records)==t['lean_attempts']==15
out=dict(charged=15,accepted=sum(r['accepted']for r in records),rejected=sum(not r['accepted']for r in records),unspent=85,kani=0,ids_used=t['used_ids'],refusals=t['refusals'],reserved_audit_ids_unused=[37997,37998,37999],stop_reason='native fixture disagreement, not budget exhaustion',maximum_lean_peak_rss_kib=max(r['peak_rss_kib']for r in records),all_lean_swaps_zero=all(r['swaps']==0 for r in records),receipts=records)
(D/'batch3b-receipt-index.json').write_text(json.dumps(out,indent=1)+'\n');(D/'batch3b-current-source-coverage.json').write_text(json.dumps(coverage,indent=1)+'\n')
rows=json.loads((D/'resume-row-status.json').read_text());rows['batch3b_stop_reason']=out['stop_reason'];rows['batch3b_rows_closed']=0
for r in rows['rows']:
 r['batch3b_before_after']='P unchanged; no row-closing theorem, premise removal, or new T field'
 r['batch3b_new_source_claim']=False
 if r['id']=='V239':r['batch3b_partial_only']=['PV_B3_MultilinearGuard222.wrong_length','PV_B3_PrefixFinite222.source','PV_B3_EvalCounter222.body_counter'];r['batch3b_ruling_n']='Array.update is threaded; emitted changed-write case evaluates to7. Identical-input native/emission comparison remains pending; native harness written but not run before forced stop.'
(D/'batch3b-row-status.json').write_text(json.dumps(rows,indent=1)+'\n')
log=subprocess.check_output(['git','log','--oneline','d4251d80303af9ee024a6da046ee5909d4aa631f..HEAD'],text=True);(D/'COMMIT-LOG-batch3b.txt').write_text(log)
print(json.dumps({k:v for k,v in out.items()if k not in ['receipts','ids_used','refusals']}))
