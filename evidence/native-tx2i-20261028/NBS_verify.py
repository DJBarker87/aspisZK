from pathlib import Path
import json,hashlib,re,subprocess
E=Path(__file__).resolve().parent
rows=[json.loads(p.read_text()) for p in sorted(E.glob('NBS_[LK][0-9][0-9][0-9]/receipt.json'))]
lean=[r for r in rows if r['kind']=='lean'];kani=[r for r in rows if r['kind']=='kani']
assert len(lean)==99 and len(kani)==40
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
assert all(r['limits']==limits and int(r['swaps'])==0 for r in rows)
roots=json.loads((E/'NBS_AUDIT_ROOTS.json').read_text());audit=json.loads((E/'NBS_L099/receipt.json').read_text());log=(E/'NBS_L099/stdout.log').read_text()
assert audit['exit_status']==0
printed={}
for line in log.splitlines():
 m=re.fullmatch(r"'([^']+)' depends on axioms: \[([^]]*)\]",line)
 if m:
  vals=[n.strip() for n in m.group(2).split(',') if n.strip()]
  assert set(vals)<=set(['propext','Classical.choice','Quot.sound']),line
  printed[m.group(1)]=vals
 m=re.fullmatch(r"'([^']+)' does not depend on any axioms",line)
 if m:printed[m.group(1)]=[]
assert all(n in printed for n in roots['new_top_theorems'])
matched={}
for module in roots['modules']+['NBS_Audit']:
 p=Path('lean')/(module+'.lean');pin=hashlib.sha256(p.read_bytes()).hexdigest()
 good=[r for r in lean if r['module']==module and r['exit_status']==0 and pin in r['source_hashes'].values()]
 assert good,('no matching passing snapshot',module)
 matched[module]=dict(source=str(p),sha256=pin,attempt=good[-1]['attempt'])
for p,pin in json.loads((E/'NBS_REUSE.json').read_text()).items():assert hashlib.sha256(Path(p).read_bytes()).hexdigest()==pin,p
lock=hashlib.sha256(subprocess.check_output(['git','show','4bb3b3f5:Cargo.lock'])).hexdigest()
for r in kani:
 a=r['attempt'];g=json.loads((E/(a+'-graph-check.json')).read_text())
 assert g['graph_matches_frozen'] and g['lock_sha256']==lock
 assert (E/(a+'-lock-after.log')).read_text().strip()==lock
 assert r['env']['CARGO_NET_OFFLINE']=='true'
summary=dict(lean=dict(attempts=len(lean),passed=sum(r['exit_status']==0 for r in lean),failed=sum(r['exit_status']!=0 for r in lean),new_modules=len(roots['modules']),new_top_theorems=roots['count'],audit_attempt='NBS_L099',audit_wall_seconds=audit['wall_seconds'],audit_peak_rss_kib=int(audit['peak_rss_kib']),audit_swap=0,source_revision=audit['source_revision'],matched_final_sources=matched,printed_new_axioms={n:printed[n] for n in roots['new_top_theorems']}),kani=dict(attempts=len(kani),passed=sum(r['exit_status']==0 for r in kani),failed=sum(r['exit_status']!=0 for r in kani),passing_with_KMX_hooks=[r['attempt'] for r in kani if r['exit_status']==0 and any('NBS_recheck_' in s or 'NBS_accessor::all_rows' in s for s in r['command'])],failed_attempts=[dict(attempt=r['attempt'],exit=r['exit_status'],wall_seconds=r['wall_seconds']) for r in kani if r['exit_status']]),all_scopes=dict(count=len(rows),compiler_prover_wall_seconds=sum(r['wall_seconds'] for r in rows),peak_rss_kib=max(int(r['peak_rss_kib']) for r in rows),swap=0,limits=limits),qualification='Focused source/helper/model and native-window results only. U00/U07/U08 remain OPEN as specified; no headline premise removed; target not established. No new prover launch after K040 exhausted native budget.')
(E/'NBS_VERIFICATION.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k!='lean'},indent=2));print(json.dumps({k:v for k,v in summary['lean'].items() if k not in ['matched_final_sources','printed_new_axioms']},indent=2))
