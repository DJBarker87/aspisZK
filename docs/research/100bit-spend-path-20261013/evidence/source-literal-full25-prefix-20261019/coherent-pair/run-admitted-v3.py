from pathlib import Path
import argparse,contextlib,fcntl,io,json,runpy,subprocess,sys,hashlib
W=Path(__file__).resolve().parent; C=json.loads((W/'config.json').read_text()); ap=argparse.ArgumentParser();ap.add_argument('--phase',choices=['initial','prefix'],required=True); phase=ap.parse_args().phase
G=1024**3; collector=Path(C['collector']); assert hashlib.sha256(collector.read_bytes()).hexdigest()==C['collector_sha256']
with open(C['global_lock'],'a') as lock:
 fcntl.flock(lock,fcntl.LOCK_EX)
 buf=io.StringIO()
 with contextlib.redirect_stdout(buf): runpy.run_path(str(collector))
 inv=json.loads(buf.getvalue()); rows=inv['all_populated_cgroups']; unc=[r for r in rows if r['max']=='max' and (r['scope'] or (Path(r['path']).name.endswith('.service') and not any(Path(r['path']) in Path(s['path']).parents for s in rows)))]; outer=[r for r in unc if not any(Path(s['path']) in Path(r['path']).parents for s in unc)]; usage=sum(r['current_bytes'] or 0 for r in outer); cap=6*G; reserve=8*G; finite=inv['effective_sum_bytes']
 checks={'finite_plus_candidate_le_48GiB':finite+cap<=48*G,'finite_plus_uncapped_and_reserve_le_MemTotal':finite+cap+usage+reserve<=inv['MemTotal_kB']*1024,'MemAvailable_at_least_14GiB':inv['MemAvailable_kB']*1024>=14*G}; report={'phase':phase,'inventory':inv,'outermost_uncapped_execution_nodes':outer,'candidate_cap_bytes':cap,'OS_growth_reserve_bytes':reserve,'checks':checks}; p=W/('admission-'+phase+'.json'); assert not p.exists();p.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'phase':phase,'checks':checks,'finite_reserved_GiB':finite/G,'uncapped_current_GiB':usage/G}),flush=True);assert all(checks.values()),'admission rejected; no job started'
 cmd=['systemd-run','--user','--scope','--quiet','--unit='+C['unit']+'-'+phase,'-p','MemoryHigh=4G','-p','MemoryMax=6G','-p','MemorySwapMax=0','-p','TasksMax=128','python3',str(W/'run-stage-v3.py'),phase]
 rc=subprocess.run(cmd).returncode
 if phase=='initial' and rc==0:
  r=json.loads((W/'attempt/initial-evidence/receipt.json').read_text()); C['initial_object_sha256']=r['object_sha256']; (W/'config.json').write_text(json.dumps(C,indent=2,sort_keys=True)+'\n')
 raise SystemExit(rc)
