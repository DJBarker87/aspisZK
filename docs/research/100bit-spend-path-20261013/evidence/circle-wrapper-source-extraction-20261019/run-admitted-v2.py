from pathlib import Path
import argparse, contextlib, fcntl, io, json, runpy, subprocess

a=argparse.ArgumentParser();a.add_argument('--phase',choices=['charon','aeneas'],required=True);o=a.parse_args()
w=Path('/home/dombarker/project-offloads/r1-circle-sample-wrapper-extraction-v2')
with open('/tmp/aspis-global-extraction-admission-20261019.lock','a') as lock:
 fcntl.flock(lock,fcntl.LOCK_EX)
 buf=io.StringIO()
 with contextlib.redirect_stdout(buf):runpy.run_path(str(w/'collect-cgroups.py'))
 inventory=json.loads(buf.getvalue());rows=inventory['all_populated_cgroups'];root=Path('/sys/fs/cgroup')
 uncapped=[r for r in rows if r['max']=='max' and (r['scope'] or (Path(r['path']).name.endswith('.service') and not any(Path(r['path']) in Path(s['path']).parents for s in rows)))]
 outer=[r for r in uncapped if not any(Path(s['path']) in Path(r['path']).parents for s in uncapped)]
 # Count active execution scopes and leaf services; ancestor slices duplicate
 # descendants and retain reclaimable file/slab charges from completed jobs.
 # MemAvailable independently guards host reclaimability.
 candidate=8*2**30;reserve=8*2**30;usage=sum(r['current_bytes'] or 0 for r in outer)
 checks={'finite_plus_candidate_below_48GiB':inventory['effective_sum_bytes']+candidate<=48*2**30,
 'reservation_plus_uncapped_plus_OS_below_total':inventory['effective_sum_bytes']+candidate+usage+reserve<=inventory['MemTotal_kB']*1024,
 'available_at_least_14GiB':inventory['MemAvailable_kB']*1024>=14*2**30}
 report={'inventory':inventory,'outermost_uncapped_execution_nodes':outer,'candidate_bytes':candidate,'OS_reserve_bytes':reserve,'checks':checks,'scope':'prelaunch global admission; lock held until scoped process terminates'}
 out=w/('admission-execution-nodes-'+o.phase+'.json');assert not out.exists();out.write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps({'phase':o.phase,'checks':checks,'finite_reserved_GiB':inventory['effective_sum_bytes']/2**30,'outer_uncapped_current_GiB':usage/2**30}),flush=True)
 assert all(checks.values()),'admission rejected; no job started'
 cmd=['systemd-run','--user','--scope','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','python3',str(w/'run-source-call-extraction.py'),'--root',str(w),'--phase',o.phase]
 raise SystemExit(subprocess.run(cmd).returncode)
