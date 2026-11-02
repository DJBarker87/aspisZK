from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
plan=[(50,'late_binding',['snapshot','positive'],'pool_v1::pair_tree_profile::NEL_late_binding::binding'),(51,'late_binding',['snapshot','negative'],'pool_v1::pair_tree_profile::NEL_late_binding::binding'),(52,'late_binding',['after','positive'],'pool_v1::pair_tree_profile::NEL_late_binding::binding'),(53,'late_binding',['after','negative'],'pool_v1::pair_tree_profile::NEL_late_binding::binding'),(54,'frontier_step',['live','positive'],'pool_v1::pair_tree_profile::NEL_frontier_step::frontier_step'),(55,'frontier_step',['live','negative'],'pool_v1::pair_tree_profile::NEL_frontier_step::frontier_step'),(56,'frontier_step',['after','positive'],'pool_v1::pair_terminal::NEL_frontier_step::frontier_step'),(57,'frontier_step',['after','negative'],'pool_v1::pair_terminal::NEL_frontier_step::frontier_step'),(58,'payment_fields',['positive'],'pool_v1::payment_relation::NEL_payment_fields::field_binding'),(59,'payment_fields',['negative'],'pool_v1::payment_relation::NEL_payment_fields::field_binding')]
for n,case,args,h in plan:
 a=f'NEL_K{n:03}';subprocess.run([sys.executable,str(E/('NEL_prepare_'+case+'.py')),*args],check=True)
 for p in E.glob('NEL_*CURRENT.json'):(E/(a+'-'+p.name)).write_bytes(p.read_bytes())
 r=subprocess.run([sys.executable,str(E/'NEL_kani_run.py'),a,'kani',h],capture_output=True,text=True);print(a,case,args,r.stdout[-1500:],r.stderr,flush=True)
 if not (E/a/'receipt.json').exists():raise SystemExit('STOP unresolved launch')
 log=(E/a/'stdout.log').read_text();mode=args[-1]
 if ('VERIFICATION:- SUCCESSFUL' in log)!=(mode=='positive') or 'timed out' in log.lower() or (mode=='negative' and 'Failed Checks:' not in log):raise SystemExit('STOP inspect/split; never repeat timed-out shape')
