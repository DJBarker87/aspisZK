#!/usr/bin/env python3
"""One-shot metadata transport; never reads donor data or launches a build."""
import hashlib,json,pathlib,resource,subprocess,time,sys
T=pathlib.Path(__file__).resolve().parent;E=T.parents[1]/'evidence/sbf-cache-prep-20261024'
start=time.monotonic() # macOS RLIMIT_AS is unsupported; remote helper is capped.
assert not (E/'proc.stdout.json').exists(),'do not repeat unchanged observation'
ps=['ps','-p','91101','-o','pid=,lstart=,stat=,command='];p=subprocess.run(ps,capture_output=True)
assert p.returncode==1 and not p.stdout,'coordination launcher not terminal; do not inspect host'
marker=pathlib.Path('/private/tmp/claude-501/-Users-dominic-ZK/4dec4925-8c43-447e-9333-6147c1c7863b/scratchpad/codex-resource-actual-20261024.out')
# Marker checked only after ps proved PID absent. No other job log is copied.
assert marker.read_bytes().rstrip().endswith(b'codex-exit=0')
script=T/'SbfCachePrep_proc.py';body=script.read_bytes();revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
assert subprocess.check_output(['git','show',revision+':tools/sbf-cache-prep-20261024/'+script.name])==body,'literal helper must be committed'
cmd=['ssh','-o','BatchMode=yes','-o','ConnectTimeout=10','dombarker@100.108.41.90','sudo -n python3 -']
t=time.monotonic();r=subprocess.run(cmd,input=body,capture_output=True,timeout=60)
assert len(r.stdout)<16*1024**2 and len(r.stderr)<1024**2
(E/'proc.stdout.json').write_bytes(r.stdout);(E/'proc.stderr.txt').write_bytes(r.stderr)
u=resource.getrusage(0);c=resource.getrusage(resource.RUSAGE_CHILDREN)
receipt=dict(command=cmd,exit=r.returncode,wall_seconds=time.monotonic()-t,total_wall_seconds=time.monotonic()-start,peak_rss_bytes=u.ru_maxrss,children_peak_rss_bytes=c.ru_maxrss,swaps=u.ru_nswap+c.ru_nswap,source_revision=revision,script_sha256=hashlib.sha256(body).hexdigest(),transport_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),stdout_sha256=hashlib.sha256(r.stdout).hexdigest(),stderr_sha256=hashlib.sha256(r.stderr).hexdigest(),coordination=dict(command=ps,exit=p.returncode,stdout_bytes=0,terminal_marker='codex-exit=0',marker_checked_after_pid_absent=True),print_axioms='N/A')
(E/'proc.transport.json').write_text(json.dumps(receipt,indent=2)+'\n')
x=json.loads(r.stdout);print(json.dumps(dict(receipt=receipt,allowed=x.get('allowed_to_enter'),processes=len(x.get('processes',[])),errors=sum(bool(x.get('errors')) for x in x.get('processes',[])),matching=sum(bool(x.get('matches')) for x in x.get('processes',[]))),indent=2))
