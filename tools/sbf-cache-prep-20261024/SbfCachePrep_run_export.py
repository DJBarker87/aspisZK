#!/usr/bin/env python3
"""One export attempt with committed literal proc helper around ordinary copy."""
import hashlib,json,pathlib,resource,subprocess,sys,time
T=pathlib.Path(__file__).resolve().parent;E=T.parents[1]/'evidence/sbf-cache-prep-20261024';revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
assert subprocess.run(['ps','-p','91101','-o','pid=,lstart=,stat=,command='],capture_output=True).returncode==1
marker=pathlib.Path('/private/tmp/claude-501/-Users-dominic-ZK/4dec4925-8c43-447e-9333-6147c1c7863b/scratchpad/codex-resource-actual-20261024.out');assert marker.read_bytes().rstrip().endswith(b'codex-exit=0')
def run(phase,script,privileged=False):
    assert not (E/(phase+'.stdout.json')).exists()
    body=(T/script).read_bytes()
    if privileged:assert body==subprocess.check_output(['git','show',revision+':tools/sbf-cache-prep-20261024/'+script])
    cmd=['ssh','-o','BatchMode=yes','-o','ConnectTimeout=10','dombarker@100.108.41.90',('sudo -n ' if privileged else '')+'python3 -'];t=time.monotonic();p=subprocess.run(cmd,input=body,capture_output=True,timeout=60)
    (E/(phase+'.stdout.json')).write_bytes(p.stdout);(E/(phase+'.stderr.txt')).write_bytes(p.stderr)
    u=resource.getrusage(0);c=resource.getrusage(resource.RUSAGE_CHILDREN)
    r=dict(command=cmd,exit=p.returncode,wall_seconds=time.monotonic()-t,peak_rss_bytes=u.ru_maxrss,children_peak_rss_bytes=c.ru_maxrss,swaps=u.ru_nswap+c.ru_nswap,source_revision=revision,script_sha256=hashlib.sha256(body).hexdigest(),transport_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),stdout_sha256=hashlib.sha256(p.stdout).hexdigest(),stderr_sha256=hashlib.sha256(p.stderr).hexdigest(),print_axioms='N/A')
    (E/(phase+'.transport.json')).write_text(json.dumps(r,indent=2)+'\n');assert p.returncode==0,p.stderr;return json.loads(p.stdout)
pre=run('export-pre','SbfCachePrep_proc.py',True)
if not pre['allowed_to_enter']:print('Export stopped: pre observation denied; no retry or copy.');sys.exit(0)
try:
    copied=run('export','SbfCachePrep_export.py');print(json.dumps(copied,indent=2))
finally:
    post=run('export-post','SbfCachePrep_proc.py',True);print('Post observation allowed:',post['allowed_to_enter'])
