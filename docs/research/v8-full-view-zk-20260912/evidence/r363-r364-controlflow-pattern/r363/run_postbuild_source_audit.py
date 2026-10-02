#!/usr/bin/env python3
"""Run the read-only R363 postbuild filesystem audit in a small capped host scope."""
import datetime, hashlib, json, pathlib, shlex, subprocess, time

here=pathlib.Path(__file__).resolve().parent
script=here/'audit_postbuild_sources.py'
out=here/'postbuild-source-audit'
host='dombarker@100.108.41.90'
root='/home/dombarker/project-offloads/aspis-r363-instantiated-pattern-candidate-20261002-a'
remote_audit=root+'/candidate-audit/r363-build'
remote_script=remote_audit+'/audit_postbuild_sources.py'
remote_out=remote_audit+'/postbuild-source-audit'
sshopt=['-o','BatchMode=yes','-o','ConnectTimeout=5','-o','StrictHostKeyChecking=no','-o','UserKnownHostsFile=/dev/null']
assert script.is_file() and out.is_dir() and not any(out.iterdir()), 'local audit output dir must be empty'
assert hashlib.sha256(script.read_bytes()).hexdigest()=='2b17c40444e980c45ce5e952c5875b3b4d385aefd65ed8f9e15abe5e4fe52435'
preflight=(
 f'test -d {shlex.quote(remote_audit)} && test ! -e {shlex.quote(remote_script)} && test ! -e {shlex.quote(remote_out)} && '
 f'test "$(sha256sum {shlex.quote(root+"/candidate-audit/R363-source-tree-manifest.json")} | cut -d" " -f1)" = e43845424aeb6964281bd0d5e9d7ba4beb3d0a0aefe10b8acdab382127503e89 && '
 f'test "$(sha256sum {shlex.quote(root+"/candidate-audit/clone-audit.json")} | cut -d" " -f1)" = 7b0482d1ea4b068ece18267002cdcd7dd24689f18b6909e2964cbe6bb5bba275 && '
 f'test "$(sha256sum {shlex.quote(root+"/aeneas-r363-instantiated-pattern-candidate")} | cut -d" " -f1)" = 3dc9ad6de1af901c8ead41940ba97097a0cf06f82d27dbc7d7c5eac03695e329'
)
subprocess.run(['ssh',*sshopt,host,preflight],check=True)
subprocess.run(['scp',*sshopt,str(script),host+':'+remote_script],check=True)
argv=['systemd-run','--user','--wait','--collect','--pipe','--unit=aspis-r363-postbuild-source-audit','--working-directory='+root+'/src','-p','MemoryHigh=1G','-p','MemoryMax=2G','-p','MemorySwapMax=0','-p','TasksMax=128','python3',remote_script]
started=datetime.datetime.now(datetime.timezone.utc).isoformat()
t0=time.monotonic()
proc=subprocess.run(['ssh',*sshopt,host,shlex.join(argv)],capture_output=True,text=True)
elapsed=time.monotonic()-t0
(out/'audit-run.stdout').write_text(proc.stdout)
(out/'audit-run.stderr').write_text(proc.stderr)
receipt={'started_utc':started,'elapsed_seconds':elapsed,'exit_status':proc.returncode,'ssh_host':host,'systemd_run_argv':argv,'caps':{'MemoryHigh':'1G','MemoryMax':'2G','MemorySwapMax':'0','TasksMax':128},'remote_checker_sha256':hashlib.sha256(script.read_bytes()).hexdigest(),'remote_output':remote_out,'local_output':str(out),'source_or_build_changes':False,'compile_or_translation':False}
(out/'audit-run-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
if proc.returncode==0:
    subprocess.run(['scp','-r',*sshopt,host+':'+remote_out+'/.',str(out)],check=True)
print(json.dumps(receipt,indent=2))
raise SystemExit(proc.returncode)
