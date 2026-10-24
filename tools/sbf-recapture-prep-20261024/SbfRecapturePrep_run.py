#!/usr/bin/env python3
"""SSH metadata/hash transport with command and input-pin receipts."""
import hashlib,json,pathlib,resource,subprocess,sys,time
T=pathlib.Path(__file__).resolve().parent;E=T.parents[1]/'evidence/sbf-recapture-prep-20261024'
action=sys.argv[1];script=T/'SbfRecapturePrep_host.py';revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
cmd=['ssh','-o','BatchMode=yes','-o','ConnectTimeout=15','dombarker@100.108.41.90',f'SBF_PREP_REVISION={revision} SBF_PREP_SCRIPT_SHA256={hashlib.sha256(script.read_bytes()).hexdigest()} python3 - {action}']
t=time.monotonic();p=subprocess.run(cmd,input=script.read_bytes(),capture_output=True)
u=resource.getrusage(0);c=resource.getrusage(resource.RUSAGE_CHILDREN)
(E/(action+'.stdout.json')).write_bytes(p.stdout);(E/(action+'.stderr.txt')).write_bytes(p.stderr)
r=dict(command=cmd,exit=p.returncode,wall_seconds=time.monotonic()-t,peak_rss_bytes=u.ru_maxrss,children_peak_rss_bytes=c.ru_maxrss,swaps=u.ru_nswap+c.ru_nswap,source_revision=revision,script_sha256=hashlib.sha256(script.read_bytes()).hexdigest(),stdout_sha256=hashlib.sha256(p.stdout).hexdigest(),print_axioms='N/A')
(E/(action+'.transport.json')).write_text(json.dumps(r,indent=2)+'\n');print(p.stdout.decode());print(p.stderr.decode(),file=sys.stderr);sys.exit(p.returncode)
