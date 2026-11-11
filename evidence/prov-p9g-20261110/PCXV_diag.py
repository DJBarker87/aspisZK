#!/usr/bin/env python3
"""PCXV_ DIAGNOSTIC (credits nothing): compile each excluded root from unchanged L187 source against the current view; outputs in diag/, never objs/ or view/. One scope at a time, admission-gated."""
import json,pathlib,subprocess,time,sys,hashlib
WS=pathlib.Path('/home/dombarker/project-offloads/codex-pc-pin2-replay-20261111');L=pathlib.Path('/home/dombarker/project-offloads/codex-cx-replay-l187-20261109')
SYS='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0';D=WS/'diag';D.mkdir(exist_ok=True);(D/'adm').mkdir(exist_ok=True)
M={r['module']:r for r in json.load(open(WS/'PCXR_REBUILD_SET.json'))['modules']}
roots='PublicExtractedRawBridge431,WithdrawalCarrierBridge431,RPv_FIz_CoefficientsOnRun,RPv_FIz_WideCoefficientsOnRun,NDO_JFs_SerializerSize,NDO_JFz_Row17,NDO_JFz_Row18'.split(',')
for m in roots:
    r=M[m];af=D/'adm'/(m+'.json')
    while True:
        x=subprocess.run(['python3',str(WS/'runner/pcxr_admit.py'),str(af)],capture_output=True,text=True)
        ad=json.loads(af.read_text())
        if x.returncode==0 and ad.get('allowed') is True:break
        time.sleep(120)
    unit='pcxv-diag-%s-%d'%(hashlib.sha256(m.encode()).hexdigest()[:8],int(time.time()))
    job=dict(module=m,target='DIAG_'+m,src=str(L/'src'/r['src_rel']),root=str(L/'src'),expected_source_sha256=r['source_sha256'],out_olean=str(D/'objs'/(m.replace('.','/')+'.olean')),imports={},import_key='diag',l187_obj=None,receipt=str(D/(m+'.json')),lean=SYS+'/bin/lean',sysroot=SYS,lean_path=str(WS/'view')+':'+str(L/'base_ref'),tmpdir=str(WS/'tmp'),cwd=str(WS),source_revision='DIAGNOSTIC unchanged L187 source vs PIN2 view',unit=unit)
    jf=D/(m+'.job.json');jf.write_text(json.dumps(job))
    p=subprocess.run(['systemd-run','--user','--scope','--quiet','--unit',unit,'-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(WS/'runner/pcxr_scope_run.py'),str(jf)],capture_output=True,text=True)
    print(m,p.stdout[-200:].strip(),flush=True)
