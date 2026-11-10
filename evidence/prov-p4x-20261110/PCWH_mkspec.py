#!/usr/bin/env python3
"""usage: python3 PCWH_mkspec.py RUN BASE_SPEC NAMESPACE ROOTS(comma|ALL9) [EXTRA_INCLUDES(comma)] [NO_ABORT_FLAG]
Clone a verified earlier spec (same crate, features, overflow configuration, opacity) and change only: run, roots, tools (second tool version),
host paths, dest-file, namespace."""
import json,sys,re
sys.dont_write_bytecode=True
run,base,ns,roots=sys.argv[1:5];inc=[x for x in (sys.argv[5] if len(sys.argv)>5 else '').split(',') if x]
H='/home/dombarker/project-offloads/codex-pc-prov-p4x-20261110'
T=json.load(open('PCWH_TOOL_BUILD.json'))['result']
d=json.load(open(base))
roots=[r['charon_start_from'] for r in json.load(open('PCWH_ROOTS.json'))['roots']] if roots=='ALL9' else roots.split(',')
oldrun=d['run']
def fix(x):
    x=re.sub(r'codex-pc-prov-[a-z0-9]+-2026[0-9]+','codex-pc-prov-p4x-20261110',x)
    x=re.sub(r'PC[A-Z]{2}_workspace','PCWH_workspace',x)
    return x.replace(oldrun,run)
c=d['charon_command'];c2=[];i=0;ins=False
while i<len(c):
    if c[i]=='--start-from':
        if not ins:
            for r in roots:c2+=['--start-from',r]
            ins=True
        i+=2;continue
    if c[i]=='--dest-file':c2+=['--dest-file',H+'/'+run+'_emitted/repro.llbc'];i+=2;continue
    c2.append(c[i]);i+=1
if '--dest-file' not in c2:
    j=c2.index('--');c2=c2[:j]+['--dest-file',H+'/'+run+'_emitted/repro.llbc']+c2[j:]
for e in inc:
    j=c2.index('--dest-file');c2=c2[:j]+['--include',e]+c2[j:]
c2=[fix(x) for x in c2];c2[0]=T['host_bin']+'/charon'
a=[fix(x) for x in d['aeneas_command']];a[0]=T['host_bin']+'/aeneas'
a[-1]=H+'/'+run+'_emitted/repro.llbc'
a[a.index('-namespace')+1]=ns;a[a.index('-subdir')+1]=ns
if len(sys.argv)>6 and sys.argv[6]=='noabort' and '-abort-on-error' in a:a.remove('-abort-on-error')
d.update(run=run,spec_id=run,charon_command=c2,aeneas_command=a,aeneas_tool='second',aeneas_sha256=T['sha256_aeneas'],charon_sha256=T['sha256_charon'],charon_driver_sha256=T['sha256_charon_driver'],
 tool_label='second tool version: Aeneas 0d21a9ec + Charon 454586e9 (PCWH_TOOL_BUILD.json)',derived_from=base)
[d.pop(k,None) for k in ('llbc_stable','aeneas_only','llbc','llbc_produced_by')]
d['configuration'].update(roots=roots,namespace=[ns])
d.setdefault('extra_env',{})['CARGO_PROFILE_RELEASE_CODEGEN_UNITS']='2'  # PCWH: new charon-driver codegens dependencies; 16 default units x 4 jobs exceeded TasksMax=64 (PCWH_E003)
d['expected_limits']={'memory.high':'3221225472','memory.max':'4294967296','memory.swap.max':'0','pids.max':'64'}
json.dump(d,open(run+'_spec.json','w'),indent=1);print(run,len(roots),'roots',ns)
