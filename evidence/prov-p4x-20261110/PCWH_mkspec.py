#!/usr/bin/env python3
"""usage: python3 PCWH_mkspec.py RUN ROOTS(comma, charon selectors; 'ALL9' = the nine in PCWH_ROOTS.json) [extra --include comma]
Clone PCQK_E011 (cost-probe, overflow ON, prover,r1p-check,private-leaf-salts) and change only: run, roots, tool paths (second tool version), host paths, dest-file."""
import json,sys,re
sys.dont_write_bytecode=True
run=sys.argv[1];roots=sys.argv[2];inc=[x for x in (sys.argv[3] if len(sys.argv)>3 else '').split(',') if x]
H='/home/dombarker/project-offloads/codex-pc-prov-p4x-20261110'
T=json.load(open('PCWH_TOOL_BUILD.json'))['result']
d=json.load(open('../prov-p1n-20261110/PCQK_E011_spec.json'))
roots=[r['charon_start_from'] for r in json.load(open('PCWH_ROOTS.json'))['roots']] if roots=='ALL9' else roots.split(',')
c=d['charon_command'];c2=[];i=0;ins=False
while i<len(c):
    if c[i]=='--start-from':
        if not ins:
            for r in roots:c2+=['--start-from',r]
            ins=True
        i+=2;continue
    if c[i]=='--dest-file':c2+=['--dest-file',H+'/'+run+'_emitted/repro.llbc'];i+=2;continue
    c2.append(c[i]);i+=1
for e in inc:
    j=c2.index('--dest-file');c2=c2[:j]+['--include',e]+c2[j:]
def fix(x):return x.replace('codex-pc-prov-p1n-20261110',H.split('/')[-1]).replace('PCQK_workspace','PCWH_workspace').replace('PCQK_E011',run)
c2=[fix(x) for x in c2];c2[0]=T['host_bin']+'/charon'
a=[fix(x) for x in d['aeneas_command']];a[0]=T['host_bin']+'/aeneas'
a[a.index('-namespace')+1]='PCWH_cp';a[a.index('-subdir')+1]='PCWH_cp'
d.update(run=run,spec_id=run,charon_command=c2,aeneas_command=a,aeneas_tool='second',aeneas_sha256=T['sha256_aeneas'],charon_sha256=T['sha256_charon'],charon_driver_sha256=T['sha256_charon_driver'],
 tool_label='second tool version: Aeneas 0d21a9ec + Charon 454586e9 (PCWH_TOOL_BUILD.json)')
d.pop('llbc_stable',None);d['opacity']=[]
d['configuration'].update(roots=roots,namespace=['PCWH_cp'])
json.dump(d,open(run+'_spec.json','w'),indent=1);print(run,len(roots),'roots')
