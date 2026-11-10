#!/usr/bin/env python3
"""PCQL_batch2.py TAG GATEMOD(dotted, e.g. NGD_SlotRef.Funs) FRESHDIR(inputs/fresh_E0xx) FRESHNS ONLY_JSON [PREVLOG]
Gate source = the L187 replay closure source (read-only ssh cat), not a research candidate. Writes PRVEq_<M>_<TAG>.lean, gen/<M>_<TAG>.*"""
import sys,json,re,subprocess,os
sys.dont_write_bytecode=True
H=os.path.dirname(os.path.abspath(__file__));os.chdir(H)
L='/home/dombarker/project-offloads/codex-cx-replay-l187-20261109/src/'
tag,m,fd,ns,only=sys.argv[1:6];prev=sys.argv[6] if len(sys.argv)>6 else None
safe=m.replace('.','_')
def cat(rel):
    r=subprocess.run(['ssh','-o','ConnectTimeout=20','-o','ServerAliveInterval=15','dombarker@100.108.41.90','timeout 60 cat '+L+rel],capture_output=True,text=True);return r.stdout if r.returncode==0 else ''
rel=m.replace('.','/')+'.lean'
gs=cat(rel);assert gs,'no gate source '+rel
open(f'inputs/gate_{safe}.lean','w').write(gs)
tt='';gt=f'inputs/gatetypes_{safe}.lean'
if m.endswith('.Funs'):
    tt=cat(m[:-5].replace('.','/')+'/Types.lean')
    if tt:open(gt,'w').write(tt)
gfiles=f'inputs/gate_{safe}.lean'+(','+gt if tt else '')
r=subprocess.run(['python3','-B','PCQL_automap.py',gfiles,f'{fd}/Funs.lean,{fd}/Types.lean',f'gen/nm_{safe}_{tag}.json'],capture_output=True,text=True);print(r.stdout.strip())
cmd=['python3','-B','PCQL_gen_equalities.py','--module',m,'--tag','_'+tag,'--fresh-dir',fd,'--fresh-ns',ns,'--gate-source',f'inputs/gate_{safe}.lean','--name-map',f'gen/nm_{safe}_{tag}.json','--out',f'PRVEq_{safe}_{tag}.lean','--report',f'gen/{safe}_{tag}.report.json','--state-out',f'gen/{safe}_{tag}.state.json','--prune-fresh','--only',only,'--gate-types-source',gt if tt else f'inputs/gate_{safe}.lean']
nss=re.findall(r'(?m)^namespace\s+(\S+)',gs)
if len(nss)>1:cmd+=['--gate-namespace',nss[0]]
if prev:
    import glob,lzma
    sc=[json.load(open(f)) for f in glob.glob('PCQL_L[0-9][0-9][0-9]/receipt.json')];sc=[x for x in sc if x['module']==f'PRVEq_{safe}_{prev}'];a=sc[-1]['attempt']
    open(f'gen/{safe}_{prev}.lean-log','w').write(lzma.open(f'{a}/stdout.log.xz').read().decode())
    cmd+=['--state',f'gen/{safe}_{prev}.state.json','--lean-log',f'gen/{safe}_{prev}.lean-log']
g=subprocess.run(cmd,capture_output=True,text=True);print(g.returncode,g.stdout.strip()[-300:],g.stderr.strip()[-400:])
