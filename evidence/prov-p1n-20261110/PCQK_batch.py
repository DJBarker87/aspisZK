#!/usr/bin/env python3
"""PCQK_batch.py TAG FRESH_DIR FRESH_NS MODULE... : resolve gate source (research git; candidate whose imports equal the ledger30 export imports,
last such), fetch it and its Types sibling, build the recorded name map (PCQK_automap.py), run PCQK_gen_equalities.py with --prune-fresh.
Writes PRVEq_<M>_<TAG>.lean and gen/<M>_<TAG>.*; a summary line per module to gen/PCQK_BATCH_<TAG>.jsonl."""
import sys,json,re,subprocess,os
sys.dont_write_bytecode=True
H=os.path.dirname(os.path.abspath(__file__));R='/Users/dominic/ZK'
S='/private/tmp/claude-501/-Users-dominic-ZK/e51a42a3-64c9-4a23-9ea1-f7bf410e2db1/scratchpad/'
tag,fd,ns,*mods=sys.argv[1:]
ms=json.load(open(S+'modsrc.json'))
imp={}
for l in open(H+'/../ledger30-20261111/NNN_EXPECTED_IMPORTS.jsonl'):
    d=json.loads(l);imp[d['module']]=set(d['imports'])-{'Init'}
def show(p):return subprocess.run(['git','-C',R,'show','research:'+p],capture_output=True,text=True).stdout
OT=os.environ.get('OUTTAG',tag)
log=open(f'{H}/gen/PCQK_BATCH_{tag}.jsonl','a')
for m in mods:
    safe=m.replace('.','_');cands=ms.get(m,[]);good=[p for p in cands if set(re.findall(r'(?m)^import\s+(\S+)',show(p)))-{'Init'}==imp.get(m)]
    if not good: log.write(json.dumps(dict(module=m,status='NO_GATE_SOURCE',cands=len(cands)))+'\n');continue
    p=good[-1];gate=f'inputs/gate_{safe}.lean';open(f'{H}/{gate}','w').write(show(p))
    tp=None
    if m.endswith('.Funs'):tp=p[:-len('Funs.lean')]+'Types.lean'
    elif 'Funs' in os.path.basename(p):tp=p.replace('Funs','Types')
    gt=f'inputs/gatetypes_{safe}.lean'
    tt=show(tp) if tp else ''
    if tt:open(f'{H}/{gt}','w').write(tt)
    gfiles=gate+(','+gt if tt else '')
    r=subprocess.run(['python3','-B','PCQK_automap.py',gfiles,f'{fd}/Funs.lean,{fd}/Types.lean',f'gen/nm_{safe}_{tag}.json'],cwd=H,capture_output=True,text=True)
    cmd=['python3','-B','PCQK_gen_equalities.py','--module',m,'--tag','_'+tag,'--fresh-dir',fd,'--fresh-ns',ns,'--gate-source',gate,'--name-map',f'gen/nm_{safe}_{tag}.json',
         '--out',f'PRVEq_{safe}_{OT}.lean','--report',f'gen/{safe}_{OT}.report.json','--state-out',f'gen/{safe}_{OT}.state.json','--prune-fresh']
    cmd+=['--gate-types-source',gt if tt else gate]
    if len(re.findall(r'(?m)^namespace\s+(\S+)',open(f'{H}/{gate}').read()))>1:cmd+=['--gate-namespace',re.findall(r'(?m)^namespace\s+(\S+)',open(f'{H}/{gate}').read())[0]]
    prev=os.environ.get('PREV')
    if prev:
        import glob,lzma
        sc=[json.load(open(f)) for f in glob.glob(H+'/PCQK_L[0-9][0-9][0-9]/receipt.json')]
        sc=[r for r in sc if r['module']==f'PRVEq_{safe}_{prev}']
        if not sc:continue
        a=sc[-1]['attempt'];open(f'{H}/gen/{safe}_{prev}.lean-log','w').write(lzma.open(f'{H}/{a}/stdout.log.xz').read().decode())
        cmd+=['--state',f'gen/{safe}_{prev}.state.json','--lean-log',f'gen/{safe}_{prev}.lean-log']
    g=subprocess.run(cmd,cwd=H,capture_output=True,text=True)
    try:rep=json.loads(g.stdout.strip().splitlines()[-1])
    except Exception:rep={}
    log.write(json.dumps(dict(module=m,source=p,ncand=len(cands),ngood=len(good),automap=r.stdout.strip(),rc=g.returncode,report=rep,err=g.stderr.strip()[-200:]))+'\n');log.flush()
    print(m,g.returncode,rep.get('common_declarations'),g.stderr.strip()[-100:])
