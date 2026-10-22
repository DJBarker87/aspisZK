#!/usr/bin/env python3
"""Independent replay and negative controls for constant callback flow."""
import collections,copy,hashlib,json,resource,subprocess,sys,time
from pathlib import Path
start=time.monotonic();R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s10-inventory4-20261021'
x=json.loads((E/'indirect.json').read_text());elf=json.loads((B/'evidence/s10-inventory2-20261021/elf-crosscheck.json').read_text())
original=json.loads((B/'evidence/s10-inventory-20261021/inventory.json').read_text());recorded=json.loads((E/'resolved.json').read_text())
def replay(operand,mode,extra_taken=()):
    rawmap={a:r['address'] for r in original['declarations'] if r.get('evidence')=='linked symbol' and r['artifact']==mode for a in r['raw_symbol_aliases']}
    g=elf['artifacts'][mode];taken={p['target'] for p in g['address_taken_functions']}|set(extra_taken)
    def go(o):
        if o['kind']=='null':return True,{'null'}
        if o['kind']=='symbol':return o['raw'] in rawmap,{o['raw']}
        if o['kind']!='formal':return False,set()
        addr=rawmap.get(o['raw'])
        expected=collections.Counter(c['caller'] for c in g['calls'] if c['kind']=='direct' and c.get('target')==addr)
        incoming=[r for r in o['incoming'] if r['caller'] in rawmap]
        observed=collections.Counter(rawmap[r['caller']] for r in incoming)
        if addr is None or addr in taken or not expected or expected!=observed:return False,set()
        values=set()
        for r in incoming:
            closed,part=go(r['origin'])
            if not closed:return False,set()
            values|=part
        return True,values
    return go(operand)
results=[]
for s in x['sites']:
    cs=[replay(c['operand_origin'],s['mode']) for c in s['llvm_candidates']]
    closed=bool(cs) and all(c[0] for c in cs);values=sorted(set().union(*(c[1] for c in cs))) if closed else []
    status='LLVM_CALLBACK_NULL' if closed and values==['null'] else 'LLVM_CALLBACK_CONSTANT' if closed and values else 'OPEN'
    r=next(r for r in recorded['sites'] if (r['mode'],r['address'])==(s['mode'],s['address']))
    assert (r['status'],r['values'])==(status,values)
    results.append((s,status))
# Each of the eight closed flows must fail if any of its evidenced final
# incoming arguments is lost or if the function address may escape.
negative=[]
for s,status in results:
    if status=='OPEN':continue
    operand=s['llvm_candidates'][0]['operand_origin'];assert operand['kind']=='formal'
    addr=s['caller'];assert not replay(operand,s['mode'],[addr])[0]
    mutated=copy.deepcopy(operand);mutated['incoming']=[];assert not replay(mutated,s['mode'])[0]
    mutated=copy.deepcopy(operand)
    def poison(o):
        if o['kind']=='formal':
            for i in o['incoming']:
                if poison(i['origin']):return True
        elif o['kind'] in ['null','symbol']:
            o.clear();o.update(kind='ssa',value='%unresolved',status='OPEN');return True
        return False
    assert poison(mutated) and not replay(mutated,s['mode'])[0]
    negative.append(dict(mode=s['mode'],address=s['address'],checks=['removed incoming','escaped callback','unknown SSA operand']))
u=resource.getrusage(resource.RUSAGE_SELF)
r=dict(target='tools/s10-inventory4-20261021/check-callbacks.py',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),exit_status=0,wall_seconds=time.monotonic()-start,peak_rss_bytes=u.ru_maxrss if sys.platform=='darwin' else u.ru_maxrss*1024,swaps=u.ru_nswap,print_axioms='N/A: compiler-flow evidence only',counts=dict(collections.Counter(status for _,status in results)),negative_controls=negative)
(E/'callback-validation.json').write_text(json.dumps(r,indent=2,sort_keys=True)+'\n');print(json.dumps(dict(exit_status=0,counts=r['counts'],negative_checks=3*len(negative))))
