#!/usr/bin/env python3
"""Close constant LLVM callback flow only when final ELF callers corroborate it.
No SSA memory load, escaping callback or mismatched caller multiset is closed.
"""
import collections,hashlib,json
from pathlib import Path
H=Path('/home/dombarker/project-offloads/codex-cx-s10-repin2-20261023')
P=H.parent/'codex-cx-s10-repin2-20261023';F=H.parent/'codex-cx-s10-repin2-20261023'
x=json.loads((H/'indirect.json').read_text());elf=json.loads((F/'elf-crosscheck.json').read_text())
rawrows=json.loads((P/'elf-raw-input.json').read_text());out=[]
for mode in ['default','devnet','pool']:
    rawmap={a:int(r['id'].split(':')[2],16) for r in rawrows if r['artifact']==mode for a in r['raw_symbol_aliases']}
    g=elf['artifacts'][mode];taken={p['target'] for p in g['address_taken_functions']}
    def solve(o):
        kind=o['kind']
        if kind=='null':return dict(closed=True,values=['null'])
        if kind=='symbol':return dict(closed=o['raw'] in rawmap,values=[o['raw']])
        if kind!='formal':return dict(closed=False,reason=kind,definition=o.get('definition'))
        raw=o['raw'];addr=rawmap.get(raw);sources=[]
        expected=collections.Counter(c['caller'] for c in g['calls'] if c['kind']=='direct' and c.get('target')==addr)
        incoming=[r for r in o['incoming'] if r['caller'] in rawmap]
        observed=collections.Counter(rawmap[r['caller']] for r in incoming)
        for r in incoming:sources.append(dict(path=r['path'],line=r['line'],caller=r['caller'],actual=r['actual'],resolution=solve(r['origin'])))
        checks=dict(function_is_linked=addr is not None,address_not_taken=addr not in taken,
            nonempty_direct_callers=bool(expected),final_caller_multiset_equal=observed==expected)
        closed=all(checks.values()) and all(s['resolution']['closed'] for s in sources)
        return dict(closed=closed,raw=raw,parameter=o['parameter'],checks=checks,
            expected_final_callers=dict(expected),observed_final_callers=dict(observed),incoming=sources,
            values=sorted({v for s in sources for v in s['resolution'].get('values',[])}) if closed else [])
    for s in x['sites']:
        if s['mode']!=mode:continue
        candidates=[dict(raw=c['raw'],path=c['path'],llvm_line=c['llvm_line'],resolution=solve(c['operand_origin'])) for c in s['llvm_candidates']]
        allclosed=bool(candidates) and all(c['resolution']['closed'] for c in candidates)
        values=sorted({v for c in candidates for v in c['resolution'].get('values',[])}) if allclosed else []
        status='LLVM_CALLBACK_CONSTANT' if allclosed and values and values!=['null'] else 'LLVM_CALLBACK_NULL' if allclosed and values==['null'] else 'OPEN'
        out.append(dict(mode=mode,address=s['address'],caller=s['caller'],caller_symbols=s['caller_symbols'],status=status,values=values,candidates=candidates,
            trust_scope='Frozen compiler preserves its LLVM calling convention and SSA semantics; final raw symbols/caller multiplicities and no relocated function-address escape corroborate the parameter flow. This is compiler evidence, not a Lean source refinement or an all-path machine simulation.'))
p=H/'resolved.json';r=dict(schema='s10-pass4-constant-callback-flow-v1',sites=out,counts=dict(collections.Counter(s['status'] for s in out)),
    inputs={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in [H/'indirect.json',F/'elf-crosscheck.json',P/'elf-raw-input.json']},
    generator='tools/s10-inventory5-20261021/resolve-host.py')
p.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
print(json.dumps(dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size,counts=r['counts'])),flush=True)
