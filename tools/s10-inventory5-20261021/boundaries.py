#!/usr/bin/env python3
"""Per-instruction dispatch contracts. A specification is never a Lean proof."""
import argparse,collections,hashlib,json
from pathlib import Path
R=Path(__file__).resolve().parents[2]
B=R/'docs/research/100bit-spend-path-20261013'
E=B/'evidence/s10-inventory5-20261021'
def load(p):return json.loads(p.read_text())
def enc(x):return (json.dumps(x,indent=2,sort_keys=True)+'\n').encode()
def build():
    resolved=load(E/'resolved.json');elf=load(B/'evidence/s10-inventory2-20261021/elf-crosscheck.json')
    specs={
      'fmt_dispatch':dict(
        abi='Frozen Rust core::fmt ABI and vtable layout at the pinned callx; data and metadata must originate from the same constructed trait object or fmt::Arguments entry.',
        precondition='The reachable Rust formatting object is live, correctly aligned and initialized; its concrete callback has the exact method ABI. The compiler preserves this provenance; the attacker cannot inject a raw callback address through serialized spend bytes.',
        normal='Invoke exactly the method selected by that object/argument, in the original call order with the original receiver, Formatter options, width/precision, and input string/character/value. Preserve every formatting write and mutable formatter/sink field, the returned fmt::Result, and short circuit on its actual Err.',
        exceptional='Retain allocator failure, nested callback failure and panic/abort behavior. Formatting failure or panic never fabricates an accepted verification result.',
        oracle='Every reachable concrete formatting callback is confined to formatting/sink state and issues no spend-oracle read, checkpoint mutation, account write or authority change. If this confinement cannot be adopted for a callback, expose its effects as an owned site instead.',
        scope='Only the listed core::fmt/core::panic::panic_info callx instructions. No owned digest callback, allocation helper, verifier arithmetic, account adapter or general arbitrary Rust trait object is covered.'),
      'boxed_error_drop':dict(
        abi='Frozen Rust drop glue and dynamically selected destructor/deallocator ABI for Box<bincode::error::ErrorKind>.',
        precondition='The Box and any nested error trait object have valid allocator and vtable provenance from the frozen reachable library path; no serialized input is treated as a vtable pointer.',
        normal='Drop each initialized payload exactly once and deallocate using the original allocator/layout; preserve destructor order and all library/allocator post-state.',
        exceptional='Retain destructor panic/abort and allocation/deallocation failure semantics. Drop cannot turn rejected input into accepted execution.',
        oracle='Reachable error payload destructors/deallocators issue no spend-oracle query, checkpoint/account mutation or authority change. A payload failing confinement remains an owned callback obligation.',
        scope='Only the listed Box<bincode::error::ErrorKind> drop callx. No other destructor is silently trusted.')}
    rows=[]
    for r in resolved['sites']:
        site=next(s for s in elf['artifacts'][r['mode']]['indirect_sites'] if s['address']==r['address'])
        row=dict(mode=r['mode'],address=r['address'],caller=r['caller'],caller_symbols=r['caller_symbols'],machine_operand=site['operand'],previous_status=r['status'])
        if r['status']!='OPEN':
            row.update(disposition='COMPILER_TARGET_FLOW',targets=r['values'],source_refinement=False)
        else:
            names=r['caller_symbols'];assert names
            if all('core::fmt' in n or 'core..fmt' in n or 'core..panic..panic_info' in n for n in names):spec='fmt_dispatch'
            elif len(names)==1 and names[0].startswith('core::ptr::drop_in_place$LT$alloc..boxed..Box$LT$bincode..error..ErrorKind'):spec='boxed_error_drop'
            else:raise AssertionError(('unclassified owned or unknown indirect caller',row))
            row.update(disposition='TRUST_BOUNDARY_SPECIFIED',specification=spec,
                adoption='Explicit trusted operational contract proposed for these exact frozen instructions. No target-flow theorem, source refinement, owner acceptance or Lean axiom is manufactured.',
                source_refinement=False)
        rows.append(row)
    assert len(rows)==152 and sum(r['disposition']=='TRUST_BOUNDARY_SPECIFIED' for r in rows)==131
    return dict(schema='s10-pass5-indirect-boundaries-v1',model='AspisR1.OraclePortFrozen2.dV_frozen2',sites=rows,specifications=specs,
        counts=dict(collections.Counter(r['disposition'] for r in rows)),
        inputs={str(p.relative_to(R)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [E/'resolved.json',B/'evidence/s10-inventory2-20261021/elf-crosscheck.json']},
        release_status='NOT_ESTABLISHED: proposed library trust must be adopted and connected to concrete source carriers; dispatch accounting does not construct the source Calls tree.')
if __name__=='__main__':
    a=argparse.ArgumentParser();a.add_argument('--check',action='store_true');args=a.parse_args();raw=enc(build());p=E/'indirect-boundaries.json';assert len(raw)<=5_000_000
    if args.check:assert p.read_bytes()==raw
    else:p.write_bytes(raw)
    print(json.dumps(dict(exit_status=0,counts=build()['counts'])))
