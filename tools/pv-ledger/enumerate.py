#!/usr/bin/env python3
"""Reproduce the conservative function/call inventory using read-only git objects."""
import hashlib
import json
import lzma
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'evidence/pv-ledger-20261108'
PINS = {
 'slice': ('codex/pv-stx-20261104', '55002ec0e2eecdcafc22d27d8c97dde5954268c1'),
 'thread': ('codex/pv-evhB-20261103', '0ba0c659c9bc5fc446e4ac4cd09f0e145339f1f1'),
}

def git(rev, path):
    return subprocess.check_output(['git', 'show', f'{rev}:{path}'], cwd=ROOT)

def load(rev, path):
    raw = git(rev, path)
    if path.endswith('.xz'):
        raw = lzma.decompress(raw)
    return json.loads(raw), hashlib.sha256(raw).hexdigest()

def walk(o):
    if isinstance(o, dict):
        yield o
        for v in o.values():
            yield from walk(v)
    elif isinstance(o, list):
        for v in o:
            yield from walk(v)

def name(parts):
    result = []
    for p in parts:
        if 'Ident' in p:
            result.append(p['Ident'][0])
        elif 'Impl' in p:
            result.append('impl[' + (str(p['Impl']['Trait']) if 'Trait' in p['Impl'] else 'inherent') + ']')
        elif 'Closure' in p:
            result.append('closure[' + str(p['Closure']) + ']')
    return '::'.join(result)

def key(o):
    if 'HashConsedValue' in o:
        return o['HashConsedValue'][0]
    return o.get('Deduplicated')

def target(c, path):
    k = c.get('Regular', {}).get('kind', {})
    if 'Fun' in k:
        f = k['Fun']
        if 'Regular' in f:
            return [f['Regular']]
        return ['builtin:' + json.dumps(f['Builtin'], sort_keys=True, separators=(',', ':'))]
    if 'Trait' in k:
        t, m = k['Trait']
        mapping = ({1670: 6, 1686: 8} if path == 'slice' else
                   {38389: 220, 38321: 208, 38973: 15, 38964: 18})
        return [mapping.get(key(t), f'trait:{key(t)}:{m}')]
    if 'Dynamic' in c:
        # Source-selected TLS initializer tokens; both alternatives retained.
        return [468, 469]
    return ['descriptor:' + hashlib.sha256(json.dumps(c, sort_keys=True).encode()).hexdigest()[:16]]

def generate():
    rows, inputs = [], []
    for path, (branch, rev) in PINS.items():
        native_signatures = {}
        if path == 'slice':
            base = 'evidence/pv-stx-20261104/SLICE/'
            cohorts = {}
            for n in [94906, 94915, 94917]:
                p = f'{base}N{n}/generated/NativeInstructions.json'
                d, sha = load(rev, p)
                cohorts[n] = {f['function']: f for f in d['functions']}
                inputs.append(dict(path=path, branch=branch, revision=rev, artifact=p, sha256=sha))
            fs = dict(cohorts[94917])
            fs.update(cohorts[94906])
            for i in [31, 35]:
                fs[i] = cohorts[94915][i]
            for i in [47, 48, 58, 59, 60]:
                fs[i] = cohorts[94917][i]
            emitted = {i for i, f in fs.items() if 'body' in f['code']}
            syntax = {i: f'lean/PV_STX2_SliceF{i}.lean' for i in emitted}
            for i in [31, 35]:
                syntax[i] = f'lean/PV_STX2_Source7CtorF{i}.lean'
            for i in [47, 48, 58, 59, 60]:
                syntax[i] = f'lean/PV_STX2_Source7AllocF{i}.lean'
            # Callback bodies passed through from_fn/wrap_mut_1.
            semantic = {2: [5], 4: [7]}
            boundary = {}
        else:
            meta_path = 'evidence/pv-evhB-20261103/thread-line/generated/N95807/OrderedFamilies.llbc.xz'
            meta, meta_sha = load(rev, meta_path)
            assert meta['has_errors'] is False
            native_signatures = {f['def_id']: f['signature'] for f in meta['translated']['fun_decls'] if f}
            inputs.append(dict(path=path, branch=branch, revision=rev, artifact=meta_path, sha256=meta_sha))
            p = 'evidence/pv-evhB-20261103/thread-line/generated/N95808/generated/NativeInstructions.json.xz'
            d, sha = load(rev, p)
            inputs.append(dict(path=path, branch=branch, revision=rev, artifact=p, sha256=sha))
            fs = {f['function']: f for f in d['functions']}
            # The original-entry installed resolver, plus the now executed Packet bodies.
            emitted = {0,1,2,5,6,17,170,125,219,316,220,208,15,164,166,270,361,
                       124,126,216,218,315,222,443,458,537}
            syntax = {i: f'lean/PV_THR2_F{i}.lean' for i in emitted}
            semantic = {318: [316], 170: [18], 361: [214]}
            boundary = {268: 'thread-5: outermost handles Vec constructor at 7894; downstream of OwnInit',
                        468: 'thread-3: source-selected TLS thunk, RunEntryDynamic.children',
                        469: 'thread-3: source-selected TLS thunk, RunEntryDynamic.children',
                        214: 'executed clone specialization D782/D784; emitted opaque body, named full-reply child'}
        pending, seen = [0], set()
        while pending:
            i = pending.pop()
            if i in seen:
                continue
            seen.add(i)
            f = fs.get(i) if isinstance(i, int) else None
            body = bool(f and 'body' in f['code'] and i in emitted)
            calls = []
            if body:
                for c in walk(f['code']):
                    if 'call_identity' in c:
                        for t in target(c['callee'], path):
                            calls.append(dict(site=c['call_identity']['statement'], target=t,
                                              source_path=c['call_identity']['path']))
                for node in walk(f['code']):
                    op = node.get('opcode')
                    if op in ('Native.CopyNonOverlapping', 'Native.Drop'):
                        ident = node['identity']
                        calls.append(dict(site=ident['statement'],
                            target='builtin:CopyNonOverlapping' if op.endswith('CopyNonOverlapping') else 'builtin:Drop',
                            source_path=ident['path']))
                # Deduplicate nesting represented both natively and as emitted instructions.
                calls = list({(c['site'], str(c['target'])): c for c in calls}.values())
            for t in semantic.get(i, []):
                if not any(c['target'] == t for c in calls):
                    calls.append(dict(site='documented-dispatch', target=t, source_path=[]))
            pending.extend(c['target'] for c in calls)
            rid = f'{path}:f{i}' if isinstance(i, int) else f'{path}:{i}'
            for c in calls:
                t = c['target']
                c['row'] = f'{path}:f{t}' if isinstance(t, int) else f'{path}:{t}'
            code_kind = ('Structured' if f and 'body' in f['code'] else
                         f['code'].get('opcode', 'Builtin') if f else 'Builtin')
            row = dict(id=rid, emitted_id=i, source_name=name(f['item_meta']['name']) if f else str(i),
                       path=path, kind='BODY' if body else 'LEAF', emitted_kind=code_kind,
                       callees=sorted({c['row'] for c in calls}), call_sites=calls,
                       source=dict(branch=branch, revision=rev, syntax=syntax.get(i) if body else None,
                                   item_meta=f['item_meta'] if f else None,
                                   signature=native_signatures.get(i) if path=='thread' else (f['code'].get('entry',{}).get('signature') if f else None)),
                       disposition=('EXECUTED' if body else boundary.get(i,
                           'named full-reply child; thread-2/3' if path == 'thread' else
                           'named full-reply native/opaque child; documented primitive semantics where applicable')),
                       status='OPEN', evidence=[], missing=['No B-y call-entry contract theorem with complete reply/frame and callee instantiation evidence.'])
            if path == 'slice' and i == 0:
                row['aliases'] = ['Programs.source7', 'StateOnlyTraceFoundation::clone']
                row['root'] = True
            if path == 'slice' and i == 9:
                row['aliases'] = ['16-column loop body', 'try_from_fn_erased']
            rows.append(row)
    rows.append(dict(id='thread:OwnInit', emitted_id='F0->f361@14756',
        source_name='OwnInit (composition root; not a separate emitted function)', path='thread',
        kind='BODY', emitted_kind='CompositionRoot', root=True,
        callees=['thread:f0'], call_sites=[], source=dict(branch=PINS['thread'][0], revision=PINS['thread'][1], syntax=None),
        disposition='Composition to the ThreadInit box; f361 return remains a separate obligation.',
        status='OPEN', evidence=[], missing=['OwnInitClosure.closed and complete branch composition do not exist.']))
    rows.sort(key=lambda r: (r['path'], isinstance(r['emitted_id'], str), str(r['emitted_id']).zfill(8)))
    result = dict(schema_version=1, ruling='B-y / LOG D860', source_pins=inputs,
        enumeration_policy='Conservative syntactic call closure: includes alternate return/error/cleanup calls of executed bodies. Stops at the installed named-child boundary. Callback/trait dispatch edges are explicit. No claim that every syntactic call occurs on one trace.',
        qualification='Translator patch owner acceptance and compiler/source association obligations are retained. No privacy endpoint premise is removed by this ledger.', rows=rows)
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / 'enumeration.json').write_text(json.dumps(result, indent=2) + '\n')
    return result

if __name__ == '__main__':
    d = generate()
    for path in PINS:
        subset = [r for r in d['rows'] if r['path'] == path]
        print(path, len(subset), 'BODY', sum(r['kind']=='BODY' for r in subset), 'LEAF', sum(r['kind']=='LEAF' for r in subset))
