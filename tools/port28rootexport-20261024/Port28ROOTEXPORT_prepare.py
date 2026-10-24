#!/usr/bin/env python3
"""Git-only original ROOT input preparation. No host, cache or Lean execution."""
import argparse
import hashlib
import json
import os
import threading
from pathlib import Path
import re
import resource
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'evidence/port28rootexport-20261024'
ENTRY = 'e37ef5182a83bdd1104eeec17da1f669a8c0a778'
REQUEST = '93de4606f3'
CURRENT = '9acc015544c36891712af984c0a9604a39425eeb'
ORIGINAL = '97caa13d923fb7b112fed5f7a1f45e210ff70602'
BASE = 'docs/research/100bit-spend-path-20261013/'
inputs = {}

def sha(b):
    return hashlib.sha256(b).hexdigest()

def blob(rev, path):
    raw = subprocess.check_output(['git', 'show', rev + ':' + path], cwd=ROOT)
    inputs[rev + ':' + path] = dict(revision=rev, path=path, sha256=sha(raw), bytes=len(raw))
    return raw

def load(rev, path):
    return json.loads(blob(rev, path))

def standard(lines):
    assert lines
    for line in lines:
        if 'does not depend on any axioms' in line:
            continue
        m = re.search(r'\[([^]]*)\]', line)
        assert m and set(m[1].replace(' ', '').split(',')) <= {'propext', 'Classical.choice', 'Quot.sound'}, line

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--write', action='store_true')
    args = ap.parse_args()
    start = time.monotonic()
    # This tool never reads binary objects or invokes a compiler. Bound preprocessing.
    # macOS rejects lowering RLIMIT_AS; monitor aggregate self/child RSS instead.
    # Stop at448MiB, reserving64MiB below the512MiB preprocessing ceiling.
    def monitor():
        while True:
            table = subprocess.check_output(['ps', '-axo', 'pid=,ppid=,rss='], text=True)
            rows = [tuple(map(int, line.split())) for line in table.splitlines()]
            owned = {os.getpid()}
            while True:
                expanded = owned | {pid for pid, ppid, rss in rows if ppid in owned}
                if expanded == owned:
                    break
                owned = expanded
            if sum(rss * 1024 for pid, ppid, rss in rows if pid in owned) >= 448 * 1024**2:
                os.write(2, b'PREPROCESSING AGGREGATE RSS STOP\n')
                os._exit(137)
            time.sleep(0.05)
    threading.Thread(target=monitor, daemon=True).start()
    request = load(REQUEST, 'evidence/port27sdk-20261024/Port27SDK_export-request.json')
    audit = load(REQUEST, 'evidence/port27sdk-20261024/Port27SDK_audit.json')
    prior_check = load(REQUEST, 'evidence/port27sdk-20261024/Port27SDK_check.receipt.json')
    assert prior_check  # full immutable receipt retained among hashed inputs; not a new kernel gate
    for name in ['README.md', 'INTEGRATION.md', 'EXPORT-REQUEST.md']:
        blob(REQUEST, 'evidence/port27sdk-20261024/' + name)
    selection = load(CURRENT, BASE + 'evidence/s126-current-caller-20261021/s6-sdk-first-factor-20261024/declarations.json')
    assert request['historical_factor_revision'] == ORIGINAL
    assert request['current_revision'] == CURRENT
    assert len(selection['selections']) == 14
    pieces, spans, sources, seeds = [], [], {}, []
    # Full original sources are retained as literal data, not compiled or relabelled.
    def source(module):
        path = BASE + 'lean/' + module + '.lean'
        raw = blob(ORIGINAL, path)
        sources[module] = dict(origin=inputs[ORIGINAL + ':' + path], text=raw.decode())
        return raw
    for row, prior in zip(selection['selections'], audit['exact_source_selections']):
        raw = source(row['module'])
        assert sha(raw) == row['source_sha256'] == prior['source_sha256']
        text = raw.decode()
        assert text.count(row['start']) == 1
        lo = text.index(row['start'])
        hi = text.index(row['end'], lo) if row['end'] is not None else len(text)
        body = text[lo:hi]
        assert sha(body.encode()) == row['body_sha256'] == prior['body_sha256']
        wrapped = row['header'] + body + row['footer']
        pieces.append(wrapped)
        namespaces = re.findall(r'^namespace (\S+)', wrapped, re.M)
        assert len(namespaces) == 1, row['module']
        namespace = namespaces[0]
        declared = re.findall(r'^\s*(?:private )?(?:noncomputable )?(?:def|abbrev|structure|inductive|theorem)\s+(\S+)', body, re.M)
        assert declared == prior['declarations']
        qualified = [namespace + '.' + n for n in declared]
        for name in qualified:
            seeds.append(dict(module=row['module'], name=name, origin='exact factor span',
                              generated_family='REQUIRED; actual emitted/private/ctor/projection/recursor inventory not yet acquired'))
        spans.append(dict(module=row['module'], namespace=namespace, start_line=prior['start_line'],
                          end_line=prior['end_line'], body_sha256=sha(body.encode()), text=body,
                          source_sha256=sha(raw), qualified_source_declarations=qualified))
    factored = selection['imports'] + '\n'.join(pieces) + '\nend\n'
    assert factored.encode() == blob(CURRENT, selection['source'])
    assert sha(factored.encode()) == selection['source_sha256']
    # Add only named original root groups; no namespace-wide multiproof/interface selection.
    extra = {
        'S2W_D189Consolidation': ['accepted_run', 'wrapper_frames'],
        'S2W_NativeConsolidation': ['FirstCut', 'SecondCut', 'SourceCuts', 'cuts_of_acceptance'],
        'S2W_ScheduledConsolidation': ['accepted_run'],
        'S2W_DigestExtraction': ['AeneasExtraction', 'sourceBoundary', 'native_binding'],
    }
    for module, names in extra.items():
        text = source(module).decode()
        assert 'namespace AspisR1.' + module in text
        for name in names:
            assert re.search(r'^(?:structure|def|theorem|abbrev) ' + name + r'\b', text, re.M), (module, name)
            fq = 'AspisR1.' + module + '.' + name
            if not any(s['name'] == fq for s in seeds):
                seeds.append(dict(module=module, name=fq, origin='required ROOT seed', generated_family='REQUIRED; not acquired'))
    for module in ['S2TrustedSdkBorrow', 'S2W_TrustedStd', 'AdapterRwRuntimeAdmission',
                   'S2W_ExpandedChildren', 'S2W_TraceSplice', 'S2W_ExtractionBoundary',
                   'S2W_Trace', 'S2W_AuthenticatedInputs']:
        source(module)
    receipts = {}
    historical_pins = {}
    for n in ['109', '110']:
        config = load(ENTRY, 'tools/s2w-20261023/lean-' + n + '.json')
        r = load(ENTRY, 'evidence/s2w-20261023/lean-' + n + '/receipt.json')
        assert r['exit_status'] == 0
        assert config['env']['LEAN_PATH'] == r['env']['LEAN_PATH']
        assert r['deps_fingerprint']['lean_binary_sha256'] == 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
        standard(r['print_axioms'])
        for module, pin in r['deps_fingerprint']['selected_objects'].items():
            historical_pins[module] = dict(**pin, assessment='REUSED direct dependency receipt pin; object NOT opened', receipt='lean-' + n)
        receipts['lean-' + n] = dict(assessment='REUSED historical compile; no new identity gate', receipt=r)
    assert receipts['lean-109']['receipt']['source_hashes']['S2W_D189Consolidation.lean'] == sources['S2W_D189Consolidation']['origin']['sha256']
    expected = {'S2W_D189Consolidation.olean': ('2968435770a732738bbfd9e09b7efa3d2d649df5899d8bb0cdbf56e99cadedd8', 376736),
                'S2W_D189Wrappers.olean': ('767215ab84602f604bff75713c814e79a8954bdd6464fd747b2cd37f96106443', 349320),
                'S2W_ScheduledConsolidation.olean': ('ee41f8ace38ec3ddf520d3626fa0d0000f62c3322d67b9cb015a6bbadb41dd54', 226128)}
    for module, (digest, size) in expected.items():
        assert historical_pins[module]['sha256'] == digest and historical_pins[module]['bytes'] == size
    pattern = 'evidence/port18coherence-20261024/lean-011/sources/Port18COHERENCE_RootSnapshot.lean'
    accepted_tool = blob(ENTRY, pattern).decode()
    assert 'value? (allowOpaque := true)' in accepted_tool
    assert 'saveModuleData' in accepted_tool and 'regions.reverse.forM CompactedRegion.free' in accepted_tool
    # Preserve the original tool exactly as data, without executing its main/#eval.
    sources['REUSED_Port18_RootSnapshot_tool'] = dict(origin=inputs[ENTRY + ':' + pattern], text=accepted_tool)
    source_bundle = dict(schema='Port28ROOTEXPORT-original-source-data-v1', sources=sources, exact_spans=spans,
                         assessment='immutable source bytes only; no emitted ConstantInfo or source/object identity established')
    plan = dict(schema='Port28ROOTEXPORT-bounded-root-seeds-v1', seeds=seeds,
                count=len(seeds), scope='source names only; emitted names and private/generated groups remain unacquired',
                closure_policy='types AND allowOpaque values; all mutual/ctor/recursor groups and rule RHS; iterate all origins until fixed point; no first-wins',
                unresolved_status='NOT COMPUTED; no object data acquired', duplicates_status='NOT COMPUTED; no object data acquired',
                graph_status='NOT COMPUTED; source imports are not ConstantInfo edges',
                historical_direct_object_pins=historical_pins,
                ordered_original_lean_path=receipts['lean-109']['receipt']['env']['LEAN_PATH'].split(':'),
                raw_transport_status='NOT PRODUCED', parts_status='main historical pins do not pin server/private parts',
                local_lean_precondition='released own object-part inventory plus warm pinned core and source/AST/input preflight; no project trusted imports')
    manifest = dict(schema='Port28ROOTEXPORT-offline-preparation-v1', status='SOURCE_PREPARATION_ONLY; HOST_GATE_BLOCKED',
                    source_revision=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
                    original_source_revision=ORIGINAL, current_factor_text_revision=CURRENT,
                    inputs=sorted(inputs.values(), key=lambda x:(x['revision'], x['path'])), historical_receipts=receipts,
                    new_object_observations=[], transports=[], emitted_declarations=[],
                    new_lean_invocations=0, allocated_lean_slots=1, unused_allocated_lean_slots=1,
                    host_accesses=0, new_print_axioms='N/A: data preparation only; no theorem',
                    assumptions='unchanged; none discharged or added', whole_experiment='not established', security_targets='both not yet established')
    outputs = {'Port28ROOTEXPORT_sources.json': source_bundle, 'Port28ROOTEXPORT_seed-plan.json': plan,
               'Port28ROOTEXPORT_manifest.json': manifest}
    for name, value in outputs.items():
        data = (json.dumps(value, indent=2) + '\n').encode()
        assert len(data) <= 5_000_000
        if args.write:
            (OUT / name).write_bytes(data)
        else:
            # Revision is the preparation revision, not a reason to rewrite evidence.
            if name.endswith('manifest.json'):
                recorded = json.loads((OUT / name).read_bytes())
                value['source_revision'] = recorded['source_revision']
                data = (json.dumps(value, indent=2) + '\n').encode()
            assert (OUT / name).read_bytes() == data, name
    usage = resource.getrusage(resource.RUSAGE_SELF)
    print(json.dumps(dict(status=manifest['status'], exact_spans=14, source_seed_names=len(seeds),
                          immutable_inputs=len(inputs), new_lean_invocations=0, host_accesses=0,
                          wall_seconds=time.monotonic()-start, peak_rss_bytes=usage.ru_maxrss,
                          swaps=usage.ru_nswap, print_axioms=manifest['new_print_axioms'])))

if __name__ == '__main__':
    main()
