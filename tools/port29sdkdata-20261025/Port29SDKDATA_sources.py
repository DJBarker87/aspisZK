#!/usr/bin/env python3
"""Immutable source-copy assessment and newer cut transport availability only."""
import hashlib
import json
from pathlib import Path
import resource
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
E = ROOT / 'evidence/port29sdkdata-20261025'
T = Path(__file__).resolve().parent
B = 'docs/research/100bit-spend-path-20261013/'
C = B + 'lean-candidates/s126-caller-boundary-20261021/'
PUB = Path('/private/tmp/s126-sdk-current-9acc-proof-refresh-20261024-v1')
start = time.monotonic()
pins = []


def sha(b):
    return hashlib.sha256(b).hexdigest()


def get(rev, path):
    b = subprocess.check_output(['git', 'show', rev + ':' + path], cwd=ROOT)
    pins.append(dict(revision=rev, path=path, sha256=sha(b), bytes=len(b)))
    return b


def write(path, data):
    with path.open('x') as f:
        json.dump(data, f, indent=2)
        f.write('\n')


request = json.loads((PUB / 'metadata/request.json').read_text())
factor_manifest = json.loads(get('0d373458d3', B + 'evidence/s126-current-caller-20261021/s6-sdk-first-factor-20261024/declarations.json'))
root_sources = json.loads(get('7b3ff55fffc', 'evidence/port28rootexport-20261024/Port28ROOTEXPORT_sources.json'))
assert len(factor_manifest['selections']) == 14
rows = []
chunks = []
for row in factor_manifest['selections']:
    b = get(row['revision'], row['path'])
    assert sha(b) == row['source_sha256']
    src = b.decode()
    pos = src.index(row['start'])
    stop = src.index(row['end'], pos) if row['end'] is not None else len(src)
    body = src[pos:stop]
    assert sha(body.encode()) == row['body_sha256']
    old = root_sources['sources'][row['module']]
    assert old['text'].encode() == b and old['origin']['sha256'] == sha(b)
    chunks.append(row['header'] + body + row['footer'])
    rows.append(dict(module=row['module'], source_revision=row['revision'], source_path=row['path'],
                     original_source_sha256=sha(b), root_source_copy_sha256=sha(old['text'].encode()),
                     source_copy_status='BYTE IDENTICAL', selected_span_sha256=sha(body.encode()),
                     emitted_span_sha256=sha(body.encode()), start=row['start'], end=row['end'],
                     compiled_ConstantInfo_equality='NOT RUN; literal span equality does not establish it'))
content = (factor_manifest['imports'] + '\n'.join(chunks) + '\nend\n').encode()
assert sha(content) == factor_manifest['source_sha256']
primary = []
for module, row in request['targets'].items():
    source = row['source']
    b = get(source['revision'], source['path'])
    assert sha(b) == source['sha256'] and len(b) == source['bytes']
    if module == 'S6SdkDependencyFactorV1':
        assert b == content
    primary.append(dict(module=module, source=source, published_original_object_sha256=row['published_object_sha256'],
                        assessment='Immutable source bytes checked; published object/source association reused, no new compiler identity gate'))

# Exact accepted implementation text is retained for review, not compiled here.
helper_path = B + 'lean/Port18COHERENCE_CompatibilityLoad.lean'
helper = get('904745b496', helper_path)
text = helper.decode()
body = text[text.index('def sameDeclaration'):text.index('\ndef load')]
dest = T / 'Port29SDKDATA_accepted-helper.lean.txt'
with dest.open('x') as f:
    f.write(body)
reviewed = json.loads(get('0d373458d3', B + 'evidence/s126-current-caller-20261021/s6-sdk-source-cuts-20261024/declaration-audit-helper.json'))
assert sha(helper) == reviewed['source_sha256'] and sha(body.encode()) == reviewed['copied_body_sha256']
helper_assessment = dict(revision='904745b496', path=helper_path, source_sha256=sha(helper),
                         exact_copied_body_sha256=sha(dest.read_bytes()),
                         copy_status='EXACT accepted sameDeclaration/readComplete body; no changes, not executed',
                         streaming_limit='readComplete returns compacted data without region ownership; a streaming diagnostic must retain/free readModuleDataParts regions explicitly before returning only owned strings. This file alone is not a ready streaming diagnostic.')

cuts = json.loads(get('0d373458d3', B + 'evidence/s126-current-caller-20261021/s6-sdk-source-cuts-20261024/targets.json'))
modules = {Path(f['relative']).as_posix()[len('transport/'):-len('.olean')].replace('/', '.')
           for f in json.loads((PUB / 'manifest.json').read_text())['files']
           if f['relative'].startswith('transport/') and f['relative'].endswith('.olean')}
cut_rows = []
for module, attempt in cuts['targets'].items():
    source = get('0d373458d3', C + module + '.lean')
    receipt_path = B + 'evidence/s126-current-caller-20261021/' + attempt + '/receipt.json'
    receipt = json.loads(get('0d373458d3', receipt_path))
    # Only reuse owner receipts and check transport absence; do not repeat the six-target audit.
    cut_rows.append(dict(module=module, immutable_source_sha256=sha(source), receipt_path=receipt_path,
                         receipt_source_sha256=receipt['source_sha256'], reused_exit_status=receipt['exit_status'],
                         reused_full_print_axioms=receipt['print_axioms'],
                         included_in_CURRENT_raw_release=module in modules,
                         new_compiler_or_kernel_validation=False))
assert not any(r['included_in_CURRENT_raw_release'] for r in cut_rows)
refresh_source = (PUB / 'metadata/sdk-current-entry-privileges-replay-v1-source.lean').read_bytes()
old_refresh_source = get('97caa13d92', B + 'lean/S2W_EntryPrivileges.lean')
assert refresh_source == old_refresh_source
refresh_receipt = json.loads((PUB / 'metadata/sdk-current-entry-privileges-replay-v1-receipt.json').read_text())

write(E / 'Port29SDKDATA_sources.json', dict(
    schema='Port29SDKDATA-immutable-source-and-availability-v1',
    source_revision=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
    command=[sys.executable, '-B', str(Path(__file__).resolve())], tool_sha256=sha(Path(__file__).read_bytes()),
    immutable_git_pins=pins, factor_source_spans=rows, primary_targets=primary,
    exact_factor_reconstruction_sha256=sha(content), compiled_factor_vs_original_equality='NOT RUN',
    accepted_helper=helper_assessment, newer_cuts=cut_rows,
    proof_source_refresh=dict(before_source_sha256=sha(old_refresh_source), after_source_sha256=sha(refresh_source),
        source_status='BYTE IDENTICAL; dependency proof object changes remain explicit',
        old_object_sha256='dd69525c1045fbda9d3aa5b07abf7f23e998bd4f99862baa4623cbb81827a9d1',
        new_object_sha256='828531202c24658cd2b220cd9d2c67a62aac1d65dd007184dfcd60ab3a205978',
        reused_full_print_axioms=refresh_receipt['print_axioms'],
        four_public_type_comparisons='Reused released same_type=true for guards/readonly/writable/accepted_privileges; no new type comparison'),
    premise_changes='NONE; no theorem statement or proof premise changed in this job',
    new_print_axioms='N/A: source-only noncompiler audit', exit_status=0, wall_seconds=time.monotonic()-start,
    peak_rss_bytes=resource.getrusage(0).ru_maxrss, swaps=resource.getrusage(0).ru_nswap,
    runtime=dict(version=sys.version, executable=sys.executable, executable_sha256=sha(Path(sys.executable).resolve().read_bytes())),
    lean_invocations=0))
print(json.dumps(dict(status='PASS source-copy and availability audit', factor_spans=len(rows),
                     newer_cut_raw_modules_available=0, copied_helper_sha256=sha(dest.read_bytes()),
                     wall_seconds=time.monotonic()-start, peak_rss_bytes=resource.getrusage(0).ru_maxrss)))
