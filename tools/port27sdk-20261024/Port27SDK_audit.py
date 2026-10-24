#!/usr/bin/env python3
"""Immutable Git-only SDK integration audit. Never opens an object/cache/worktree."""
from pathlib import Path
import hashlib, json, re, subprocess, sys
from functools import lru_cache
R = Path(__file__).resolve().parents[2]
E = R / 'evidence/port27sdk-20261024'
A = '9acc015544c36891712af984c0a9604a39425eeb'
BASE = '74d67bcc99a749152ee0a400876b0e2169531bfd'
HIST = subprocess.check_output(['git', 'rev-parse', '97caa13d92'], cwd=R, text=True).strip()
B = 'docs/research/100bit-spend-path-20261013/'
C = B + 'lean-candidates/s126-caller-boundary-20261021/'
P = B + 'evidence/s126-current-caller-20261021/'
inputs = {}
@lru_cache(None)
def blob(rev, path):
    raw = subprocess.check_output(['git', 'show', rev + ':' + path], cwd=R)
    inputs[rev + ':' + path] = dict(revision=rev, path=path, sha256=sha(raw), bytes=len(raw))
    return raw

def sha(raw): return hashlib.sha256(raw).hexdigest()
def load(rev, path): return json.loads(blob(rev, path))
def text(rev, path): return blob(rev, path).decode()
def code_only(raw):
    # Lean block comments nest; source prose is not a declaration.
    s = raw.decode(); out = []; i = 0; depth = 0
    while i < len(s):
        if s[i:i+2] == '/-': depth += 1; i += 2
        elif depth and s[i:i+2] == '-/': depth -= 1; i += 2
        elif not depth and s[i:i+2] == '--':
            j = s.find('\n', i); i = len(s) if j < 0 else j
        else:
            if not depth: out.append(s[i])
            i += 1
    assert depth == 0
    return ''.join(out)
def standard(lines):
    assert lines
    for line in lines:
        m = re.search(r'\[([^]]*)\]', line, re.S)
        assert m and set(m[1].replace('\n', '').replace(' ', '').split(',')) <= {'propext','Classical.choice','Quot.sound'}, line

manifest = load(A, P + 's6-sdk-first-factor-20261024/declarations.json')
rows = manifest['selections']
assert len(rows) == 14
parts = []
correspondence = []
for row in rows:
    src = blob(HIST, row['path'])
    assert sha(src) == row['source_sha256']
    s = src.decode(); assert s.count(row['start']) == 1
    start = s.index(row['start'])
    end = s.index(row['end'], start) if row['end'] is not None else len(s)
    body = s[start:end]
    assert sha(body.encode()) == row['body_sha256']
    parts.append(row['header'] + body + row['footer'])
    declarations = re.findall(r'^\s*(?:private )?(?:noncomputable )?(?:def|abbrev|structure|inductive|theorem)\s+(\S+)', body, re.M)
    correspondence.append(dict(module=row['module'], path=row['path'], source_sha256=sha(src), body_sha256=sha(body.encode()), start_line=s[:start].count('\n')+1, end_line=s[:end].count('\n')+1, declarations=declarations, equality='exact selected source bytes only; resolved ConstantInfo not compared'))
expected = manifest['imports'] + '\n'.join(parts) + '\nend\n'
assert expected.encode() == blob(A, manifest['source'])
assert sha(expected.encode()) == manifest['source_sha256']
targets = load(A, P + 's6-sdk-first-factor-20261024/targets.json')
pins = load(A, P + 's6-sdk-first-factor-import-pins.json')
byname = {}
for row in pins['modules']:
    n = row['name']; assert n not in byname or byname[n] == row
    byname[n] = row
assert len(byname) == 6614
validation = {}
for target, attempt in targets['targets'].items():
    source = blob(A, C + target + '.lean')
    receipt = load(A, P + attempt + '/receipt.json')
    assert receipt['exit_status'] == 0 and receipt['swaps'] == 0
    assert sha(source) == receipt['source_sha256'] == pins['targets'][target]['source_sha256']
    assert source == blob(A, P + attempt + '/source.lean')
    assert receipt['object_sha256'] == pins['targets'][target]['object_sha256'] == byname[target]['sha256']
    assert '-j1' in receipt['command'] and '-M4400' in receipt['command']
    standard(receipt['print_axioms'])
    assert not re.search(r'\b(sorry|axiom|admit|native_decide|bv_decide)\b|set_option (maxHeartbeats|maxRecDepth)', code_only(source))
    for dep, obj in receipt['direct_imports'].items():
        assert byname[dep]['sha256'] == obj['sha256']
    validation[target] = dict(assessment='historical A checked conditional factor scope, source-only receipt verification now; no object read or new kernel check', receipt=inputs[A + ':' + P + attempt + '/receipt.json'], command=receipt['command'], source_revision=receipt['source_revision'], exit_status=receipt['exit_status'], wall_seconds=receipt['wall_seconds'], peak_rss_bytes=receipt['peak_rss_bytes'], swaps=receipt['swaps'], print_axioms=receipt['print_axioms'])
    # The receipt's object-only import closure must be a closed named graph.
    wanted = set(pins['targets'][target]['modules']) | {target}
    todo = [target]; reached = set()
    while todo:
        n = todo.pop()
        if n in reached: continue
        reached.add(n)
        assert n in byname, n
        todo += byname[n]['imports']
    assert reached == wanted, (target, len(reached), len(wanted), sorted(reached ^ wanted)[:20])
    validation[target]['recorded_import_closure_size'] = len(reached)
# Preserve old failed approaches as old evidence, not reruns.
rejections = []
for attempt in targets['rejected']:
    r = load(A, P + attempt + '/receipt.json')
    log = text(A, P + attempt + '/time.log')
    assert r['exit_status'] == 134 and 'memory_exception' in log
    rejections.append(dict(attempt=attempt, exit_status=r['exit_status'], source_sha256=r['source_sha256'], assessment='reused historical failure; no unchanged retry'))
original = text(A, C + 'S6SdkStage1ReuseV1.lean')
assert original.replace('import S2W_D189Consolidation','import S6SdkDependencyFactorV1').replace('AspisS6SdkStage1Reuse','AspisS6SdkStage1ReuseFactored') == text(A, C + 'S6SdkStage1ReuseFactoredV1.lean')
for f in ['factor.py','check-factor.py','register-factor.py']:
    blob(A, 'tools/s6-sdk-first-20261024/' + f)
canonical = load(BASE, 'evidence/port18coherence-20261024/canonical-manifest.json')
transport = load(BASE, 'evidence/port18coherence-20261024/transport-manifest.json')
names = {d['name'] for d in canonical['declarations']}
modules = {r['module'] for r in transport['snapshots']}
seeds = ['AspisS6SdkStage1ReuseFactored.public_read', 'AspisS6SdkStage1ReuseFactored.accepted_sdk_stage1', 'AspisS1ValuesOwnedInstallation.sdk_stage1_account_numeric']
assert not names.intersection(seeds)
assert not modules.intersection(targets['targets'])
# Exact source reuse assessment for the historical canonical project module inputs.
source_assessment = []
current_paths = set(subprocess.check_output(['git','ls-tree','-r','--name-only',A],cwd=R,text=True).splitlines())
for module in canonical['modules']:
    s = module['source']
    if 'path' not in s: continue
    p = s['path']
    now = blob(A, p) if p in current_paths else None
    source_assessment.append(dict(side=module['side'], module=module['module'], path=p, historical_sha256=s['sha256'], current_sha256=sha(now) if now is not None else None, assessment='same source bytes; complete resolved declaration comparison still required' if now is not None and sha(now)==s['sha256'] else 'source differs; historical declaration reuse not justified by source' if now is not None else 'source path absent from current A tree; historical provenance only'))
for f in ['Kernel','CompatibilityLoad','CheckedDomain','CheckedPrepare','CheckedDriver','CheckedAccounting','CheckedAudit','CandidateSnapshot','RootSnapshot']:
    blob(BASE, B + 'lean/Port18COHERENCE_' + f + '.lean')
for p in ['evidence/port18validate-20261024/lean-004/receipt.json','evidence/port18validate-20261024/lean-004/stdout.log','evidence/port18final-20261024/lean-001/receipt.json','evidence/port18final-20261024/lean-001/stdout.log']:
    blob(BASE, p)
final = load(BASE, 'evidence/port18final-20261024/lean-001/receipt.json')
assert final['accepted'] and final['exit_status']==0 and final['swaps']==0
standard(final['print_axioms']); assert len(final['print_axioms'])==17
log = text(BASE, 'evidence/port18validate-20261024/lean-004/stdout.log')
assert log.count('REJECTED ')==7 and 'ACCEPTED exact valid' in log
# These are literal source statements, not newly elaborated signatures.
signatures = {}
for target, theorem in [('S6SdkStage1ReuseFactoredV1','accepted_sdk_stage1'), ('S1SdkStage1AccountNumericV1','sdk_stage1_account_numeric')]:
    s = text(A, C + target + '.lean')
    pos = s.index('theorem ' + theorem)
    end = s.index(' := by', pos)
    signatures[target] = s[pos:end] + '\n'
# Hidden full carrier sources are historical pins, never invented current sources.
for f in ['S2TrustedSdkBorrow','S2W_TrustedStd','AdapterRwRuntimeAdmission']:
    blob(HIST, B + 'lean/' + f + '.lean')
for f in ['S6CurrentFirstInstallationV1','S6CurrentStage1FirstFieldsV1','S1OwnedStage1AccountNumericV1','S1ValuesOwnedInstallationV1','S1NativePrepareBuffersV1']:
    blob(A, C + f + '.lean')
for f in ['S2W_D189Consolidation','S2W_NativeConsolidation','S2W_ExpandedChildren','S2W_TraceSplice','S2W_AuthenticatedInputs','S2W_DigestExtraction','S2W_ExtractionBoundary']:
    blob(HIST, B + 'lean/' + f + '.lean')
for f in ['Port17RELEASE_Driver','Port17RELEASE_Prepare']:
    blob(BASE, B + 'lean/' + f + '.lean')
summary = dict(schema='port27sdk-immutable-source-audit-v1', current_A=A, factor_origin=HIST, historical_port18_basis=BASE, status='PASS source/receipt audit; BLOCKED current declaration transport; logical coherence NOT established', exact_source_selections=correspondence, recorded_import_metadata_count=len(byname), historical_conditional_validation=validation, reused_resource_failures=rejections, port18=dict(immutable_A_basis=canonical['immutable_A_basis'], root_proof_basis=canonical['root_proof_basis'], selected_declarations=len(names), missing_current_seeds=seeds, missing_current_target_transports=sorted(targets['targets']), rejection_tests='seven unchanged historical rejection tests reused, not rerun', final_audit='17 historical standard-only reports; not new current SDK evidence'), historical_source_assessment=source_assessment, inputs=sorted(inputs.values(), key=lambda r:(r['revision'],r['path'])), new_lean_attempts=0, unused_worker_lean_allocation=6, native_or_release_claim=False)
d189 = text(HIST, B + 'lean/S2W_D189Consolidation.lean')
pos = d189.index('theorem accepted_run'); end = d189.index(' := by',pos)
signatures['S2W_D189Consolidation_historical'] = d189[pos:end] + '\n'
request = dict(schema='port27sdk-bounded-immutable-export-request-v1', current_revision=A, historical_factor_revision=HIST, current_directory=C, primary_seeds=seeds, targets={n: dict(source=inputs[A+':'+C+n+'.lean'], published_object_sha256=pins['targets'][n]['object_sha256'], object_assessment='hash metadata only; worker has not opened object') for n in targets['targets']}, original_factor_modules=[dict(module=r['module'], path=r['path'], source_sha256=r['source_sha256']) for r in rows], historical_enclosing_seeds=['AspisR1.S2W_D189Consolidation.accepted_run','AspisR1.S2W_D189Consolidation.wrapper_frames','AspisR1.S2W_NativeConsolidation.cuts_of_acceptance','AspisR1.S2W_ScheduledConsolidation.accepted_run'], required_closure='complete types, theorem and opaque values, inductive/constructor/mutual groups, recursor groups/rule RHS and generated auxiliaries; unresolved EMPTY; complete ConstantInfo; exact names; no rewriting', trust='untrusted raw transport only, imports/entries empty, never imported as trusted modules; kernel reconstruction required', status='requested data not available in released Port18 coverage; no current emitted declarations inspected')
outputs = {'Port27SDK_audit.json': json.dumps(summary,indent=2)+'\n', 'Port27SDK_export-request.json': json.dumps(request,indent=2)+'\n'}
for target, signature in signatures.items(): outputs['Port27SDK_' + target + '_statement.txt'] = signature
if '--write' in sys.argv:
    for name, content in outputs.items():
        assert len(content.encode()) <= 5_000_000
        (E/name).write_text(content)
else:
    for name, content in outputs.items(): assert (E/name).read_text()==content, name
print(json.dumps(dict(status=summary['status'], selections=14, import_metadata=len(byname), pinned_inputs=len(inputs), source_assessment_records=len(source_assessment), new_lean_attempts=0)))
