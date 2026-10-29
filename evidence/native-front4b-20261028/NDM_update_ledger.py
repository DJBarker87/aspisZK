"""Private NDM overlay; call unchanged NDK gates, never edit the lead ledger."""
from pathlib import Path
import collections
import hashlib
import importlib.util
import json
import subprocess
import sys

E = Path(__file__).resolve().parent
ROOT = E.parent.parent
NDK = E.parent / 'native-ledger2-20261028'
sys.path.insert(0, str(NDK))
import NDK_validate as validator
import NDK_review as review

sha = lambda b: hashlib.sha256(b).hexdigest()
dump = lambda x: json.dumps(x, indent=2, sort_keys=True) + '\n'
baseline = json.loads((NDK / 'NDK_LEDGER.json').read_text())
d = json.loads(json.dumps(baseline))
function = 'programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_zero'
cid = 'NDM::refresh::bounded_zero_iteration'
claim_evidence = []


def cite(path):
    p = ROOT / path
    data = p.read_bytes()
    d['evidence_manifest'][path] = dict(sha256=sha(data), bytes=len(data),
                                       revision='NDM private continuation, not merged adoption')
    if path not in claim_evidence:
        claim_evidence.append(path)
    return path


def local(name):
    return cite(str((E / name).relative_to(ROOT)))


receipts = []
features = []
for number in range(39, 45):
    a = f'NDM_K{number:03d}'
    receipt = json.loads((E / a / 'receipt.json').read_text())
    log = (E / a / 'stdout.log').read_text()
    review.check_native(receipt, log, number % 2 == 1)
    graph = json.loads((E / (a + '-graph-check.json')).read_text())
    features.append(dict(attempt=a, **review.check_features(graph, 'program')))
    lock = json.loads((E / (a + '-lock-check.json')).read_text())
    assert lock['unchanged'] and lock['before'] == review.LOCK == lock['after']
    receipts.append(local(a + '/receipt.json'))
    for suffix in ['/stdout.log', '/NDM_harness.patch', '-graph-check.json', '-lock-check.json']:
        local(a + suffix)

theorems = []
for attempt, module, theorem in [
    ('NDM_L006', 'NDM_ZeroSuffix', 'NDM_ZeroSuffix.resume_suffix'),
    ('NDM_L012', 'NDM_ZeroCut', 'NDM_ZeroCut.suffix_step'),
    ('NDM_L016', 'NDM_ZeroCaller', 'NDM_ZeroCaller.checkpoint_domain'),
]:
    snapshot = E / attempt / 'sources' / 'NDM_generated' / (module + '.lean')
    current = E / (module + '.lean')
    receipt = json.loads((E / attempt / 'receipt.json').read_text())
    review.check_theorem(receipt, theorem, snapshot.read_bytes(), current.read_bytes())
    rp = local(attempt + '/receipt.json')
    receipts.append(rp)
    sp = local(module + '.lean')
    theorems.append(dict(name=theorem, source=sp,
                         source_sha256=sha(current.read_bytes()), receipt=rp))
    local(attempt + '/stdout.log')

for p in ['NDM_E001/NDM_reference.rs.txt', 'NDM_E001/NDM_EXTRACTION_PINS.json',
          'NDM_Reference/Funs.lean', 'NDM_Reference/Types.lean',
          'NDM_E001/receipt.json', 'NDM_L002/receipt.json',
          'NDM_ZERO_BRIDGE.md', 'NDM_ZERO_ERASURE.json']:
    local(p)
for p in ['evidence/native-front4-20261028/NDG_ZeroRun.lean',
          'evidence/native-front4-20261028/NDG_L016/receipt.json']:
    cite(p)

domain = ('Related valid borrowed byte slices of length <=1768; native one-step '
          'carrier exercised as every arbitrary subslice of a 1768-byte backing. '
          'Same byte image, descriptor, live provenance and ordinary Rust slice '
          'interpretation retained. Native Vec/SDK snapshot carrier transport is '
          'not discharged. Model checkpoint read establishes exactly1768 bytes.')
physical = ('P6/D188 approved semantic transport of the checked native cut and '
            'the coherent Slice byte image; standard Rust slice/index semantics, '
            'tool/compiler and source-to-ELF interpretation retained. No SDK '
            'allocator or whole-entry physical instance is inferred.')
hypotheses = [dict(name='NDM.ZeroDomain', statement=domain, discharged_by=None),
              dict(name='NDM.ZeroPhysicalInterpretation', statement=physical, discharged_by=None)]
claim = dict(claim_id=cid, function=function, reported_status='CLOSED-CONDITIONAL',
             admissible_local_credit=True, medium='P6 hybrid native iteration / imported Lean induction',
             profile='deployed program pool-adapter,private-leaf-salts',
             feature_parity='explicit deployed program graph; frozen lock before/after every run',
             named_hypotheses=hypotheses, evidence=sorted(claim_evidence),
             receipts=sorted(receipts), active_support_receipts=sorted(receipts),
             historical_quarantined_receipts=[], replaced_quarantined_support=[],
             quarantined_support=[], arithmetic_stubs=[],
             rule14_dependency_audit=True, theorem_associations=theorems,
             native_feature_checks=features,
             composition_trust='Owner amendment fifth: P6/D188 semantic-transport reclassification, never removal',
             source_claim_text=[domain, physical,
               'CLOSED local bounded loop bridge only. Same-source ghost erasure, '
               'three native terminal/reject/continue pairs, E001 tag extraction, '
               'NDG induction, NDM suffix and model caller association. '
               'Actual runtime/Vec snapshot interpretation and composed caller remain OPEN.'],
             limitations=['Native backing class and physical interpretation retained',
                          'No SDK snapshot or whole-entry caller instance',
                          'No full frozen release replay or ELF reproduction'])
d['claims'].append(claim)
d['refresh']['decisions'].append(dict(function=function, prefix='NDM', decision='ADMIT LOCAL CONDITIONAL in private overlay only', domain=domain, remaining='Native Vec/SDK carrier and composed caller remain OPEN'))
for row in d['rows']:
    if row['function'] != function:
        continue
    assert row['bridge_status'] == 'OPEN'
    row['claim_ids'].append(cid)
    row['selected_claims'] = [cid]
    row['bridge_status'] = 'CLOSED-CONDITIONAL'
    row['named_hypotheses'] = hypotheses
    row['feature_parity'].append(dict(claim=cid, status=claim['feature_parity']))
    row['feature_parity_summary'] = claim['feature_parity']
    row['medium'].append(claim['medium'])
    row['no_credit_reason'] = None
    row['evidence'] = sorted(set(row['evidence']) | set(claim_evidence))
    row['receipts'] = sorted(set(row['receipts']) | set(receipts))
    row['receipt_sha256'] = {p: d['evidence_manifest'][p]['sha256'] for p in row['receipts']}
    row['reviewed_packet_updates'].append(dict(prefix='NDM', disposition=claim['source_claim_text'],
                                               evidence=sorted(claim_evidence)))

graph = {r['function']: set(r['canonical_callees']) for r in d['rows']}
statuses = {r['function']: r['bridge_status'] for r in d['rows']}
down = {}
for n in graph:
    seen = set()
    todo = list(graph[n])
    while todo:
        k = todo.pop()
        if k not in seen:
            seen.add(k)
            todo.extend(graph[k])
    down[n] = seen - {n}
opens = {n for n, status in statuses.items() if status in ['OPEN', 'quarantined']}
up = {n: {k for k in graph if n in down[k]} for n in graph}
frontier = []
visited = set()
for n in sorted(opens):
    group = tuple(sorted({n} | {m for m in down[n] if n in down[m]}))
    if group in visited or ((down[n] & opens) - set(group)):
        continue
    visited.add(group)
    candidates = sorted(set(group) & opens)
    selected = sorted(candidates, key=lambda k: (-len(up[k]), k))[0]
    frontier.append(dict(representative=selected, open_scc_members=candidates,
                         all_scc_members=list(group), dependent_functions=len(up[selected]),
                         dependent_rows=sum(r['function'] in up[selected] for r in d['rows'])))
d['critical_path']['frontier'] = sorted(frontier, key=lambda r: (-r['dependent_rows'], r['representative']))
d['critical_path']['highest_impact_open'] = [
    dict(function=n, dependent_functions=len(up[n]),
         dependent_rows=sum(r['function'] in up[n] for r in d['rows']))
    for n in sorted(opens, key=lambda n: (-sum(r['function'] in up[n] for r in d['rows']), n))[:20]]
for row in d['rows']:
    row['open_transitive_dependencies'] = sorted(down[row['function']] & opens)
    for obligation in row['caller_domain_obligations']:
        if obligation.get('callee') == function:
            obligation['callee_local_status'] = 'CLOSED-CONDITIONAL'
            obligation['callee_claims'] = [cid]
            obligation['required_named_hypotheses'] = [h['name'] for h in hypotheses]
            assert obligation['status'] == 'OPEN' and obligation['discharged_by'] is None
for tx in ['TX1', 'TX2', 'all_rows']:
    rows = [r for r in d['rows'] if tx == 'all_rows' or r['transaction'] == tx]
    d['coverage'][tx]['local_bridge_status'] = dict(collections.Counter(r['bridge_status'] for r in rows))
d['coverage']['unique_functions']['local_bridge_status'] = dict(collections.Counter(statuses.values()))
old_rows = {r['row']: r for r in baseline['rows']}
delta = dict(baseline_ledger_sha256=sha((NDK / 'NDK_LEDGER.json').read_bytes()),
             frozen_revision=d['frozen_revision'], headline=d['headline'], adopted_upstream=False,
             local_changes=[dict(row=r['row'], function=r['function'],
                                 before=old_rows[r['row']]['bridge_status'], after=r['bridge_status'],
                                 domain=domain, physical_interpretation=physical,
                                 claim=cid) for r in d['rows']
                            if r['bridge_status'] != old_rows[r['row']]['bridge_status']],
             composed_closures=[], trust_change='reclassification, not removal',
             before_coverage=baseline['coverage'], after_coverage=d['coverage'])
d['refresh']['changed_rows'] += [dict(row=c['row'], function=c['function'], before=c['before'], after=c['after'], admitted_claims=[cid]) for c in delta['local_changes']]
d['ndm_continuation'] = dict(baseline_ledger_sha256=delta['baseline_ledger_sha256'],
                              adopted_upstream=False, authority='private continuation proposal only')
attempts = [json.loads(line) for line in (E / 'NDM_ATTEMPTS.jsonl').read_text().splitlines()]
d['budget'] = dict(kani_limit=80, lean_limit=80, extraction_limit=20,
                   kani_used=sum(a['kind'] == 'kani' for a in attempts),
                   lean_used=sum(a['kind'] == 'lean' for a in attempts),
                   extraction_used=sum(a['kind'] == 'extract' for a in attempts))
# Do not replace the reviewed upstream history with a fictitious new merged packet.
validator.validate_invariants(d)
(E / 'NDM_LEDGER.json').write_text(dump(d))
(E / 'NDM_LEDGER_DELTA.json').write_text(dump(delta))
(E / 'NDM_LEDGER_VALIDATION.json').write_text(dump(dict(
    exit_status=0, validator=str((NDK / 'NDK_validate.py').relative_to(ROOT)),
    validator_sha256=sha((NDK / 'NDK_validate.py').read_bytes()),
    entrypoint='unchanged validate_invariants, including NDK_review.validate_refresh',
    full_corpus_recomputation='not adopted; frozen merged corpus needs an explicit lead refresh',
    changed_rows=len(delta['local_changes']), composed_closures=0,
    ledger_sha256=sha((E / 'NDM_LEDGER.json').read_bytes()), coverage=d['coverage'],
    frontier=len(frontier), budget=d['budget'])))
print(dump(dict(validation='passed unchanged NDK invariant gates',
                changed_rows=delta['local_changes'], budget=d['budget'])))
