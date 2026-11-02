#!/usr/bin/env python3
"""Authoritative additive evidence ledger; stdlib, read-only prover receipts.

Run with --write to regenerate, otherwise compare all derived output bytes.
Inherited validators execute unchanged. NDT's historical all-OPEN invariant is
checked on its baseline, never removed to accommodate later certificates.
"""
import argparse
import collections
import copy
import hashlib
import json
import lzma
from pathlib import Path
import re
import resource
import subprocess
import sys
import os
import threading
import time

sys.dont_write_bytecode = True
# Applies to this process and inherited Python review subprocesses.
CAP = 7 * 1024**3
# Darwin rejects RLIMIT_AS/DATA below its existing VM map. Monitor aggregate
# parent/child RSS instead; Linux additionally receives an address-space cap.
if sys.platform != 'darwin':
    resource.setrlimit(resource.RLIMIT_AS, (CAP, CAP))
PEAK_AGGREGATE_RSS = 0

def memory_watch():
    global PEAK_AGGREGATE_RSS
    while True:
        try:
            sample = subprocess.check_output(['ps', '-axo', 'pid=,ppid=,rss='], text=True)
            table = [tuple(map(int, line.split())) for line in sample.splitlines()]
            descendants = {os.getpid()}
            for _ in range(len(table)):
                added = {pid for pid, ppid, rss in table if ppid in descendants} - descendants
                if not added:
                    break
                descendants |= added
            total = sum(rss * 1024 for pid, ppid, rss in table if pid in descendants)
            PEAK_AGGREGATE_RSS = max(PEAK_AGGREGATE_RSS, total)
            if total >= CAP:
                for pid in descendants - {os.getpid()}:
                    try:
                        os.kill(pid, 9)
                    except ProcessLookupError:
                        pass
                os._exit(137)
        except Exception:
            os._exit(138)  # no unmonitored continuation
        time.sleep(0.5)

threading.Thread(target=memory_watch, daemon=True).start()
E = Path(__file__).resolve().parent
R = E.parent.parent
for directory in ['native-ledger3-20261029', 'native-ledger2-20261028',
                  'native-compledger-20261028', 'slice-q-compose-20261029',
                  'slice-s-compose4-20261101']:
    sys.path.insert(0, str(R / 'evidence' / directory))
import NDT_validate as ndt
import NCZ_validate as ncz
import NEB_validate as q
import NEL_validate as s


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def read(path):
    return json.loads(Path(path).read_bytes())


def encode(value):
    # Compact JSON keeps the full inherited ledger below the 20 MB limit.
    return json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=False) + '\n'


def require(test, reason):
    if not test:
        raise ValueError(reason)


class Inputs:
    """Git-backed immutable inputs; validate materialized bytes and deletions."""
    def __init__(self):
        self.pins = read(E / 'NEN_INPUTS.json')
        self.revision = self.pins['revision']
        self.used = {}
        self.deleted = set(ndt.git('ls-files', '--deleted').decode().splitlines())
        self.proc = subprocess.Popen(['git', 'cat-file', '--batch'], cwd=R,
                                     stdin=subprocess.PIPE, stdout=subprocess.PIPE)

    def raw(self, path, digest=None, revision=None):
        require(path not in self.deleted, 'deleted input: ' + path)
        self.proc.stdin.write(((revision or self.revision) + ':' + path + '\n').encode())
        self.proc.stdin.flush()
        header = self.proc.stdout.readline().split()
        require(len(header) == 3 and header[1] == b'blob', 'missing input: ' + path)
        data = self.proc.stdout.read(int(header[2]))
        require(self.proc.stdout.read(1) == b'\n', 'Git protocol')
        if revision is None and (R / path).exists():
            require(sha((R / path).read_bytes()) == sha(data), 'dirty input: ' + path)
        if digest:
            require(sha(data) == digest, 'input hash: ' + path)
        self.used[((revision + ':') if revision else '') + path] = {'sha256': sha(data), 'git_blob': header[0].decode(), 'bytes': len(data)}
        return data

    def obj(self, path):
        return json.loads(self.raw(path))

    def check_corpus(self):
        # New evidence requires an explicit input snapshot refresh. Own receipts
        # are outputs and excluded; unrelated later commits cannot add credit.
        prefixes = read(E / 'NEN_SCOPE.json')['input_directories']
        actual = {}
        for line in ndt.git('ls-tree', '-rl', 'HEAD', '--', *prefixes,
                             ndt.DESIGN).decode().splitlines():
            meta, path = line.split('\t', 1)
            _, kind, oid, size = meta.split()
            if kind == 'blob':
                actual[path] = {'git_blob': oid, 'bytes': int(size)}
        require(actual == self.pins['files'], 'merged input corpus changed; explicitly refresh snapshot')
        reports = {}
        for line in ndt.git('ls-tree', '-rl', 'HEAD').decode().splitlines():
            meta, path = line.split('\t', 1)
            _, kind, oid, size = meta.split()
            if kind == 'blob' and path.endswith('.md') and not path.startswith('evidence/ledger4-20261102/') and ('/evidence/' in '/' + path and path.split('evidence/', 1)[1].count('/') == 1):
                reports[path] = {'git_blob': oid, 'bytes': int(size)}
        require(reports == self.pins['report_files'], 'merged report corpus changed; explicit refresh required')
        # Check all materialized lane inputs, including imported validators/code.
        for path, pin in dict(actual, **reports).items():
            require(path not in self.deleted, 'deleted input: ' + path)
            p = R / path
            if p.is_file():
                raw = p.read_bytes()
                oid = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
                require(oid == pin['git_blob'], 'changed materialized input: ' + path)

    def close(self):
        self.proc.stdin.close()
        self.proc.wait()
        self.proc.stdout.close()


def baseline_audit(inputs):
    base = inputs.obj('evidence/native-ledger3-20261029/NDT_LEDGER.json')
    ndt.validate_invariants(base)
    ncz.validate_invariants(base)
    # NDT release replay is reused by reading its original receipt, not rerun.
    receipt = inputs.obj('evidence/native-ledger3-20261029/NDT_FINAL_RECEIPT.json')
    require(receipt['exit_status'] == 0, 'NDT baseline receipt did not pass')
    # Revalidate every inherited content address, even outside sparse checkout.
    report_drift = []
    require(receipt['ledger_sha256'] == sha((R / 'evidence/native-ledger3-20261029/NDT_LEDGER.json').read_bytes()), 'NDT receipt ledger pin')
    for path, digest in receipt['source_hashes'].items():
        inputs.raw(path, digest)
    for path, ref in base['evidence_manifest'].items():
        current = inputs.raw(path)
        if sha(current) != ref['sha256']:
            # Reports evolve after a snapshot. Keep BOTH versions explicit;
            # never relabel an old statement as the current report.
            require(path.endswith('.md') and path in inputs.pins['files'], 'changed inherited non-report input: ' + path)
            historical = inputs.raw(path, ref['sha256'], ref['revision'])
            report_drift.append(dict(path=path, historical_sha256=sha(historical), current_sha256=sha(current), disposition='Historical baseline only; later reports pinned separately, no automatic proof adoption'))
    inputs.baseline_report_drift = report_drift
    # Actual frozen whole bodies and inventory identity, independent of labels.
    bodies = {}
    for row in base['rows']:
        path = row['function'].split('::')[0]
        if path not in bodies:
            bodies[path] = ndt.git('show', base['frozen_revision'] + ':' + path)
        start, end = row['frozen_body_byte_range']
        require(sha(bodies[path][start:end]) == row['frozen_body_sha256'],
                'frozen body mismatch: ' + row['row'])
    return base


def strings(value):
    if isinstance(value, str):
        yield value
    elif isinstance(value, dict):
        for item in value.values():
            yield from strings(item)
    elif isinstance(value, list):
        for item in value:
            yield from strings(item)


def refs(value):
    return sorted({x for x in strings(value) if x.startswith('evidence/') and x.endswith('/receipt.json')})


def outcome(row):
    if row['outcome'] == 'RESTORED':
        return 'RESTORED'
    if row['outcome'].startswith('UNAFFECTED'):
        return 'UNAFFECTED'
    return 'SUSPENDED' if 'SUSPENDED' in row.get('reason', '') else 'OPEN'


def aggregate(statuses):
    values = set(statuses)
    if 'SUSPENDED' in values:
        return 'SUSPENDED'
    if not values or 'OPEN' in values:
        return 'OPEN'
    return 'RESTORED' if 'RESTORED' in values else 'UNAFFECTED'


def k3_inventory(inputs, packets):
    credits = {}
    for lane in ['k3-audit-20261030/NEH', 'k3-review2-20261101/NEK']:
        review = inputs.obj('evidence/' + lane + '_LEDGER_DELTA.json')
        for item in review['receipts']:
            p = item['receipt']
            previous = credits.get(p)
            credits[p] = dict(receipt=p, harness=item['harness'], k3_status=outcome(item),
                              reason=item['reason'], review='evidence/' + lane + '_LEDGER_DELTA.json',
                              pair=item.get('pair'), k2_quarantined=False)
            if previous:
                credits[p]['previous_k3_status'] = previous['k3_status']
    latest = inputs.obj('evidence/k3-review2-20261101/NEK_LEDGER_DELTA.json')
    for alias in latest['byte_identical_aliases']:
        p, canonical = alias['receipt'], alias['canonical']
        inputs.raw(p, alias['receipt_sha256'])
        inputs.raw(canonical, alias['receipt_sha256'])
        if canonical in credits:
            credits[p] = dict(credits[canonical], receipt=p, canonical_receipt=canonical)
    # Reconcile every exact-byte alias, including the NEA originals whose
    # canonical active receipts live in NEB's imported packet.
    for item in latest['receipts']:
        if not item.get('alias_of'):
            continue
        canonical = item['alias_of']
        digest = sha(inputs.raw(canonical))
        inputs.raw(item['receipt'], digest)
        require(canonical in credits, 'unreviewed alias target')
        credits[item['receipt']] = dict(credits[canonical], receipt=item['receipt'], canonical_receipt=canonical)
    # Replacement results are reviewed same-property/name pairs or explicit
    # complete conjunct assemblies. A lone PASS never restores a property.
    checked_pairs = set()
    assemblies = {c['positive_receipt']: c for c in latest['common_certificates']}
    for credit in list(credits.values()):
        if credit['k3_status'] != 'RESTORED':
            continue
        pair = credit['pair']
        require(pair, 'restoration lacks pair: ' + credit['receipt'])
        if 'windows' in pair:
            require(pair['windows'] and len(pair['windows']) == len(pair['controls']), 'incomplete window assembly')
            # These are the review's complete, same-property conjuncts; their
            # frame/copy/shape obligations are retained, not inferred from PASS.
            matches = [c for c in latest['common_certificates'] if credit.get('canonical_receipt', credit['receipt']) in {c['positive_receipt'], c.get('historical_control')}]
            require(matches and all(c['closed'] and all(x['closed'] for x in c['conjuncts']) for c in matches), 'unclosed conjunct assembly')
            pairs = []
            for positive, control in zip(pair['windows'], pair['controls']):
                if control == 'NEK_K052':
                    require(any(x['control_replaced_by_nibbles'] for c in matches for x in c['conjuncts'] if x['control'] == control), 'unapproved timeout replacement')
                    pairs += [('NEK_K235', 'NEK_K236'), ('NEK_K237', 'NEK_K238'), ('NEK_K335', 'NEK_K328'), ('NEK_K329', 'NEK_K330'), ('NEK_K331', 'NEK_K332'), ('NEK_K333', 'NEK_K334')]
                    # K051 remains the original positive; K052 earns no credit.
                    require(inputs.obj('evidence/k3-review2-20261101/' + positive + '/receipt.json')['exit_status'] == 0, 'missing original window')
                else:
                    pairs.append((positive, control))
            # Preserve every per-conjunct copy gate and Box shape gate.
            for c in matches:
                for x in c['conjuncts']:
                    clause = int(x['positive'].split('_K')[1])
                    # Batch starts K039 and emits one positive/control per
                    # conjunct; copy suite starts K130 in the same order.
                    index = (clause - 39) // 2
                    pairs.append((f'NEK_K{130 + 2*index:03}', f'NEK_K{131 + 2*index:03}'))
            pairs += [('NEK_K190', 'NEK_K191'), ('NEK_K192', 'NEK_K194'), ('NEK_K219', 'NEK_K220')]
            for a in ['NEK_L001', 'NEK_L003', 'NEK_L004', 'NEK_L006']:
                rc = inputs.obj('evidence/k3-review2-20261101/' + a + '/receipt.json')
                require(rc['exit_status'] == 0 and rc['print_axioms'], 'missing formal assembly')
                for audit in rc['print_axioms']:
                    names = re.search(r'\[([^]]*)\]', audit)
                    require((names and {x.strip() for x in names[1].split(',')} <= {'propext', 'Classical.choice', 'Quot.sound'}) or 'does not depend on any axioms' in audit, 'unapproved assembly axioms')
        else:
            pairs = [(pair['positive'], pair['control'])]
        for positive, control in pairs:
            if (positive, control) in checked_pairs:
                continue
            checked_pairs.add((positive, control))
            modules = []
            for attempt, expected in [(positive, 0), (control, 1)]:
                directory = 'k3-review2-20261101' if attempt.startswith('NEK_') else 'k3-audit-20261030'
                path = 'evidence/' + directory + '/' + attempt + '/receipt.json'
                receipt = inputs.obj(path)
                require(receipt['exit_status'] == expected and int(receipt['swaps']) == 0,
                        'invalid restoration pair: ' + path)
                modules.append(receipt.get('module'))
                log = inputs.raw(str(Path(path).parent / 'stdout.log')).decode()
                require(('VERIFICATION:- SUCCESSFUL' if expected == 0 else 'VERIFICATION:- FAILED') in log,
                        'missing restoration verdict: ' + path)
                require('timed out' not in log.lower(), 'timed-out restoration: ' + path)
            if 'windows' not in pair and modules[0] != modules[1]:
                # Some original copy suites already had separate correct/wrong
                # harnesses. Require BOTH unchanged original names, never a
                # suffix-stripping or renamed harness exemption.
                originals = {c['harness'] for c in credits.values() if c.get('pair') == pair}
                require(set(modules) <= originals, 'renamed matched restoration control')
    # Later S native certificates are checked by the unmodified NEE/NEJ/NEL
    # gates as well. Rule-16 evidence is additional, never a substitute.
    for packet in packets:
        for path in refs(packet):
            if path in credits:
                continue
            receipt = inputs.obj(path)
            if receipt.get('kind') != 'kani':
                continue
            parent = Path(path).parent
            directory = parent.parent
            attempt = parent.name
            rule_path = str(directory / (attempt + '-rule16-check.json'))
            if rule_path in inputs.pins['files']:
                check = inputs.obj(rule_path)
                safe = check.get('no_writable_static') is True
            else:
                # Exact receipt-pinned oracle/contracts, not a string search of
                # arbitrary source with the same function name.
                patches = [name for name in receipt['source_hashes'] if name.endswith('.patch')]
                safe = bool(patches)
                for name in patches:
                    candidates = [str(directory / (attempt + '-' + name)), str(directory / name), str(parent / 'sources' / name)]
                    if name.endswith('KMX_copy_stubs.patch'):
                        candidates.append('evidence/kani-mitig-20261028/KMX_copy_stubs.patch')
                    available = [p for p in candidates if p in inputs.pins['files'] or (R / p).is_file()]
                    require(available, 'missing receipt-pinned patch: ' + name)
                    code = inputs.raw(available[0], receipt['source_hashes'][name]).decode()
                    safe &= not bool(re.search(r'\bstatic\s+mut\b|\bstatic\s+\w+\s*:[^;=]*(?:Atomic|UnsafeCell|RefCell|Cell\s*<)', code))
            credits[path] = dict(receipt=path, harness=receipt.get('module'),
                                 k3_status='UNAFFECTED' if safe else 'OPEN',
                                 reason='Receipt-pinned later S local-frame certificate; inherited native gates still mandatory' if safe else 'No complete rule-16 source check',
                                 review=rule_path if rule_path in inputs.pins['files'] else str(directory),
                                 k2_quarantined=False)
    return credits, latest


def support_gate(paths, credits):
    reasons = []
    for path in sorted(set(paths)):
        c = credits.get(path)
        if c is None:
            reasons.append('K-3 unreviewed support: ' + path)
        elif c.get('k2_quarantined'):
            reasons.append('K-2 quarantined support: ' + path)
        elif c['k3_status'] not in {'RESTORED', 'UNAFFECTED'}:
            reasons.append('K-3 ' + c['k3_status'] + ': ' + path)
    return reasons


def slice_results(base, packet_q, packet_s):
    out_q, delta = q.extend(base, packet_q)
    out_s = s.compose(base, packet_s, read(s.E / 'NEL_REVIEWED_CERTIFICATES.json'))
    return out_q, out_s, delta


def row_support(row, packet, reviewed_rows, credits):
    # NEK audited the exact selected Q closure (rather than flat historical
    # receipt lists). Later S subjects carry receipt-pinned native certificates.
    qkey = 'NEB:' + row['row']
    if qkey in reviewed_rows and row['function'] in Q_FUNCTIONS:
        record = reviewed_rows[qkey]
        require(record['function'] == row['function'] and record['k3_fully_cleared_including_transitive_support'],
                'wrong K-3 row identity')
        return sorted(record['support_receipts'])
    certificates = []
    f = row['function']
    for group in ['members', 'roots', 'hypotheses', 'edges', 'inventory_edges', 'externals']:
        for subject, cert in packet.get(group, {}).items():
            if subject == f or subject.startswith(f + '::') or subject.startswith(f + ' -> ') or any(o['id'] == subject for o in row['caller_domain_obligations']):
                certificates.append(cert)
    found = {p for p in refs(certificates) if p in credits}
    require(found, 'composed row has no reviewed native support: ' + row['row'])
    return sorted(found)


Q_FUNCTIONS = set()


def unify(base, out_q, out_s, packet_s, credits, latest):
    result = copy.deepcopy(base)
    rows = {r['row']: r for r in result['rows']}
    reviewed = {r['row']: r for r in latest['rows']}
    claims = {c['claim_id']: c for c in result['claims']}
    quarantine = {c['receipt'] for c in base['quarantine']}
    for path in quarantine:
        credits.setdefault(path, dict(receipt=path, k3_status='OPEN', reason='Historical K-2 quarantine', harness=None))['k2_quarantined'] = True
    for claim in result['claims']:
        support = claim.get('active_support_receipts', [])
        blocked = support_gate(support, credits)
        if claim['quarantined_support']:
            blocked.append('K-2 quarantined claim support')
        claim['k3_status'] = aggregate(credits.get(p, {}).get('k3_status', 'OPEN') for p in support)
        claim['historical_admissible_local_credit'] = claim['admissible_local_credit']
        claim['effective_local_credit'] = bool(claim['admissible_local_credit'] and support and not blocked)
        claim['admissible_local_credit'] = claim['effective_local_credit']
        claim['NEN_support_rejections'] = blocked
    candidates = {}
    for lane, source in [('Q', out_q), ('S', out_s)]:
        for r in source['rows']:
            if r['function'] not in SLICES[lane]['functions']:
                continue
            if r['row'] in candidates:
                prior_lane, prior = candidates[r['row']]
                require(prior['function'] == r['function'] and prior['frozen_body_sha256'] == r['frozen_body_sha256'], 'conflicting slice identity')
                if prior['composed_status'] == 'CLOSED' and r['composed_status'] == 'CLOSED':
                    require(prior['selected_claims'] == r['selected_claims'], 'conflicting CLOSED slice selections')
                elif r['composed_status'] == 'CLOSED':
                    candidates[r['row']] = (lane, r)
            else:
                candidates[r['row']] = (lane, r)
    for rid, (lane, candidate) in candidates.items():
        rows[rid].update(copy.deepcopy(candidate))
        rows[rid]['NEN_slice'] = lane
    for row in result['rows']:
        row['historical_bridge_status'] = row['bridge_status']
        row['NEN_rejections'] = []
        row['slice_reported_closed'] = row['composed_status'] == 'CLOSED'
        if row['slice_reported_closed']:
            support = row_support(row, packet_s, reviewed, credits)
        else:
            support = sorted({p for cid in row['selected_claims'] for p in claims.get(cid, {}).get('active_support_receipts', [])})
        row['active_support_receipts'] = support
        row['k3_status'] = aggregate(credits.get(p, {}).get('k3_status', 'OPEN') for p in support)
        reasons = support_gate(support, credits)
        if not support and row['selected_claims']:
            reasons.append('No reviewed active native support')
        if any(claims.get(cid, {}).get('quarantined_support') for cid in row['selected_claims']):
            reasons.append('K-2 quarantined selected claim')
        row['NEN_rejections'] += reasons
        if reasons:
            row['composed_status'] = 'OPEN'
            row['bridge_status'] = 'quarantined' if any('K-2' in r for r in reasons) else 'OPEN'
        if row['composed_status'] != 'CLOSED' and not row['NEN_rejections']:
            row['NEN_rejections'].append('Missing complete row/call-domain/hypothesis composition certificate')
    # Propagate denied *active* dependencies, retaining explicitly certified
    # alternatives. No cycle can bootstrap a CLOSED row here.
    changed = True
    while changed:
        changed = False
        byfunction = collections.defaultdict(list)
        for row in result['rows']:
            byfunction[row['function']].append(row)
        for row in result['rows']:
            if row['composed_status'] != 'CLOSED':
                continue
            for ob in row['caller_domain_obligations']:
                callee = ob.get('callee')
                if not callee:
                    continue
                key = row['function'] + ' -> ' + callee
                if row['NEN_slice'] == 'Q':
                    edge = Q_EDGES.get(ob['id'], {})
                    excluded = edge.get('certificate', {}).get('kind') == 'STATIC_UNREACHABLE'
                else:
                    cert = packet_s.get('edges', {}).get(key) or packet_s.get('inventory_edges', {}).get(key)
                    excluded = bool(cert and cert['kind'] == 'alternative-resolution')
                if not excluded and any(r['composed_status'] != 'CLOSED' for r in byfunction[callee]):
                    row['composed_status'] = 'OPEN'
                    row['NEN_rejections'].append('Dependent row OPEN: ' + callee)
                    changed = True
                    break
    for row in result['rows']:
        if row['composed_status'] == 'CLOSED':
            require(row['selected_claims'] and row['bridge_status'] == 'CLOSED-CONDITIONAL', 'closed without bridge')
            require(not row['open_transitive_dependencies'], 'open transitive dependency')
            require(all(h['discharged_by'] for h in row['named_hypotheses']), 'open hypothesis')
            require(all(o['status'] == 'CLOSED' and o['discharged_by'] for o in row['caller_domain_obligations']), 'open edge')
            require(not support_gate(row['active_support_receipts'], credits), 'blocked native credit')
    result['coverage'] = coverage(result['rows'])
    result['NEN_credits'] = sorted(credits.values(), key=lambda x: x['receipt'])
    result['NEN_rejected_slice_closures'] = [dict(row=r['row'], slice=r['NEN_slice'], function=r['function'], reasons=r['NEN_rejections']) for r in result['rows'] if r['slice_reported_closed'] and r['composed_status'] != 'CLOSED']
    result['NEN_composed_per_slice'] = {lane: sum(r['composed_status'] == 'CLOSED' and r.get('NEN_slice') == lane for r in result['rows']) for lane in SLICES}
    result['NEN_composed_slice_membership'] = {lane: sum(r['composed_status'] == 'CLOSED' and r['function'] in spec['functions'] for r in result['rows']) for lane, spec in SLICES.items()}
    result['status_semantics']['composed_status'] = 'All original slice gates plus per-credit K-3/K-2 and active dependency gates. P6/D188 transport trust retained.'
    result['critical_path']['status'] = 'Historical NDT advisory frontier only; not recomputed for NEN'
    return result


def coverage(rows):
    def counts(rs):
        return dict(rows=len(rs), local_bridge_status=dict(collections.Counter(r['bridge_status'] for r in rs)), composed_status=dict(collections.Counter(r['composed_status'] for r in rs)), k3_status=dict(collections.Counter(r['k3_status'] for r in rs)))
    result = {tx: counts([r for r in rows if r['row'].startswith(tx + ':')]) for tx in ['TX1', 'TX2']}
    result['all_rows'] = counts(rows)
    grouped = collections.defaultdict(list)
    for row in rows:
        grouped[row['function']].append(row)
    result['unique_functions'] = dict(count=len(grouped), composed_status=dict(collections.Counter('CLOSED' if all(r['composed_status'] == 'CLOSED' for r in rs) else 'OPEN' for rs in grouped.values())), local_bridge_status=dict(collections.Counter(aggregate_bridge(rs) for rs in grouped.values())))
    return result


def aggregate_bridge(rows):
    statuses = {r['bridge_status'] for r in rows}
    return next(iter(statuses)) if len(statuses) == 1 else 'MIXED'



def packet_audit(inputs, result, credits):
    """Reconcile every requested packet, including intentionally unadopted work."""
    dispositions = []
    for directory, prefix in [('slice-q-leaves-20261029', 'NEA'), ('slice-s-leaves-20261029', 'NEC')]:
        path = 'evidence/' + directory + '/' + prefix + '_CLOSED.json'
        proposals = inputs.obj(path)
        for proposal in proposals:
            support = [p if p.startswith('evidence/') else 'evidence/' + directory + '/' + p
                       for p in proposal['kani_receipt_paths'] + proposal['control_receipts']]
            matches = [r for r in result['rows'] if proposal['claim_id'] in r['selected_claims'] and r['composed_status'] == 'CLOSED']
            # The exact selected certificates govern geometry adoption; the
            # proposer packet's flat receipt list remains preserved history.
            active = sorted({p for r in matches for p in r['active_support_receipts']}) if matches else support
            status = aggregate(credits.get(p, {}).get('k3_status', 'OPEN') for p in active)
            rejected = support_gate(active, credits)
            reason = 'Admitted through unchanged NEB geometry/row certificates' if matches else 'Local proposal retained; no unified same-call/root composition certificate selects this packet'
            credit = dict(claim_id=proposal['claim_id'], function=proposal['function'], packet=proposal,
                          evidence=[path], active_support_receipts=active, k3_status=status,
                          admissible_local_credit=bool(matches and not rejected),
                          effective_local_credit=bool(matches and not rejected),
                          NEN_support_rejections=rejected, NEN_disposition=reason)
            # Complete statements/domain/physical qualifications remain visible.
            if not any(c['claim_id'] == credit['claim_id'] for c in result['claims']):
                result['claims'].append(credit)
            dispositions.append(dict(packet=path, claim=proposal['claim_id'], function=proposal['function'],
                                     k3_status=status, composed_rows=[r['row'] for r in matches],
                                     disposition=reason, rejection_reasons=rejected))
    # NEG's local-record repair is real support progress, but its CLOSED file
    # intentionally contains no end-to-end member. Never promote fixtures or
    # isolated native arithmetic to the missing loop/refinement law.
    directory = 'evidence/slice-q-mul-20261029/'
    audit = inputs.obj(directory + 'NEG_FINAL_AUDIT.json')
    require(inputs.obj(directory + 'NEG_CLOSED.json') == [] and audit['new_composed_closed'] == 0,
            'NEG new closure requires explicit certificate integration')
    for positive, control in audit['rule16_pairs'].items():
        modules = []
        for attempt, expected in [(positive, 0), (control, 1)]:
            path = directory + attempt + '/receipt.json'
            rc = inputs.obj(path)
            log = inputs.raw(directory + attempt + '/stdout.log').decode()
            require(rc['exit_status'] == expected and int(rc['swaps']) == 0, 'invalid NEG local-record pair')
            require(('VERIFICATION:- SUCCESSFUL' if expected == 0 else 'VERIFICATION:- FAILED') in log and 'timed out' not in log.lower(), 'NEG incomplete pair')
            patch = inputs.raw(directory + attempt + '/NEG_harness.patch').decode()
            added = '\n'.join(l[1:] for l in patch.splitlines() if l.startswith('+') and not l.startswith('+++'))
            require(not re.search(r'\bstatic\s+mut\b|\bstatic\s+\w+\s*:[^;=]*(?:Atomic|UnsafeCell|RefCell|Cell\s*<)', added), 'NEG writable static')
            require(inputs.obj(directory + attempt + '-admission.json')['reservation']['allowed'] is True, 'NEG admission')
            require(inputs.obj(directory + attempt + '-admission.json')['exit'] == 0, 'NEG admission exit')
            require(inputs.obj(directory + attempt + '-lock-check.json')['unchanged'], 'NEG lock')
            require(not inputs.obj(directory + attempt + '-source-check.json')['errors'], 'NEG source')
            modules.append(rc['module'])
            credits[path] = dict(receipt=path, harness=rc['module'], k3_status='UNAFFECTED',
                                 k2_quarantined=False, reason='Matched local-record NEG native window only; no composed bridge',
                                 review=directory + 'NEG_FINAL_AUDIT.json')
        require(modules[0] == modules[1], 'NEG renamed paired target')
    for attempt in ['NEG_K003', 'NEG_K009']:
        path = directory + attempt + '/receipt.json'
        rc = inputs.obj(path)
        credits[path] = dict(receipt=path, harness=rc['module'], k3_status='SUSPENDED',
                             k2_quarantined=False, reason='Historical writable-static property; local-record replacement does not retroactively validate this receipt',
                             review=directory + 'NEG_FINAL_AUDIT.json')
    dispositions.append(dict(packet=directory + 'NEG_FINAL_AUDIT.json', composed_rows=[],
                             disposition='0 new CLOSED members; loop/native-emitted/callee-domain obligations remain; local-record windows and finite fixtures retained'))
    # Re-run the actual source certificate as a pure function. This is a status
    # check over frozen Git bytes; it launches neither Kani nor Lean.
    directory = 'evidence/slice-q-fnptr-20261029/'
    sys.path.insert(0, str(R / directory))
    import NEF_OBSERVER_CERTIFICATE as observer
    src = {p: observer.frozen(p) for p in [observer.P, observer.O, observer.A, observer.V, observer.C, observer.S, observer.F]}
    evidence = inputs.raw('evidence/native-featparity-20261028/NCS_I002-stdout.log')
    records = [json.loads(l) for l in evidence.decode().splitlines() if l.startswith('{')]
    nodes = next(x['nodes'] for x in records if x['label'] == 'program-deployed')
    checked = observer.validate(src, nodes)
    stored = inputs.obj(directory + 'NEF_OBSERVER_CERTIFICATE.json')
    require(all(stored[k] == value for k, value in checked.items()), 'NEF observer certificate drift')
    pins = inputs.obj(directory + 'NEF_SOURCE_PINS.json')
    require(all(sha(source.encode()) == pins['files'][p]['sha256'] for p, source in src.items()), 'NEF frozen source pin')
    dispositions.append(dict(packet=directory + 'NEF_OBSERVER_CERTIFICATE.json', composed_rows=[],
                             disposition='Source-specialisation certificate checked; scope is deployed None-observer roots, not arbitrary library APIs. K-2 quarantine unchanged; no full query/inverse bridge'))
    result['NEN_packet_dispositions'] = dispositions
    result['NEN_credits'] = sorted(credits.values(), key=lambda x: x['receipt'])


def build(inputs):
    inputs.check_corpus()
    base = baseline_audit(inputs)
    packet_q = inputs.obj('evidence/slice-q-compose-20261029/NEB_EDGES.json')
    packet_s = inputs.obj('evidence/slice-s-compose4-20261101/NEL_LEDGER_DELTA.json')
    global SLICES, Q_FUNCTIONS, Q_EDGES
    SLICES = inputs.obj(ndt.DESIGN + 'VERTICAL-SLICES-20261029.json')['slices']
    Q_FUNCTIONS = set(SLICES['Q']['functions'])
    Q_EDGES = {e['obligation_id']: e for e in packet_q['edges'] + packet_q['inventory_edges']}
    out_q, out_s, delta = slice_results(base, packet_q, packet_s)
    require(delta == read(q.E / 'NEB_LEDGER_DELTA.json'), 'Q validator result changed')
    # Record actual predecessor validator results, not stale packet headlines.
    predecessor_results = {'NEB': [r['row'] for r in out_q['rows'] if r['composed_status'] == 'CLOSED'],
                           'NEL': [r['row'] for r in out_s['rows'] if r['composed_status'] == 'CLOSED']}
    for prefix, module, directory in [('NEE', s.predecessor.predecessor, 'slice-s-compose2-20261029'), ('NEJ', s.predecessor, 'slice-s-compose3-20261101')]:
        packet = inputs.obj('evidence/' + directory + '/' + prefix + '_LEDGER_DELTA.json')
        review = inputs.obj('evidence/' + directory + '/' + prefix + '_REVIEWED_CERTIFICATES.json')
        checked = module.compose(base, packet, review)
        predecessor_results[prefix] = [r['row'] for r in checked['rows'] if r['composed_status'] == 'CLOSED']
    credits, latest = k3_inventory(inputs, [packet_s])
    result = unify(base, out_q, out_s, packet_s, credits, latest)
    result['NEN_slice_validator_results'] = predecessor_results
    for row in result['rows']:
        row['NEN_reported_closed_by'] = [label for label, ids in predecessor_results.items() if row['row'] in ids]
    # Reconcile every earlier validator's reported closure too. Latest source
    # certificates may supersede a historical packet but never hide rejection.
    rejected = {r['row']: r for r in result['NEN_rejected_slice_closures']}
    for row in result['rows']:
        if row['NEN_reported_closed_by'] and row['composed_status'] != 'CLOSED':
            rejected[row['row']] = dict(row=row['row'], slice=row.get('NEN_slice'), function=row['function'], reported_by=row['NEN_reported_closed_by'], reasons=row['NEN_rejections'])
    result['NEN_rejected_slice_closures'] = sorted(rejected.values(), key=lambda x: x['row'])
    packet_audit(inputs, result, credits)
    # Inventory every requested lane's candidate native receipt, including
    # failed/incomplete/orphan attempts; none gains support by mere presence.
    for path in inputs.pins['files']:
        if not re.fullmatch(r'evidence/slice-[^/]+/NE[ABCEFGJL]_K\d+/receipt.json', path) or path in credits:
            continue
        rc = inputs.obj(path)
        if rc.get('kind') != 'kani':
            continue
        credits[path] = dict(receipt=path, harness=rc.get('module'), k3_status='OPEN',
                             k2_quarantined=False, reason='Not admitted as active static-free native support; historical attempt retained',
                             review='NEN candidate inventory only; no support')
    result['NEN_credits'] = sorted(credits.values(), key=lambda x: x['receipt'])
    result['NEN_k3_credit_counts'] = dict(collections.Counter(c['k3_status'] for c in credits.values()))
    result['NEN_current_report_corpus'] = dict(count=len(inputs.pins['report_files']), pinned_in='NEN_INPUTS.json:report_files', policy='All current top-level reports pinned. Documentary mentions are discovery only; only explicit checked certificates add credit.')
    result['NEN_source_revision'] = inputs.revision
    result['NEN_historical_report_drift'] = inputs.baseline_report_drift
    result['NEN_baseline_validation'] = 'Unchanged NDT and NCZ invariants; all baseline manifest hashes and frozen bodies rechecked; full NDT replay reused from exit-0 receipt, not rerun.'
    result['NEN_budget'] = {'lean_runs': 0, 'kani_runs': 0, 'python_aggregate_rss_limit_bytes': CAP}
    result['NEN_evidence_manifest'] = {p: ref for p, ref in inputs.used.items() if p not in base['evidence_manifest'] or ref['sha256'] != base['evidence_manifest'][p]['sha256']}
    return result


def markdown(d):
    lines = ['# NEN authoritative ledger', '', 'Target not yet established. Frozen source `' + d['frozen_revision'] + '`.', '',
             'Every original NDT/NCZ invariant is checked on the pinned baseline. Q uses NEB unchanged; S uses the unchanged NDT→NED→NEE→NEJ→NEL chain. Call-domain, ruling (y)/(y-prime), exact review/hash, controls, feature parity and rule-16 gates are retained. K-3/K-2 add denial checks. Trust is reclassified under P6/D188 option A, never discharged.', '',
             '| Coverage | Rows | Composed CLOSED | Composed OPEN |', '|---|---:|---:|---:|']
    for key in ['TX1', 'TX2', 'all_rows']:
        c = d['coverage'][key]
        lines.append(f"| {key} | {c['rows']} | {c['composed_status'].get('CLOSED', 0)} | {c['composed_status'].get('OPEN', 0)} |")
    c = d['coverage']['unique_functions']
    lines += [f"| unique functions | {c['count']} | {c['composed_status'].get('CLOSED', 0)} | {c['composed_status'].get('OPEN', 0)} |", '',
              'Composed CLOSED by contributing slice: ' + ', '.join(f'{k}: {v}' for k, v in d['NEN_composed_per_slice'].items()) + '.', '',
              '## Slice-validator closure reconciliation', '',
              f"Slice-reported CLOSED rows rejected: {len(d['NEN_rejected_slice_closures'])}."]
    lines.append('Actual validator CLOSED counts: ' + ', '.join(f'{label}: {len(ids)}' for label, ids in d['NEN_slice_validator_results'].items()) + '.')
    for r in d['NEN_rejected_slice_closures']:
        lines.append(f"- {r['row']} ({r['slice']}): " + '; '.join(r['reasons']))
    lines += ['', 'Slice membership (overlapping): ' + ', '.join(f'{k}: {v}' for k, v in d['NEN_composed_slice_membership'].items()) + '. The Q to_limbs occurrences also belong to S; contributions above count each occurrence once.', '',
              'K-3 candidate receipt statuses: ' + ', '.join(f'{k}: {v}' for k, v in d['NEN_k3_credit_counts'].items()) + '.', '', '## Packet dispositions', '']
    for item in d['NEN_packet_dispositions']:
        lines.append('- `' + item.get('claim', item['packet']) + '`: ' + item['disposition'] + ('; ' + '; '.join(item['rejection_reasons']) if item.get('rejection_reasons') else ''))
    lines += ['', '## Historical report changes', '']
    for item in d['NEN_historical_report_drift']:
        lines.append('- `' + item['path'] + '`: historical SHA256 `' + item['historical_sha256'] + '`, current `' + item['current_sha256'] + '`. ' + item['disposition'])
    lines += ['', '## Admissions and open rows', '', '| Row | Bridge | Composed | K-3 | Admission or rejection reason |', '|---|---|---|---|---|']
    for row in d['rows']:
        reason = 'All unchanged slice gates and reviewed active support accepted' if row['composed_status'] == 'CLOSED' else '; '.join(row['NEN_rejections'])
        lines.append(f"| {row['row']} | {row['bridge_status']} | {row['composed_status']} | {row['k3_status']} | {reason} |")
    lines += ['', '## Validation boundary', '', d['NEN_baseline_validation'], '',
              'No prover, native compiler or remote scope ran. Reading a historical successful receipt is evidence reuse, not a new replay. K-3 status does not lift K-2 or discharge any packet domain. Historical critical-path data remains explicitly historical. Full source statements, receipts, qualifications and rejected claims remain in JSON.', '']
    return '\n'.join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    inputs = Inputs()
    try:
        result = build(inputs)
    finally:
        inputs.close()
    artifacts = {'NEN_LEDGER.json': encode(result), 'NEN_LEDGER.md': markdown(result)}
    for name, contents in artifacts.items():
        require(len(contents.encode()) <= 20_000_000, 'oversize artifact: ' + name)
        if args.write:
            (E / name).write_text(contents)
        else:
            require((E / name).read_text() == contents, 'derived output drift: ' + name)
    print(json.dumps(dict(coverage=result['coverage'], composed_per_slice=result['NEN_composed_per_slice'], rejected_slice_rows=result['NEN_rejected_slice_closures']), indent=2))


if __name__ == '__main__':
    main()
