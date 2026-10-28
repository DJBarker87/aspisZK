#!/usr/bin/env python3
"""Deterministic, conservative composition ledger. Python stdlib; no prover launch.

Read sparse files through Git without materializing other lanes. A present file
must equal the pinned blob; deletion of a materialized file is an error. --write
rebuilds derived artifacts; ordinary invocation compares them, never repairs them.
"""
import argparse
import collections
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
BASE = '898a8b0da7703af67b676b18b575236940830283'
FROZEN = '4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
DESIGN = 'docs/research/100bit-spend-path-20261013/design/'
OUT = 'evidence/native-ledger2-20261028/'
NCS = 'evidence/native-featparity-20261028/'
KNG = 'evidence/kani-undet-20261028/'
KNF = 'evidence/kani-k2leaf-20261028/'
INV = [('TX1', 'evidence/native-inv1-20261027/NBI1_INVENTORY.json'),
       ('TX2', 'evidence/native-inv2-20261027/NBI2_INVENTORY.json')]


def sha(b):
    return hashlib.sha256(b).hexdigest()


def dump(v):
    return json.dumps(v, indent=2, sort_keys=True, ensure_ascii=False) + '\n'


def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)


def canonical(s):
    # Retain lifetime/owner spelling. Only TX1's source-line suffix is removed.
    return re.sub(r'@\d+$', '', s)


class Store:
    def __init__(self):
        self.tree = {}
        for line in git('ls-tree', '-rl', BASE).decode().splitlines():
            meta, path = line.split('\t', 1)
            mode, kind, oid, size = meta.split()
            if kind == 'blob':
                self.tree[path] = (oid, int(size))
        self.head_tree = {}
        for line in git('ls-tree', '-r', 'HEAD').decode().splitlines():
            meta, path = line.split('\t', 1)
            self.head_tree[path] = meta.split()[2]
        self.proc = subprocess.Popen(['git', 'cat-file', '--batch'], cwd=ROOT,
                                     stdin=subprocess.PIPE, stdout=subprocess.PIPE)
        self.cache = {}
        self.used = {}
        self.deleted = set(git('ls-files', '--deleted').decode().splitlines())

    def blob(self, spec):
        self.proc.stdin.write((spec + '\n').encode())
        self.proc.stdin.flush()
        h = self.proc.stdout.readline().split()
        if len(h) != 3 or h[1] != b'blob':
            raise ValueError('missing Git blob: ' + spec)
        b = self.proc.stdout.read(int(h[2]))
        assert self.proc.stdout.read(1) == b'\n'
        return b

    def read(self, p, cite=True):
        if p not in self.tree:
            raise ValueError('missing evidence: ' + p)
        if self.head_tree.get(p) != self.tree[p][0]:
            raise ValueError('merged evidence missing or changed since snapshot: ' + p)
        if p in self.deleted:
            raise ValueError('deleted evidence: ' + p)
        if p not in self.cache:
            b = self.blob(self.tree[p][0])
            if (ROOT / p).exists():
                if sha((ROOT / p).read_bytes()) != sha(b):
                    raise ValueError('changed evidence: ' + p)
            self.cache[p] = b
        b = self.cache[p]
        if cite:
            self.used[p] = {'sha256': sha(b), 'bytes': len(b),
                            'git_blob': self.tree[p][0], 'revision': BASE}
        return b

    def obj(self, p):
        return json.loads(self.read(p))

    def text(self, p):
        return self.read(p).decode('utf-8', errors='replace')

    def close(self):
        self.proc.stdin.close()
        self.proc.wait()


def strip_anchor(p):
    return re.sub(r':\d+(?:[-–]\d+)?$', '', p).split('#')[0]


def collect():
    s = Store()
    # Every merged evidence packet's top-level prose reports, including legacy
    # reports under docs/research/.../evidence. Nested vendored/source READMEs
    # are excluded. Search the entire merged tree, not the sparse file set.
    report_paths = []
    for p in s.tree:
        if not p.endswith('.md') or '/evidence/' not in '/' + p:
            continue
        suffix = p.split('evidence/', 1)[1]
        if suffix.count('/') == 1 and not p.startswith(OUT):
            report_paths.append(p)
    report_paths += [p for p in s.tree if p.startswith(DESIGN) and p.endswith('.md')]
    report_paths = sorted(set(report_paths))
    current_reports = []
    for p in s.head_tree:
        if p.startswith(OUT) or not p.endswith('.md'):
            continue
        if p.startswith(DESIGN) or ('/evidence/' in '/' + p and p.split('evidence/', 1)[1].count('/') == 1):
            current_reports.append(p)
    assert sorted(set(current_reports)) == report_paths, 'merged report corpus changed; refresh evidence snapshot explicitly'
    docs = {p: s.text(p) for p in report_paths}
    ncs = s.obj(NCS + 'NCS_RESULTS.json')['rows']
    suspended = s.obj(NCS + 'NCS_SUSPENDED.json')
    kng = s.obj(KNG + 'KNG_RESULTS.json')
    knf = s.obj(KNF + 'KNF_PAIRS.json')
    for p in ['NCS_ASSOCIATIONS.json', 'NCS_VALIDATION.json']:
        s.read(NCS + p)
    for p in ['KNG_FEATURE_AUDIT.json', 'KNG_PROPERTY_AUDIT.json',
              'KNG_SOURCE_ASSOCIATION.json', 'KNG_RECONSTRUCTION_HASHES.json']:
        s.read(KNG + p)
    s.read(KNF + 'KNF_FEATURE_BODY_AUDIT.json')
    s.read(KNF + 'KNF_SOURCE_PINS.json')
    s.read('evidence/sound-int2-20261025/final-closure-manifest.json')
    patch = 'evidence/kani-mitig-20261028/KMX_copy_stubs.patch'
    patch_hash = sha(s.read(patch))
    restoration = {r['audit_row']: r for r in kng['rows']}
    assert {r['audit_id'] for r in ncs if r['classification'] == 'UNDETERMINED'} == set(restoration)
    for r in ncs:
        if r['classification'] == 'SAME BODIES':
            assert not r['differing_functions'] and not r['cfg_unknown_bodies'], r['id']
            assert all(h['original'] == h['deployed'] for h in r['reached_hashes']), r['id']
    for r in restoration.values():
        assert set(r['required_historical_attempts']) <= {p['historical_attempt'] for p in r['new_pairs']}, r['audit_row']
    receipt_index = collections.defaultdict(list)
    for p in s.tree:
        if p.endswith('/receipt.json'):
            receipt_index[p.split('/')[-2]].append(p)
    missing = []
    def cite(p):
        p = strip_anchor(p)
        if p not in s.tree:
            missing.append(p)
            return None
        s.read(p)
        return p
    def receipt(attempt):
        paths = receipt_index.get(attempt, [])
        # Prefer exact attempt directory, reject ambiguous copies unless equal.
        if not paths:
            missing.append('receipt for ' + attempt)
            return []
        for p in paths:
            s.read(p)
        hashes = {s.used[p]['sha256'] for p in paths}
        if len(hashes) > 1:
            # Contradictory attempt identities cannot be silently selected.
            raise ValueError('conflicting receipt hashes for ' + attempt)
        return [sorted(paths, key=lambda p: (p.count('/'), p))[0]]

    # Check every replacement pair independently, not the summary's PASS label.
    for pair in kng['pairs']:
        assert pair['status'] == 'RESTORED' and not pair['rule14']
        for key, positive in [('positive_result', True), ('control_result', False)]:
            r = pair[key]
            p = KNG + r['receipt']
            data = s.obj(p)
            assert sha(s.read(p)) == r['receipt_sha256'], p
            assert r['valid'] and not r['timeout'], p
            assert r['exit'] == (0 if positive else 1), p
            assert data['exit_status'] == r['exit'], p
    # KNF schema is retained verbatim, and all static pair receipts are pinned.
    for pair in knf:
        for key, expected_exit in [('positive', 0), ('control', 1)]:
            data = s.obj(KNF + pair[key] + '/receipt.json')
            assert data['exit_status'] == expected_exit, pair[key]
    knf_text = dump(knf)
    knf_receipts = []
    for attempt in sorted(set(re.findall(r'KNF_K\d{3}', knf_text))):
        knf_receipts += receipt(attempt)
    for p in knf_receipts:
        s.obj(p)

    inventories = {tx: s.obj(p) for tx, p in INV}
    functions = {}
    raw_entries = []
    source_cache = {}
    body_findings = []
    for tx, inv in inventories.items():
        assert len(inv['functions']) == (345 if tx == 'TX1' else 242)
        assert inv.get('source_revision', inv.get('frozen_revision')) == FROZEN
        for i, f in enumerate(inv['functions']):
            name = canonical(f['id'])
            functions.setdefault(name, []).append((tx, f))
            path = f['file']
            if path not in source_cache:
                source_cache[path] = s.blob(FROZEN + ':' + path)
            a, b = f.get('body_byte_range', [f.get('body_start_byte'), f.get('body_end_byte')])
            actual = sha(source_cache[path][a:b])
            if actual != f['body_sha256']:
                body_findings.append({'transaction': tx, 'function': name,
                                      'expected': f['body_sha256'], 'actual': actual,
                                      'range': [a, b]})
            raw_entries.append((tx, i, name, f))
    assert not body_findings, dump(body_findings)
    # Preserve independent inventory observations; do not erase differing edges.
    adjacency = {name: set() for name in functions}
    for tx, i, name, f in raw_entries:
        for call in f.get('callees', f.get('calls', [])):
            adjacency[name].update(canonical(t) for t in call.get('targets', []) if canonical(t) in functions)
    candidate_index = collections.defaultdict(list)
    for r in ncs:
        for root in r['roots']:
            if root in functions:
                candidate_index[root].append(r)
    # Documentary mentions for every function: qualified identities first;
    # then exact backtick owner::name tokens ONLY within a named source file.
    # These are discovery pointers, never proof credit.
    mentions = collections.defaultdict(list)
    unindexed = []
    known_sources = {strip_anchor(p) for r in ncs for p in r['sources']}
    for p, text in docs.items():
        candidates = []
        for name in functions:
            file, tail = name.split('::', 1)
            if name in text or ((file in text or Path(file).name in text) and (f'`{tail}`' in text or f"`{tail.replace(chr(60)+chr(39)+'a'+chr(62), '')}`" in text)):
                candidates.append(name)
        if not candidates:
            continue
        for line_no, line in enumerate(text.splitlines(), 1):
            if len(line) > 20000:
                continue
            for name in candidates:
                file, tail = name.split('::', 1)
                short = tail.replace("<'a>", '')
                exact = name in line
                if exact or (f'`{tail}`' in line or f'`{short}`' in line) and (file in text or Path(file).name in text):
                    hit = {'path': p, 'line': line_no, 'text': line[:3000],
                           'association': 'exact function ID' if exact else 'owner token plus source-file context'}
                    mentions[name].append(hit)
                    if 'CLOSED' in line and p not in known_sources:
                        unindexed.append({'function': name, **hit})
    # Build packet claims with exact source detail and receipts, not transitive
    # credit for every function in NCS's conservative reached cone.
    claims = {}
    for name, rows in candidate_index.items():
        claims[name] = []
        for r in rows:
            ev = [NCS + 'NCS_RESULTS.json', NCS + 'NCS_ASSOCIATIONS.json']
            ev += [v for p in r['sources'] if (v := cite(p))]
            rs = []
            for attempt in r.get('positive_receipts', []):
                rs += receipt(attempt)
            fix = restoration.get(r['audit_id'])
            parity = r['classification']
            if fix:
                assert fix['status'] == 'RESTORED'
                parity = 'SAME BODIES + KNG replacement property'
                ev += [KNG + 'KNG_RESULTS.json', KNG + 'KNG_FEATURE_AUDIT.json',
                       KNG + 'KNG_SOURCE_ASSOCIATION.json', KNG + 'KNG_PROPERTY_AUDIT.json']
                for pair in fix['new_pairs']:
                    rs += [KNG + pair['positive'], KNG + pair['control']]
            quarantine = r.get('quarantined_support', [])
            replaced_quarantine = []
            if r['packet'] == 'P6':
                ev += [KNF + 'KNF_FINDING.md', KNF + 'KNF_LEAF_DEPENDENCY.md',
                       KNF + 'KNF_SOURCE_ASSOCIATION.md', KNF + 'KNF_FEATURE_BODY_AUDIT.json', KNF + 'KNF_PAIRS.json']
                rs += knf_receipts
                replaced_quarantine = quarantine
                quarantine = []
                if name.endswith('verifier.rs::checkpoint'):
                    ev += [v for p in ['evidence/kani-reverify5-20261028/KNE_FINDING.md',
                                      'evidence/kani-reverify5-20261028/KNE_PAIRS.json',
                                      'evidence/kani-reverify5-20261028/KNE_COVERAGE.json'] if (v := cite(p))]
                    # Original packet is retained as superseded history.
            # NCS narrow copy replay families are fragments, not complete bodies.
            fragment = r['packet'] in ['KMX', 'KMZ'] or len(r['roots']) != 1 or 'inactive serializer' in r['member']
            reason = []
            if fragment:
                reason.append('fragment or ambiguous multi-root attribution; no whole-body credit')
            if parity == 'UNDETERMINED':
                reason.append('rule15 historical harness association unresolved')
            if quarantine:
                reason.append('rule14 supporting observation quarantined')
            all_ev = sorted(set(ev + rs))
            for p in all_ev:
                cite(p)
            c = {'claim_id': r['id'], 'audit_id': r['audit_id'],
                 'reported_status': r['credited_status'], 'medium': 'P6 hybrid',
                 'feature_parity': parity, 'profile': r['profile'],
                 'source_claim_text': r['detail'], 'evidence': all_ev,
                 'receipts': sorted(set(rs)), 'quarantined_support': quarantine,
                 'replaced_quarantined_support': replaced_quarantine,
                 'stub_attributes': r.get('all_stubs', []),
                 'arithmetic_stubs': r.get('arithmetic_stubs', []),
                 'admissible_local_credit': not reason,
                 'limitations': reason,
                 'named_hypotheses': [
                     {'name': r['audit_id'] + '.PacketDomain',
                      'statement': 'Exact domain and same-input/Result/carrier qualifications in source_claim_text and cited packet; no caller instance inferred.',
                      'discharged_by': None},
                     {'name': r['audit_id'] + '.PhysicalInterpretation',
                      'statement': 'Retained source/library/allocator/runtime/tool and emitted-definition association qualifications of this packet.',
                      'discharged_by': None}],
                 'composition_trust': 'Owner amendment fifth: P6/D188 semantic-transport reclassification, never proof removal'}
            claims[name].append(c)
    # Later contract/reference packets postdate NCS's whole-member index.
    supplemental = json.loads((ROOT / 'evidence/native-compledger-20261028/NCZ_SUPPLEMENTAL.json').read_text())
    for spec in supplemental:
        prefix = spec['id'].split('::')[0].split('_')[-1]
        directory = 'evidence/' + spec['packet'] + '/'
        evidence = [directory + p for p in spec['reports']]
        rs = list(spec.get('additional_receipts', []))
        for p in rs:
            s.read(p)
        verdicts = []
        for kind in ['positive', 'negative', 'shape_positive', 'shape_negative', 'lean']:
            for number in spec[kind]:
                attempt = prefix + ('_L' if kind == 'lean' else '_K') + f'{number:03d}'
                p = directory + attempt + '/receipt.json'
                data = s.obj(p)
                rs.append(p)
                actual = data['exit_status']
                if not spec.get('native_verdicts_from_receipts'):
                    assert actual == (1 if 'negative' in kind else 0), (attempt, kind, actual)
                if kind != 'lean':
                    log = s.text(directory + attempt + '/stdout.log')
                    failed = re.findall(r'\*\* (\d+) of \d+ failed', log)
                    assert failed and failed[-1] == ('1' if 'negative' in kind else '0'), (attempt, 'non-semantic or multiple failure control', failed)
                    assert ('VERIFICATION:- FAILED' if 'negative' in kind else 'VERIFICATION:- SUCCESSFUL') in log, attempt
                verdicts.append({'attempt': attempt, 'kind': kind, 'exit': actual})
                for suffix in ['-graph-check.json', '-graph.json', '-lock-check.json', '-source-check.json']:
                    gp = directory + attempt + suffix
                    if gp in s.tree:
                        g = s.obj(gp)
                        if spec['admit'] and kind in ['positive', 'negative'] and suffix == '-graph-check.json':
                            project = next(x for x in g['selected_closure'] if x['name'] == 'aspis-r1-cost-probe')
                            assert {'default', 'private-leaf-salts', 'optimized-terminal', 'program-build'} <= set(project['features']), (attempt, 'deployed feature selection')
                        evidence.append(gp)
        for p in evidence:
            s.read(p)
        for name in spec.get('functions', [spec.get('function')]):
            assert name in functions, name
            cid = spec['id'] + ('::' + name.split('::', 1)[1] if 'functions' in spec else '')
            claims.setdefault(name, []).append({
                'claim_id': cid, 'audit_id': cid,
                'reported_status': 'CLOSED-CONDITIONAL local component; full caller association OPEN',
                'medium': spec['medium'], 'reference_medium': spec.get('reference_medium'),
                'feature_parity': spec['feature_status'], 'profile': 'packet-qualified',
                'source_claim_text': [spec['domain']],
                'evidence': sorted(set(evidence + rs)), 'receipts': sorted(set(rs)),
                'quarantined_support': [], 'replaced_quarantined_support': [],
                'stub_attributes': [], 'arithmetic_stubs': [],
                'admissible_local_credit': spec['admit'],
                'limitations': [] if spec['admit'] else ['No new deployed whole-body credit: retain exact feature/model/caller association limits in domain and feature_parity'],
                'native_pair_verdicts': verdicts,
                'named_hypotheses': [
                    {'name': cid + '.PacketDomain', 'statement': spec['domain'], 'discharged_by': None},
                    {'name': cid + '.PhysicalInterpretation', 'statement': 'Exact accepted reference/tool/source/features and physical call transport; no enclosing SDK/native caller certificate.', 'discharged_by': None}],
                'composition_trust': 'Owner amendment fifth: P6/D188 semantic-transport reclassification, never proof removal'})
    from NDK_review import refresh_claims
    refresh = refresh_claims(s, functions, claims)
    # Name algorithmic conditions explicitly, rather than hiding them inside a
    # generic PacketDomain wrapper. Their exact spelling is retained from JSON
    # condition arrays or the authoritative per-member packet.
    condition_names = ['DigestEncodeRaw', 'DigestEncodeCanonical', 'DigestDecode',
                       'TransferEncode', 'WithdrawalEncode', 'DriverEstablishedDomain']
    for name, cs in claims.items():
        for c in cs:
            statements = []
            for raw in c['source_claim_text']:
                try:
                    obj = json.loads(raw)
                    statements.extend(obj.get('conditions', []))
                except (ValueError, TypeError):
                    pass
            body = '\n'.join(c['source_claim_text'])
            for condition in condition_names:
                if condition in body:
                    statements.append(condition)
            if c['claim_id'] == 'P6::verifier::checkpoint':
                statements.append('DriverEstablishedDomain')
                c['history'] = [{'status': 'superseded', 'evidence': 'evidence/leaf-p6-11-20261027/LPm_checkpoint_LEAF.md', 'reason': 'KNE reached-S2/final_len64/weights64 writer route supersedes arbitrary-growth/old append association'}]
            for condition in sorted(set(statements)):
                c['named_hypotheses'].append({'name': condition,
                    'statement': condition + ': exact law/domain in cited packet, with same Result/effects/carrier; local component evidence does not instantiate this caller law.',
                    'discharged_by': None})
    # Pin actual receipts, their run logs (axiom audits retained in stdout) and
    # neighbouring machine summaries. Missing historical references are findings,
    # never fabricated citations.
    cited_receipts = sorted({p for cs in claims.values() for c in cs for p in c['receipts']})
    for p in cited_receipts:
        for filename in ['stdout.log', 'time.log', 'classification.json', 'feature_association.json']:
            q = str(Path(p).parent / filename)
            if q in s.tree:
                s.read(q)
    # Pin source snapshots matching the receipt's declared sha256, and nearby
    # graph/lock/feature/copy controls. Historical unmatched source pointers
    # remain source-association obligations rather than silently using HEAD.
    for p in cited_receipts:
        data = s.obj(p)
        for source, digest in data.get('source_hashes', {}).items():
            q = str(Path(p).parent / 'sources' / source)
            if q in s.tree and s.tree[q][1] < 20 * 1024 * 1024:
                b = s.read(q)
                assert sha(b) == digest, ('receipt source mismatch', p, q)
        directory = str(Path(p).parent.parent)
        attempt = Path(p).parent.name
        for suffix in ['-graph.json', '-graph-check.json', '-metadata.json',
                       '-lock-check.json', '-source-check.json']:
            q = directory + '/' + attempt + suffix
            if q in s.tree:
                s.read(q)
    # Audit all explicitly referenced attempt IDs in relevant bridge packets.
    # Their manifests remain indexed even where they cannot earn local credit.
    support_receipts = collections.defaultdict(list)
    relevant_dirs = {str(Path(p).parent) for cs in claims.values() for c in cs for p in c['evidence'] if p.endswith('.md')}
    for directory in sorted(relevant_dirs):
        packet_docs = [t for p, t in docs.items() if str(Path(p).parent) == directory]
        ids = set(re.findall(r'\b[A-Za-z][A-Za-z0-9]*_(?:K|L)\d{3}\b', '\n'.join(packet_docs)))
        for attempt in sorted(ids):
            for p in receipt(attempt):
                support_receipts[directory].append(p)
    # No claim is unconditional: local theorems retain explicit domain/physical
    # hypotheses. This is intentionally stronger than repeating CLOSED labels.
    local_status = {}
    for name in functions:
        cs = claims.get(name, [])
        if any(c['admissible_local_credit'] for c in cs):
            local_status[name] = 'CLOSED-CONDITIONAL'
        elif any(c['quarantined_support'] for c in cs):
            local_status[name] = 'quarantined'
        else:
            local_status[name] = 'OPEN'
    # A pure trust-value row is separate from the digest wrapper's local byte
    # transport. Never silently mark the whole wrapper trusted/closed.
    trust_rows = [
        {'id': 'RuntimeSha256Value', 'medium': 'trust row',
         'scope': 'SolanaDigest/hashv reply value realises H. Exact ordered request slices and unchanged reply are separate bridge obligations; coherent dictionary slots op43/op44 are digest/error.',
         'evidence': [DESIGN + 'SECURITY-CONTRACT-20261021.md', 'evidence/sound-int2-20261025/HANDOFF.md']},
        {'id': 'RuntimePersistence', 'medium': 'trust row',
         'scope': 'CPR_DataPersistence.TwoTransactionLaw; approved two-transaction history law. Does not instantiate same-saved-checkpoint caller bytes.',
         'evidence': [DESIGN + 'SECURITY-CONTRACT-20261021.md']},
        {'id': 'NativeContractSemanticTransport', 'medium': 'trust row',
         'scope': 'Owner amendment fifth, scoped to accepted body/reference/dictionary/features/encoding/tool receipts. Reclassification of P6/D188, not assumption removal.',
         'evidence': [DESIGN + 'SECURITY-CONTRACT-20261021.md']}]
    for tr in trust_rows:
        for p in tr['evidence']:
            cite(p)
    graph = {k: sorted(v) for k, v in adjacency.items()}
    reverse = {k: set() for k in graph}
    for caller, targets in graph.items():
        for target in targets:
            reverse[target].add(caller)
    def reachable(start, edges):
        seen = set()
        todo = list(edges[start])
        while todo:
            x = todo.pop()
            if x not in seen:
                seen.add(x)
                todo.extend(edges[x])
        return seen - {start}
    downstream = {k: reachable(k, graph) for k in graph}
    upstream = {k: reachable(k, reverse) for k in graph}
    # SCCs from mutual reachability, deterministically named. Conservative
    # inventory unions can create spurious cycles, which are reported verbatim.
    components, assigned = [], set()
    for name in sorted(graph):
        if name not in assigned:
            group = {name} | (downstream[name] & upstream[name])
            components.append(sorted(group))
            assigned.update(group)
    component_of = {name: i for i, group in enumerate(components) for name in group}
    open_names = {k for k, v in local_status.items() if v in ['OPEN', 'quarantined']}
    open_components = {component_of[k] for k in open_names}
    frontier = []
    for i in sorted(open_components):
        group = components[i]
        reached_open = {component_of[t] for t in downstream[group[0]] if t in open_names} - {i}
        if not reached_open:
            candidates = sorted(set(group) & open_names)
            chosen = sorted(candidates, key=lambda n: (-len(upstream[n]), n))[0]
            frontier.append({'representative': chosen, 'open_scc_members': candidates,
                             'all_scc_members': group, 'dependent_functions': len(upstream[chosen]),
                             'dependent_rows': sum(len(functions[x]) for x in upstream[chosen])})
    frontier.sort(key=lambda r: (-r['dependent_rows'], r['representative']))
    assert all(any(t['representative'] == k or t['representative'] in downstream[k] for t in frontier) for k in open_names)
    rows_out = []
    units = {}
    for tx, inv in inventories.items():
        units[tx] = inv.get('bridge_units', inv.get('bridge_units_bottom_up'))
    for tx, i, name, f in raw_entries:
        memberships = [u for u in units[tx] if f.get('row') in u['members'] or name in u['members'] or canonical(f['id']) in [canonical(x) for x in u['members']]]
        cs = claims.get(name, [])
        best = [c for c in cs if c['admissible_local_credit']]
        selected = sorted(best, key=lambda c: (c['claim_id'].startswith('P6::') is False, c['claim_id']))[:1]
        edges = f.get('callees', f.get('calls', []))
        obligations = []
        for target in graph[name]:
            obligations.append({'id': 'call-domain:' + name + '->' + target,
                                'callee': target, 'caller': name,
                                'required': 'Prove this actual use establishes the selected callee PacketDomain, canonical carrier, same inputs, state, Result and ordered effects; resolve conservative alternative targets before pruning.',
                                'callee_local_status': local_status[target],
                                'callee_claims': [c['claim_id'] for c in claims.get(target, []) if c['admissible_local_credit']],
                                'required_named_hypotheses': sorted({h['name'] for c in claims.get(target, []) if c['admissible_local_credit'] for h in c['named_hypotheses']}),
                                'owner': 'Aspis S2 lead / ' + name + ' bridge owner',
                                'owner_packets': sorted({c['claim_id'].split('::')[0] for c in claims.get(name, [])}),
                                'discharged_by': None, 'status': 'OPEN'})
        external = [c for c in edges if not c.get('targets')]
        for c in external:
            obligations.append({'id': f'external:{tx}:{i+1}:{len(obligations)}',
                                'call': c, 'owner': 'Aspis S2 lead / ' + name + ' bridge owner',
                                'owner_packets': sorted({c['claim_id'].split('::')[0] for c in claims.get(name, [])}),
                                'required': 'Classify constructor/scalar operation or bind the exact SDK/std/allocator/runtime/callback law in the same execution. Inventory external does not itself imply trust adoption.',
                                'status': 'OPEN', 'discharged_by': None})
        evidence_paths = {p for c in cs for p in c['evidence']}
        for m in mentions.get(name, []):
            evidence_paths.add(m['path'])
        receipt_paths = {p for c in cs for p in c['receipts']}
        for directory in relevant_dirs:
            if any(p.startswith(directory + '/') for p in evidence_paths):
                receipt_paths.update(support_receipts[directory])
        rows_out.append({'row': f'{tx}:{i+1:03d}', 'inventory_id': f['id'],
                         'inventory_row': f.get('row'), 'transaction': tx,
                         'inventory_evidence': {'path': dict(INV)[tx], 'sha256': s.used[dict(INV)[tx]]['sha256']},
                         'frozen_body_byte_range': f.get('body_byte_range', [f.get('body_start_byte'), f.get('body_end_byte')]),
                         'source_file_sha256': sha(source_cache[f['file']]),
                         'function': name, 'frozen_body_sha256': f['body_sha256'],
                         'frozen_body_verified': True, 'source_file': f['file'],
                         'source_line': f['line'],
                         'callees': edges, 'canonical_callees': graph[name],
                         'inventory_domain_obligations': [{'unit': u['id'], 'domain': u['domain'], 'status': 'OPEN', 'discharged_by': None} for u in memberships],
                         'bridge_status': local_status[name],
                         'selected_claims': [c['claim_id'] for c in selected],
                         'claim_ids': [c['claim_id'] for c in cs],
                         'medium': sorted({c['medium'] for c in cs}),
                         'feature_parity_summary': ('Selected local claim has NCS/KNG or explicit deployed-feature association, with target/ABI limits retained' if selected else 'UNDETERMINED for a whole-body native bridge; see per-claim feature evidence and OPEN/quarantine status'),
                         'feature_parity': [{'claim': c['claim_id'], 'status': c['feature_parity']} for c in cs],
                         'caller_domain_obligations': obligations,
                         'incoming_domain_obligation_owners': sorted(reverse[name]),
                         'named_hypotheses': [h for c in selected for h in c['named_hypotheses']],
                         'composed_status': 'OPEN',
                         'composed_reason': 'No per-edge caller-domain/physical interpretation certificate is newly instantiated by this evidence audit; packet-internal proofs retain their original scope. Local fragment and model-only evidence cannot fill it.',
                         'open_transitive_dependencies': sorted(downstream[name] & open_names),
                         'evidence': sorted(evidence_paths), 'receipts': sorted(receipt_paths),
                         'receipt_sha256': {p: s.used[p]['sha256'] for p in sorted(receipt_paths)},
                         'discovery_mentions': mentions.get(name, []),
                         'trust_rows': ['RuntimeSha256Value'] if name.endswith('::SolanaDigest::digest') else [],
                         'no_credit_reason': None if best else 'No unquarantined whole-body bridge with resolved feature association in the merged audited index; inspect discovery mentions for later partial or unindexed claims.'})
    coverage = {}
    for tx in ['TX1', 'TX2', 'all_rows']:
        chosen = [r for r in rows_out if tx == 'all_rows' or r['transaction'] == tx]
        coverage[tx] = {'rows': len(chosen), 'local_bridge_status': dict(sorted(collections.Counter(r['bridge_status'] for r in chosen).items())),
                        'composed_status': dict(collections.Counter(r['composed_status'] for r in chosen)),
                        'covered_only_by_trust': 0,
                        'conditional_is_not_whole_execution_closure': True}
    coverage['unique_functions'] = {'count': len(functions), 'local_bridge_status': dict(sorted(collections.Counter(local_status.values()).items()))}
    ledger = {'schema_version': 2, 'baseline_revision': BASE, 'frozen_revision': FROZEN,
              'headline': 'AspisR1.RPx_Deployed.deployed',
              'scope': '587 inventory occurrences, canonical union for advisory graph analysis; source/inventory/evidence audit, not a new refinement proof',
              'status_semantics': {'bridge_status': 'Conservative LOCAL whole-body packet status. CLOSED-CONDITIONAL retains named packet domain and physical-interpretation hypotheses. Fragment/root associations are not whole-body credit.',
                                   'composed_status': 'CLOSED requires every selected hypothesis and call-domain obligation discharged and no open/quarantined dependency. No such new certificate is supplied here.',
                                   'superseded': 'Per-claim/history disposition; never erase historical receipts or treat superseded proof as current credit.'},
              'medium_policy': 'P6 hybrid claims reused as qualified; no new D188-faithful or reference-extraction-equality credit inferred from cohort names; contract transport remains owner-approved trust reclassification.',
              'copy_stub_patch_sha256': patch_hash,
              'coverage': coverage, 'rows': rows_out,
              'supplemental_input_sha256': sha((ROOT / 'evidence/native-compledger-20261028/NCZ_SUPPLEMENTAL.json').read_bytes()),
              'claims': [c | {'function': name} for name in sorted(claims) for c in claims[name]],
              'trust_rows': trust_rows,
              'critical_path': {'method': 'In canonical conservative union graph choose one OPEN/quarantined representative from each terminal SCC under reachability between OPEN SCCs. This is a minimum-cardinality reachability cover of all OPEN functions, not a dynamic/runtime critical path or a sufficient proof set.',
                                'minimality': 'Every terminal open SCC needs its own representative; no other open SCC can be reached downstream from it. Every open SCC reaches a terminal open SCC.',
                                'frontier': frontier,
                                'highest_impact_open': [{'function': k, 'dependent_functions': len(upstream[k]), 'dependent_rows': sum(len(functions[x]) for x in upstream[k])} for k in sorted(open_names, key=lambda k: (-sum(len(functions[x]) for x in upstream[k]), k))[:20]],
                                'cycles': [g for g in components if len(g) > 1 or g[0] in graph[g[0]]]},
              'discovery': {'report_count': len(docs), 'report_paths': report_paths,
                            'unindexed_closed_mentions': unindexed,
                            'policy': 'All top-level merged evidence reports, legacy research evidence reports and design documents searched. Exact function IDs or exact owner tokens within source-file context are retained; no substring/suffix-only proof adoption. Historical nested sources/logs are inputs only through cited receipts.',
                            'unresolved_references': sorted(set(missing)),
                            'unresolved_reference_policy': 'Not citations: unresolved historical dependency pointers are findings. They never supply closure or receipts.'},
              'quarantine': suspended['inherited_rule14_quarantine'],
              'replacement_policy': 'KNF static re-credit of P6 local leaves; KNG replacement of 23 NCS property associations. Original receipts remain quarantined or superseded. No global quarantine lift.',
              'evidence_manifest': dict(sorted(s.used.items())),
              'refresh': refresh,
              'budget': {'lean_used': 0, 'lean_limit': 10, 'kani_used': 0, 'kani_limit': 0}}
    from NDK_review import finish_refresh
    finish_refresh(ledger)
    # Required evidence of every ledger row must be in the manifest.
    validate_invariants(ledger)
    s.close()
    return ledger


def validate_invariants(d):
    from NDK_review import validate_refresh
    validate_refresh(d)
    assert len(d['rows']) == 587
    ids = {r['row'] for r in d['rows']}
    assert len(ids) == 587
    claims = {c['claim_id']: c for c in d['claims']}
    for r in d['rows']:
        assert r['frozen_body_verified']
        assert r['feature_parity_summary']
        assert r['inventory_evidence']['sha256'] == d['evidence_manifest'][r['inventory_evidence']['path']]['sha256']
        for p, digest in r.get('receipt_sha256', {}).items():
            assert digest == d['evidence_manifest'][p]['sha256'], ('receipt hash mismatch', p)
        for p in r['evidence'] + r['receipts']:
            assert p in d['evidence_manifest'], ('uncited artifact', p)
        for claim in r['selected_claims']:
            assert claims[claim]['admissible_local_credit']
            assert not claims[claim]['quarantined_support']
            assert not claims[claim]['feature_parity'].startswith('UNDETERMINED')
        for status_key in ['bridge_status', 'composed_status']:
            if r[status_key] == 'CLOSED':
                assert not [h for h in r['named_hypotheses'] if not h['discharged_by']], ('open hypothesis', r['row'])
                assert all(o['status'] == 'CLOSED' and o['discharged_by'] for o in r['caller_domain_obligations']), ('open call domain', r['row'])
                assert not r['open_transitive_dependencies'], ('open/quarantined dependency', r['row'])
                assert r['selected_claims'], ('no bridge certificate', r['row'])
        if r['bridge_status'] == 'CLOSED-CONDITIONAL':
            assert r['selected_claims'] and r['named_hypotheses']


def inherited_markdown(d):
    lines = ['# Native composition ledger', '',
             f"Frozen source `{FROZEN}`; merged evidence snapshot `{BASE}`.",
             'Headline `AspisR1.RPx_Deployed.deployed`. **The deployed 100-bit target remains unestablished.**', '',
             'This is a machine-validated evidence ledger and conservative call-graph argument. It does not supply new native bridges or Lean caller-domain certificates. Owner amendment fifth is reported as a P6/D188 tool-trust reclassification, never premise removal.', '',
             '| Inventory | Rows | Local conditional bridges | Local OPEN | Quarantined | Composed OPEN | Trust only |',
             '|---|---:|---:|---:|---:|---:|---:|']
    for tx in ['TX1', 'TX2', 'all_rows']:
        c = d['coverage'][tx]; st = c['local_bridge_status']
        lines.append(f"| {tx} | {c['rows']} | {st.get('CLOSED-CONDITIONAL',0)} | {st.get('OPEN',0)} | {st.get('quarantined',0)} | {c['composed_status'].get('OPEN',0)} | 0 |")
    lines += ['', f"Unique functions: {d['coverage']['unique_functions']['count']}. Shared TX1/TX2 bodies count once only in the union graph; transaction rows keep separate edges/domains.", '',
              'Every conditional bridge retains two named hypotheses: its exact packet domain and its physical interpretation. The original statement/qualifications appear verbatim in `claims[].source_claim_text` and the pinned packet. Every call edge has a named caller-owned domain obligation; absent same-execution discharge is explicitly OPEN. Inventory domain prose is a proposed obligation, never its proof. Model/extraction names alone earn no credit.', '',
              'The ledger distinguishes reported historical labels, admissible local claims, quarantined support, replacements, feature parity and composed status. KNF restores local leaf support through static proofs without clearing historical pointer receipts. KNG supplies replacement properties for the 23 NCS unresolved associations; it does not widen their domains. KMX/KMZ copy windows and ambiguous multi-root claims remain fragments. The digest wrapper transports bytes; `RuntimeSha256Value` alone supplies its value law. Coherent digest/error slots are op43/op44.', '',
              '## Critical path', '',
              d['critical_path']['method'], '', d['critical_path']['minimality'], '',
              '**Inventory caveat:** conservative arithmetic carrier unions include self/cyclic edges (e.g. CM31::add). These are retained, not pruned by guessed types. Ranking is advisory until carrier resolution is proved. Closing the frontier still leaves callers, domain transport, effects and physical interpretation to prove.', '',
              '| Highest-impact OPEN function | Other inventory rows depending on it |', '|---|---:|']
    for r in d['critical_path']['highest_impact_open'][:10]:
        lines.append(f"| `{r['function']}` | {r['dependent_rows']} |")
    lines += ['', f"Minimum reachability-cover frontier: **{len(d['critical_path']['frontier'])} SCC representatives**. Full members and all graph cycles are in JSON.", '',
              '| Frontier representative | Dependent rows | OPEN functions in SCC |', '|---|---:|---:|']
    for r in d['critical_path']['frontier']:
        lines.append(f"| `{r['representative']}` | {r['dependent_rows']} | {len(r['open_scc_members'])} |")
    lines += ['', '## Reproduction and boundaries', '',
              '`python3 evidence/native-compledger-20261028/NCZ_validate.py` recomputes bodies, edges, claims, feature/re-credit overlays, receipt hashes, coverage and frontier, then compares the entire ledger and this summary. `--write` deliberately regenerates derived files; it does not make new evidence pass. Present sparse-worktree files must match the pinned Git blobs, and tracked deletions fail. Unmaterialized sparse files are read from immutable Git objects. Each cited artifact is SHA256-pinned. New/changed merged reports require an explicit refreshed snapshot; no silent credit from later branches.', '',
              f"Discovery searched **{d['discovery']['report_count']}** top-level merged/legacy evidence and design reports. Documentary mentions are discovery pointers, not semantic adoption. Unindexed CLOSED mentions and unresolved historical reference pointers are retained in JSON for audit; an unresolved pointer is never presented as a valid citation. Every cited row artifact must exist and match. The validator checks indexed evidence consistency; it is not a natural-language theorem prover and cannot detect a contradiction hidden in arbitrary new prose without an explicit evidence/schema update.", '',
              'No Rust/Lean/Kani/SBF job ran; no new theorem or axioms. 0/10 Lean status attempts, 0/0 Kani. No shipped files changed, so ELF rebuild was not triggered. No host/cache/key operation. Prior ELF pins remain inherited, not reproduced.', '']
    return '\n'.join(lines)


def markdown(d):
    from NDK_review import summary
    return summary(d, inherited_markdown(d))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true')
    parser.add_argument('--ledger', type=Path, default=HERE / 'NDK_LEDGER.json')
    args = parser.parse_args()
    if args.ledger.exists() and not args.write:
        existing = json.loads(args.ledger.read_text())
        validate_invariants(existing)
    expected = collect()
    expected_text = dump(expected)
    summary = markdown(expected)
    if args.write:
        args.ledger.write_text(expected_text)
        (HERE / 'NDK_LEDGER.md').write_text(summary)
    else:
        assert args.ledger.read_text() == expected_text, 'ledger differs from recomputed evidence; do not hand-edit closure'
        assert (HERE / 'NDK_LEDGER.md').read_text() == summary, 'summary differs from computed ledger'
    print(dump({'exit_status': 0, 'coverage': expected['coverage'],
                'pinned_artifacts': len(expected['evidence_manifest']),
                'reports_searched': expected['discovery']['report_count'],
                'critical_frontier_size': len(expected['critical_path']['frontier']),
                'unresolved_historical_pointers': len(expected['discovery']['unresolved_references']),
                'lean_used': 0, 'kani_used': 0}))


if __name__ == '__main__':
    try:
        main()
    except (AssertionError, ValueError, KeyError, OSError) as e:
        print('NDK validation FAILED: ' + str(e), file=sys.stderr)
        sys.exit(1)
