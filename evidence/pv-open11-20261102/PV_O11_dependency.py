#!/usr/bin/env python3
"""D577 document census only: no formal proof or host launch."""
import argparse
import hashlib
import json
import re
import subprocess
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent
# Immediate blockers at the row's scope. e's actual-conjunction prerequisites
# c,d are expanded below, and distinguished in the retained JSON.
GROUPS = {
    'a': 'V176 V181 V178 V369 V267 V171 V175 V172 V268 V271 V269',
    'ade': 'V239 V403',
    'ad': 'V249',
    'b': 'V374',
    'ag': 'V373 V380-inversion',
    'abcdefg': 'V346 V340 V397 V398 V399',
    'ae': 'V347 V348 V349 V350 V351 V352 V353 V354 V355 V356 V357 V358 V359 V360 V361 V362 V363 V364 V365 V366 V367 V368 V036 V037 V162',
    'a_prefix': 'V161',
    'abg': 'V166',
    'abe': 'V404 V405',
    'g': 'V370 V231 V232',
    'h': 'V371',
}
# V161's pre-body PrefixContract needs native reservation/state, not op227.
GROUPS['a'] += ' ' + GROUPS.pop('a_prefix')
REASONS = {
 'V239': 'ActualInput/OwnedPublicPlan and both transcript links need one native input, terminal callback and host_work execution; source dense/model witness is insufficient.',
 'V249': 'Actual checker Result/times, builders and host_work/worker effects, early rejection and panic=abort prefixes remain unbound.',
 'V403': 'NativePrefixBinding at every recursive op121 call, selected host_work/ordered merge and distinct terminal callback; canonical prefix model alone is insufficient.',
 'V374': 'Whole-client adopted-binary witness-class experiment is a client gate; fixture throughput and the old kernel harness are not that experiment.',
 'V373': 'Adopted-image operand/caller/inline/callee completeness and native joint observer remain; conditional scanner labels do not discharge V370/V371.',
 'V380-inversion': 'All actual operands and zero/pole/retry/failure events must share the native coupling; C056 stays K-3 suspended and compiler transfer remains.',
 'V346': 'Proved=shipped manifest must join all actual native instances, user client, publication and coherent audited release; source equality is insufficient.',
 'V340': 'Current event headline and same-release research/client adoption require the actual instances and coherent release, not historical adoption decisions.',
 'V036': 'Exact meanR must hold on the SAME installed actual coupling/carrier, not the proposed product projection.',
 'V037': 'Exact meanM must hold on the SAME installed actual coupling/carrier, not an uninstantiated sufficient product premise.',
 'V161': 'Complete prefix Result/state, reservation address and failure association need the native world; this pre-body contract does not itself require publication/op227.',
 'V162': 'Complete body proof/audit/Result/state includes actual callbacks/publication, not output-only success.',
 'V166': 'Actual caller ABI, deployed feature interpretation and compiler cohort must be associated with the retained contracts and user-client entry.',
 'V397': 'Final ordered replay waits for actual instances/user client/publication and coherent NER_, not cached imports of NDR.',
 'V398': 'Final NEP importAll/private HARD-ERROR closure audit waits for the same actual coherent endpoint; no skipped unresolved constants.',
 'V399': 'Every evidence class must identify the SAME final release, with actual client/instances and coherent replay/audit.',
 'V404': 'Transfer invocation/exclusion/order/minimal reached set needs actual native public/external/record and client route association.',
 'V405': 'Withdrawal invocation/exclusion/order/minimal reached set needs actual native public/external/record and client route association.',
 'V370': 'The compiler preservation gate is g itself; source structure cannot prove compiled trace preservation.',
 'V371': 'Only h: retained pinned-CPU data-independent latency/DOITM owner boundary. No extraction/source equality or finite timing establishes it.',
 'V231': 'Selected software/SHA-NI finalizer and intrinsic/backend transfer remain under the V370 compiler-cohort boundary; source-only body facts remain scoped.',
 'V232': 'Selected SHA update-block state/callback law and std/intrinsic compiler-cohort transfer remain; bounded helper checks are not a whole row.',
}
for row in GROUPS['a'].split():
    REASONS.setdefault(row, 'The complete native carrier/decoder, ownership and returned Result/post-world must instantiate the existing link in the SAME actual caller/observer frame; see PROGRESS11 exact premise.')
for row in GROUPS['ae'].split():
    REASONS.setdefault(row, 'Full SAME-cp raw-input/history and failed/rejected native prefixes require event-world plus actual RunJoin/publication; local model/source trace facts do not install these links.')


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def build():
    triage = (ROOT / 'TRIAGE11.md').read_text()
    ranked_text = triage.split('## Ranked unowned queue\n', 1)[1].split('## Excluded live rows', 1)[0]
    ranked = re.findall(r'^\|(\d+)\|(V[^|]+)\|([^|]+)\|(.+)\|$', ranked_text, re.M)
    assert len(ranked) == 55 and [int(x[0]) for x in ranked] == list(range(1, 56))
    immediate = {}
    for tags, ids in GROUPS.items():
        for row in ids.split():
            assert row not in immediate, row
            immediate[row] = sorted(tags)
    assert set(immediate) == {x[1] for x in ranked}
    exact = {}
    reports = ['PV_O11_next-rows.json', 'PV_O11_open-sync.json',
               'PV_O11_ranked-links.json', 'PV_O11_l3-review.json', 'PV_O11_release-review.json']
    for report in reports:
        for row, entry in json.loads((ROOT / report).read_text())['rows'].items():
            exact[row] = entry['exact_premise']
    for report in ['PV_O11_write-all.json', 'PV_O11_V176-binding-status.json']:
        entry = json.loads((ROOT / report).read_text())
        exact[entry['row']] = entry['exact_remaining_premise']
        reports.append(report)
    for path, pin in json.loads((ROOT / 'PV_O11_input-pins.json').read_text()).items():
        raw = subprocess.check_output(['git', 'show', pin['blob']])
        assert hashlib.sha256(raw).hexdigest() == pin['sha256'], path
    rows = []
    for rank, row, cost, obligation in ranked:
        tags = set(immediate[row])
        if 'e' in tags:
            tags.update('cd')
        assert tags <= set('abcdefgh')
        assert ('h' not in tags or tags == {'h'})
        section = triage.split(f'### {row} — ', 1)[1].split('\n### ', 1)[0]
        definition = re.search(r'Definition: (.+)', section).group(1)
        rows.append(dict(rank=int(rank), row=row, immediate=immediate[row], obligations=sorted(tags),
                         triage_next_obligation=obligation, residual=exact.get(row, obligation), reason=REASONS[row], definition=definition,
                         status='OPEN', restored=False))
    counts = dict(sorted(Counter(t for r in rows for t in r['obligations']).items()))
    assert sum(counts.values()) >= 55
    inputs = ['TRIAGE11.md', 'PROGRESS11.md', 'PV_O11_input-pins.json',
              'inputs/l3/REPORT.md', 'inputs/l3/pv-l3-20261027-RESULTS.md'] + reports
    return dict(baseline='539caabb44', scope='55 ranked OPEN rows; overlapping necessary blockers',
                input_sha256={p: sha(ROOT / p) for p in inputs}, rows=rows, counts=counts,
                h_only=[r['row'] for r in rows if r['obligations'] == ['h']],
                restored=[], premises=dict(removed=0, added=0, weakened=0),
                new_scopes=dict(lean=0, native=0, kani=0), remaining=dict(lean=87, native=20),
                next_ids=dict(lean='90408', native='N90510', reserved_audit='90499'))


def render(data):
    names = {'a':'Native event world (pv-evh)', 'b':'User-client extraction/gates (pv-uc)',
             'c':'op227 / DeployedWrapper557', 'd':'op257 / V263',
             'e':'Publication + Nonempty P (runjoin)', 'f':'Coherent NER_ rebuild (D565)',
             'g':'V370 compiler cohort / K-3', 'h':'Row-specific only'}
    counts = '| Obligation | Rows |\n|---|---:|\n' + '\n'.join(
        f'| {t}: {names[t]} | {data["counts"].get(t, 0)} |' for t in names)
    table = '| Rank | Row | Shared obligations (closure) | Exact residual / why still OPEN |\n|---:|---|---|---|\n'
    table += '\n'.join(f'| {r["rank"]} | {r["row"]} | {", ".join(r["obligations"])} | {r["reason"]} Residual: {r["residual"]} |' for r in data['rows'])
    return counts, table


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    data = build()
    json_path = ROOT / 'PV_O11_dependency.json'
    doc_path = ROOT / 'DEPENDENCY11.md'
    counts, table = render(data)
    doc = doc_path.read_text()
    if args.check:
        assert json.loads(json_path.read_text()) == data
        assert counts in doc and table in doc
        assert data['h_only'] == ['V371'] and not data['restored']
        print(json.dumps(dict(rows=len(data['rows']), counts=data['counts'], h_only=data['h_only'], restored=[], result='PASS')))
    else:
        json_path.write_text(json.dumps(data, indent=2) + '\n')
        if '<!-- COUNTS -->' in doc:
            doc = doc.replace('<!-- COUNTS -->', counts).replace('<!-- ROWS -->', table)
        else:
            doc = re.sub(r'(## Coverage and counts\n\n).*?(\n\n## All 55 ranked rows)',
                         lambda m: m[1] + counts + m[2], doc, flags=re.S)
            doc = re.sub(r'(## All 55 ranked rows\n\n).*?(\n\n## The h-only frontier)',
                         lambda m: m[1] + table + m[2], doc, flags=re.S)
        doc_path.write_text(doc)

if __name__ == '__main__':
    main()
