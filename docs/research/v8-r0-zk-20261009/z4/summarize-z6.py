#!/usr/bin/env python3
"""Audit the Z6 log and emit summary-Z6.json and evidence-Z6.json.
Checks: exact challenge replay against probe-C.log, every (B)-(A) and (A)-(C)
row comparison, the H1-padding supplement, the cell-dependence classes, and
the compiled-source hashes against this checkout."""
import ast, hashlib, json, pathlib, re, sys
here = pathlib.Path(__file__).resolve().parent
root = here.parents[3]
log = (here / 'probe-Z6.log').read_text().splitlines()
old = (here / 'probe-C.log').read_text().splitlines()
pick = lambda lines, p: [l for l in lines if l.startswith(p)]
# 1. exact replay of Z4c's 20 challenge vectors
for p in ('TRIAL_SEED ', 'CHALLENGE '):
    assert pick(log, p) == pick(old, p)[:20] and len(pick(log, p)) == 20, p
def kv(line):
    out = {}
    for k, v in re.findall(r'(\w+)=((?:\[[^=]*?\](?=\s|$))|\S+)', line):
        try: out[k] = ast.literal_eval(v)
        except Exception: out[k] = {'true': True, 'false': False}.get(v, v)
    return out
struct = kv(pick(log, 'Z6_STRUCT ')[0])
prep = [kv(l) for l in pick(log, 'Z6_PREP ')]
assert len(prep) == 200
assert all(p['helper_nonzero_inactive_rows'] == 0 and p['balance_changes_row1023_columns'] == list(range(16))
           and p['balance_changes_other_rows'] is False and p['lean_A_equals_z4c_trace'] is True for p in prep)
ab = [kv(l) for l in pick(log, 'Z6_AB ')]
ac = [kv(l) for l in pick(log, 'Z6_AC ')]
pad = [kv(l) for l in pick(log, 'Z6_APAD ')]
assert len(ab) == 1000 and len(ac) == 200 and len(pad) == 1000
Z = [0, 0, 0, 0]
for r in ab + ac:
    assert r['diff_count'] == 0 and r['rows'] == [] and r['sum_diff'] == Z and r['hash_a'] == r['hash_b'], r
for r in pad:
    assert r['diff_equals_mu_plus_mu2_times_pad'] is True and r['sum_diff'] == Z
totals = sorted({str(r['sum_a']) for r in ab + ac} | {str(r['sum_b']) for r in ab + ac})
assert totals == [str(Z)]
classes = [l for l in log if l.startswith('Z6_CELL_CLASS ')]
cells = [kv(l) for l in pick(log, 'Z6_CELL c=')]
assert all(c['honest_trial0'] == c['random_trial0'] == c['random_trial1'] == [] for c in cells)
assert classes == ['Z6_CELL_CLASS eligible honest=[]_rel random=[]_rel count=3787',
                   'Z6_CELL_CLASS row1023 honest=[]_rel random=[]_rel count=16'], classes
full_a = ast.literal_eval(pick(log, 'Z6_FULL_A ')[0].split('values=', 1)[1])
assert len(full_a) == 1024
tapes = [kv(l) for l in pick(log, 'Z6_TAPE ')]
summary = dict(
    question='Z6: original terminal at every Boolean row under eligible noise',
    replay='20/20 TRIAL_SEED and CHALLENGE lines identical to probe-C.log',
    structure={k: struct[k] for k in struct},
    prep=dict(records=200, helper_zero_on_all_810_inactive_rows=True,
              balance_rewrites_row1023_in_all_16_columns=True, balance_touches_no_other_row=True,
              lean_A_equals_z4c_balanced_trace=True),
    A_vs_C=[dict(trial=r['trial'], witness=r['witness'], diff_count=r['diff_count'], sum_A=r['sum_b'], sum_C=r['sum_a'], hash=r['hash_a']) for r in ac],
    B_vs_A=[dict(trial=r['trial'], witness=r['witness'], tape=r['tape'], own_pair=r['own_pair'], diff_count=r['diff_count'],
                 sum_A=r['sum_a'], sum_B=r['sum_b'], sum_diff=r['sum_diff'], hash_A=r['hash_a'], hash_B=r['hash_b']) for r in ab],
    h1_padding_supplement=[dict(trial=r['trial'], witness=r['witness'], tape=r['tape'], diff_count=r['diff_count'],
                                hist_mod16=r['hist_mod16'], sum_diff=r['sum_diff'], diff_equals_mu_plus_mu2_times_pad=True) for r in pad],
    tapes=tapes,
    cell_dependence=dict(classes=classes, row1023=cells, deltas=2,
                         bases=['honest witness 0, trial-0 prefix', 'uniform M31 trace, trial-0 prefix', 'uniform M31 trace, trial-1 prefix']),
    full_A_trial0_witness0=full_a,
    full_A_nonzero_rows_trial0_witness0=[i for i, v in enumerate(full_a) if v != Z],
)
(here / 'summary-Z6.json').write_text(json.dumps(summary, separators=(',', ':')) + '\n')
# evidence
runs = []
for name in ('preflight1', 'preflight2', 'full'):
    e = json.loads((here / 'z6-runs' / name / 'evidence.json').read_text())
    tv = (here / 'z6-runs' / name / 'time-v.txt').read_text()
    g = lambda pat: re.search(pat, tv).group(1)
    runs.append(dict(attempt=name, unit=f'aspis-z6-{"preflight" if name == "preflight1" else name}', scope=e['scope'], caps=e['caps'],
                     receipts=e['receipts'], outer_time_v=dict(wall=g(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (\S+)'),
                     max_rss_kib=int(g(r'Maximum resident set size \(kbytes\): (\d+)')), exit=int(g(r'Exit status: (\d+)'))),
                     source_sha256=e['source_sha256']))
final = runs[-1]['source_sha256']
for f, d in final.items():
    assert hashlib.sha256((root / f).read_bytes()).hexdigest() == d, f
decision = {}
for f in ['docs/research/v8-r0-zk-20261009/lean/R0Z/MaskLayout.lean', 'docs/research/v8-r0-zk-20261009/lean/R0Z/HonestView.lean',
          'docs/research/v8-r0-zk-20261009/lean/R0Z/PayloadSplit.lean', 'docs/research/v8-r0-sem-proof-20261008/lean/R0P/SemDecision.lean',
          'docs/research/v8-r0-sem-proof-20261008/lean/R0P/Core.lean', 'docs/research/v8-r0-zk-20261009/LOG.md',
          'docs/research/v8-r0-zk-20261009/z4/summarize-z6.py']:
    decision[f] = hashlib.sha256((root / f).read_bytes()).hexdigest()
evidence = dict(base_revision=json.loads((here / 'z6-runs/full/evidence.json').read_text())['base_revision'],
                rustc=json.loads((here / 'z6-runs/full/evidence.json').read_text())['rustc'],
                host='dombarker@100.108.41.90', staging='/home/dombarker/project-offloads/aspis-z6-20261011/',
                build_cache='copied from aspis-z5-20261010 z4/target (read-only source)',
                concurrent_aspis_scopes_at_launch=0, reserved_MemoryMax_GiB=4,
                runs=[{k: v for k, v in r.items() if k != 'source_sha256'} for r in runs],
                compiled_source_count=len(final), final_source_sha256=final,
                failed_attempt='preflight1: assertion `eligible cell on a copy-active row c=2 r=1015` (an over-strong probe assertion, exit 101); replaced by reporting the 221 such cells',
                decision_source_sha256=decision, axioms_audit='Not applicable: no Lean executed', lean_or_production_changed=False)
(here / 'evidence-Z6.json').write_text(json.dumps(evidence, indent=1) + '\n')
print('Z6 audit OK: replay 20/20; B=A on 1000/1000 (witness,tape,prefix) at all 1024 rows; A=C 200/200; all totals 0; 3803 cells no dependence')
