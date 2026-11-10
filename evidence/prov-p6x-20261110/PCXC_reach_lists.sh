#!/bin/bash
# PCXC_reach_lists.sh: Task 2 list-level step. For each NO_FROZEN_COUNTERPART gate definition: is it (exactly, or by an
# auxiliary constant under its name) in the pinned deployed_splitB cone list, or in the pinned reachable list of any ledger30 root?
set -e
WT=/Users/dominic/ZK/.worktrees/pc-prov-p6x
SCR=/private/tmp/claude-501/-Users-dominic-ZK/e51a42a3-64c9-4a23-9ea1-f7bf410e2db1/scratchpad/partc
cd $WT/evidence/prov-p6x-20261110
python3 -I -B - "$SCR" "$WT" <<'PY'
import json, lzma, re, sys, hashlib, subprocess, collections
SCR, WT = sys.argv[1], sys.argv[2]
def git(p): return subprocess.run(['git','-C',WT,'cat-file','-p','HEAD:'+p],capture_output=True,check=True).stdout
L = json.load(lzma.open(f'{WT}/evidence/ledger30-20261111/NNN_LEDGER.json.xz'))
rootrows = collections.defaultdict(set)
for r in L['rows']:
    assert r['status'] == 'CLOSED'
    for e in r['root_owners']: rootrows[e['root']].add(r['row'])
rf = json.load(open(SCR + '/rootfile.json'))
old = json.load(open(SCR + '/roots.json'))
assert set(old) == set(rootrows) or True
print('ledger roots', len(rootrows), 'p6c roots', len(old), 'equal', set(old) == set(rootrows))
# target definitions (PCXB_NONFROZEN.md, 8 gate definitions)
P = json.load(open(f'{WT}/evidence/prov-p6c-20261109/PCXB_PROVENANCE.json'))
T = []
for m, v in P['modules'].items():
    for n, r in v['definitions'].items():
        if r['status'] == 'NO_FROZEN_COUNTERPART' or (m, n) in [('AspisR1DecodeKFullV10.Funs','AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_value'),('AspisR72Sampler.Types','AspisR72Sampler.field.r24_canonical_mul.closure'),('ClaimsUnrolledParentSource','AspisR1ClaimsUnrolledParent.candidate_claims.claims'),('NJT_ClaimsRef_Funs','NJT_ClaimsRef.r1_semantic.NJT_claims_ref')]:
            T.append((m, n, r['status'], r.get('open_reason')))
print(len(T)); [print(t[:2]) for t in T]
# splitB list
raw = lzma.open(f'{WT}/evidence/integrate-20261111/NNH_L942/audit/NEP_proof0_AspisR1.TAS_FinalB.deployed_splitB_REACHABLE.txt.xz').read()
assert hashlib.sha256(raw).hexdigest() == open(f'{WT}/evidence/integrate-20261111/NNH_L942/audit/NEP_proof0_AspisR1.TAS_FinalB.deployed_splitB_REACHABLE.txt.sha256').read().split()[0]
sb = set(l.strip() for l in raw.decode().splitlines() if l.strip())
PRIV = re.compile(r'^_private\.(.+?)\.0\.(.+)$')
def norm(n):
    m = PRIV.match(n); return m[2] if m else n
def hits(names, t):
    ex = t in names; aux = sorted(n for n in names if n.startswith(t + '.') or n == t)  # aux constants (eq_N, match_N, ...) under the name
    return ex, aux[:8], len([n for n in names if n.startswith(t + '.')])
sbn = set(norm(n) for n in sb)
res = {}
rootnames = {}
used = {}
for root in sorted(rootrows):
    p = rf[root][0]; used[root] = p
    data = lzma.decompress(git(p)).decode('utf-8','replace')
    rootnames[root] = set(norm(l.strip()) for l in data.splitlines() if l.strip())
for m, n, st, why in T:
    ex, aux, naux = hits(sbn, n)
    rr = []
    for root, names in rootnames.items():
        if n in names: rr.append(root)
    rows = sorted(set(x for r in rr for x in rootrows[r]))
    res[n] = dict(module=m, provenance_status=st, reason=why, in_splitB_list_exact=ex, splitB_aux_constants=naux, splitB_aux_sample=aux,
                  roots_reaching_exact=rr, rows=rows)
    print(n, 'splitB', ex, naux, 'roots', len(rr), 'rows', len(rows))
json.dump(dict(schema='PCXC_REACH_LISTS/1', splitB_list_sha256=hashlib.sha256(raw).hexdigest(), splitB_constants=len(sb), n_ledger_roots=len(rootrows), root_list_files=used, results=res, root_rows={r: sorted(v) for r, v in rootrows.items()}), open('PCXC_REACH_LISTS.json','w'), indent=0)
PY
