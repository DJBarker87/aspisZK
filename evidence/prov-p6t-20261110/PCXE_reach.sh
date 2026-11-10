#!/bin/bash
# PCXE_reach.sh: map the constant cone of AspisR1.TAS_FinalB.deployed_splitB (146370 constants, ledger30-style pinned
# walker output NNH_L942, sha256 verified) to emitted gate modules, with the SAME ownership rule as PCO_partition.py stage_hits
# (strong_names intersection over the module's candidate sources; private-name handling; longest-prefix fallback).
set -e
SCR=/private/tmp/claude-501/-Users-dominic-ZK/e51a42a3-64c9-4a23-9ea1-f7bf410e2db1/scratchpad/partE
cd /Users/dominic/ZK/.worktrees/pc-prov-p6t/evidence
python3 -I - "$SCR" <<'PY'
import json, lzma, re, sys, hashlib, collections
S = sys.argv[1]
raw = lzma.open('integrate-20261111/NNH_L942/audit/NEP_proof0_AspisR1.TAS_FinalB.deployed_splitB_REACHABLE.txt.xz').read()
want = open('integrate-20261111/NNH_L942/audit/NEP_proof0_AspisR1.TAS_FinalB.deployed_splitB_REACHABLE.txt.sha256').read().split()[0]
assert hashlib.sha256(raw).hexdigest() == want, 'reachable list sha mismatch'
names_in_cone = [l.strip() for l in raw.decode().splitlines() if l.strip()]
em = json.load(open(f'{S}/emods_decl.json'))
n2 = collections.defaultdict(set)
for m, v in em.items():
    for n in v['strong_names']: n2[n].add(m)
PRIV = re.compile(r'^_private\.(.+?)\.0\.(.+)$')
hit = collections.defaultdict(set)
for n in names_in_cone:
    pm = PRIV.match(n)
    if pm:
        if pm[1] in em: hit[pm[1]].add(pm[2])
        n = pm[2]
    if n in n2:
        for m in n2[n]: hit[m].add(n)
        continue
    parts = n.split('.')
    for i in range(len(parts) - 1, 1, -1):
        p = '.'.join(parts[:i])
        if p in n2:
            for m in n2[p]: hit[m].add(p)
            break
out = dict(schema='PCXE_SPLITB_HITS/1', root='AspisR1.TAS_FinalB.deployed_splitB', reachable_list_sha256=want, n_constants=len(names_in_cone),
           walker='ledger30 NNM_ProofDriver sha256 46ee271b392729449147b978830b474e3fa4ecba2b45e03ad13c02490ba6ca3c (NNH_L942, reused: same binary, same root, pinned list hash verified)',
           ownership_rule='PCO_partition.py stage_hits (strong_names per emitted module, private-name handling, longest prefix); 6ce07a6a593 base',
           modules={m: sorted(v) for m, v in sorted(hit.items())})
json.dump(out, open('prov-p6t-20261110/PCXE_SPLITB_HITS.json', 'w'), indent=0)
print('emitted modules in splitB cone:', len(hit), 'distinct reached names', sum(len(v) for v in hit.values()))
PY
