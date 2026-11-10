#!/bin/bash
# PCXC_nofrozen_reach.sh: PCXC_NOFROZEN_REACH.json and .md from PCXC_REACH_LISTS.json (list level) and the walker logs PCXC_L006 (splitB, NHS, NKA on the NNH_L939 chain) and PCXC_L007 (NHS, NKA on the ledger30 NNN chain).
cd "$(dirname "$0")"
python3 -I -B - <<'PY'
import json, lzma, re, os
def log(a):
    p = f'{a}/stdout.log'
    return open(p).read() if os.path.exists(p) else lzma.open(p + '.xz').read().decode()
def parse(t):
    res = {}; tot = {}
    for m in re.finditer(r'^PCXC_REACHABLE_TOTAL (\S+) (\d+) nodes_without_adjacency (\d+)', t, re.M): tot[m[1]] = dict(reached=int(m[2]), nodes_without_adjacency=int(m[3]))
    for m in re.finditer(r'^PCXC_TARGET (\S+) (REACHED_FROM|NOT_REACHED_FROM) (\S+)(?: hops=(\d+) theorem_nodes_on_path=(\d+))?', t, re.M):
        res[(m[1], m[3])] = dict(reached=m[2] == 'REACHED_FROM', hops=int(m[4]) if m[4] else None, theorem_nodes_on_path=int(m[5]) if m[5] else None)
    for m in re.finditer(r'^PCXC_PATH (\S+) :: (\S+) :: (.*)$', t, re.M): res[(m[1], m[2])]['path'] = m[3].split(', ')
    return res, tot
r6, t6 = parse(log('PCXC_L006')); r7, t7 = parse(log('PCXC_L007'))
L = json.load(open('PCXC_REACH_LISTS.json'))
SB = 'AspisR1.TAS_FinalB.deployed_splitB'
out = []
for n, v in L['results'].items():
    roots = v['roots_reaching_exact']
    wit = {}
    for r in ['AspisR1.NHS_CheckpointPacket.source', 'AspisR1.NKA_ClaimsRoot.claims']:
        w = r7.get((n, r))
        if w and w['reached']: wit[r] = dict(source='PCXC_L007 (ledger30 gate chain)', hops=w['hops'], theorem_nodes_on_path=w['theorem_nodes_on_path'], path=w['path'])
    sb = r6[(n, SB)]
    out.append(dict(definition=n, module=v['module'], provenance_status=v['provenance_status'],
        reachable_from_deployed_splitB=sb['reached'], splitB_in_pinned_list=v['in_splitB_list_exact'],
        splitB_witness=dict(source='PCXC_L006 (NNH_L939 chain)', hops=sb['hops'], theorem_nodes_on_path=sb['theorem_nodes_on_path'], path=sb['path']) if sb['reached'] else None,
        reachable_from_a_CLOSED_row_root=bool(roots), n_roots_reaching=len(roots), roots_reaching=roots, n_rows=len(v['rows']), rows=v['rows'], closed_root_witnesses=wit))
reach = [o for o in out if o['reachable_from_deployed_splitB'] or o['reachable_from_a_CLOSED_row_root']]
J = dict(schema='PCXC_NOFROZEN_REACH/1', target_established=False, task='Task 2 of PCXC_: reachability of the 8 NO_FROZEN_COUNTERPART gate definitions (PCXB_NONFROZEN.md)',
    method=dict(
      list_level='Name membership in the pinned reachable-constant lists: deployed_splitB = evidence/integrate-20261111/NNH_L942 (146370 constants, sha256 0b316cbb...); each of the 1099 ledger30 root constants = its pinned REACHABLE list (the list file chosen as in PCXB: evidence/ledger29-20261111/NNM_raw, PCXC_REACH_LISTS.json root_list_files). Rows = rows of ledger30 (NNN_LEDGER.json.xz, 599 rows, all CLOSED) whose root_owners name the root.',
      witness='Breadth-first search with parent pointers over the .olean files themselves (PCXC_ConeWalk.lean, scopes PCXC_L006 and PCXC_L007): edge u->v when v occurs in the type or in the value of u (PCWD_ReachMeta2 edge relation). Witnesses are shortest paths of constants; [thm]/[def] mark the constant kind.',
      walker_vs_pinned={SB: dict(pinned_list=146370, walker_reached=t6[SB]['reached']), 'AspisR1.NHS_CheckpointPacket.source': dict(pinned_list=28064, walker_reached=t6['AspisR1.NHS_CheckpointPacket.source']['reached']), 'AspisR1.NKA_ClaimsRoot.claims': dict(pinned_list=9862, walker_reached=t6['AspisR1.NKA_ClaimsRoot.claims']['reached'])},
      walker_difference='The walker relation reaches 0.25 to 1.3 percent fewer constants than the pinned lists (the pinned NNM_ProofDriver also follows kernel-level auxiliary edges that the type/value relation does not). Every one of the 8 definitions is in the pinned list of deployed_splitB and the walker independently reaches it, so the verdict does not depend on the difference.',
      cannot_see=['Constant-level reachability is not semantic use: a definition that occurs in the cone may sit only inside a theorem statement, an unused branch, a dead binding, a type-level mention or a proof term that never computes with it. The check does not decide which.',
                  'It does not decide whether the Rust function this definition models runs in the deployed ELF; for gate-only helpers there is no frozen function to compare with.',
                  'Only 2 of the 1099 ledger roots were walked on the .olean objects (NHS_CheckpointPacket.source and NKA_ClaimsRoot.claims, which between them cover all 8 definitions apart from the splitB root); the other root attributions are list-level (pinned lists from ledger29, not re-derived on the ledger30 objects).',
                  'Pinned lists for ledger roots come from ledger29 NNM_raw; ledger30 re-audited only 4 other roots (NNN_raw), so a drift of a root list between ledger29 and ledger30 is not excluded; the walker runs on the ledger30 gate (PCXC_L007) agree with the lists for the two walked roots.']),
    summary=dict(definitions=len(out), reachable_from_splitB=sum(o['reachable_from_deployed_splitB'] for o in out), reachable_from_a_closed_row_root=sum(o['reachable_from_a_CLOSED_row_root'] for o in out), reachable_from_neither=len(out) - len(reach)),
    definitions=reach + [o for o in out if o not in reach])
json.dump(J, open('PCXC_NOFROZEN_REACH.json', 'w'), indent=1)
md = ['# PCXC_NOFROZEN_REACH: do the 8 gate-only definitions reach the headline or the closed rows?', '',
 'Target not yet established. Constant-level reachability only; this does not show that anything is semantically used (limits at the end).', '',
 f'All 8 definitions that have no counterpart in the frozen Rust source are reachable from the headline theorem AspisR1.TAS_FinalB.deployed_splitB, and every one of them is also reachable from at least one closed-row root. None is unreachable.', '',
 '| definition | from deployed_splitB | closed-row roots | rows | shortest witness from deployed_splitB (hops, theorem nodes) |', '|---|---|---|---|---|']
for o in reach:
    w = o['splitB_witness']
    md.append(f"| `{o['definition']}` | yes | {o['n_roots_reaching']} | {o['n_rows']} | {w['hops']} hops, {w['theorem_nodes_on_path']} theorem nodes |")
md += ['', '## What each one is and where it is reached', '']
for o in reach:
    w = o['splitB_witness']
    md += [f"### `{o['definition']}`", f"Module {o['module']}, provenance status {o['provenance_status']}.", '',
           f"From deployed_splitB ({w['hops']} hops): " + ' -> '.join(w['path']), '']
    for r, c in o['closed_root_witnesses'].items():
        md.append(f"From closed-row root `{r}` ({c['hops']} hops): " + ' -> '.join(c['path'])); md.append('')
    md.append(f"Closed-row roots reaching it: {o['n_roots_reaching']}; rows: {', '.join(o['rows'])}."); md.append('')
    md.append('Root names: see PCXC_NOFROZEN_REACH.json (roots_reaching).'); md.append('')
md += ['## What this check cannot see', '']
md += ['* ' + x for x in J['method']['cannot_see']]
md += ['', 'Method and files: PCXC_NOFROZEN_REACH.json (full data), PCXC_REACH_LISTS.json (list level), PCXC_L006 and PCXC_L007 (walker scopes), PCXC_ConeWalk.lean.in (walker source).', '']
open('PCXC_NOFROZEN_REACH.md', 'w').write('\n'.join(md))
print(json.dumps(J['summary']), json.dumps(J['method']['walker_vs_pinned']))
PY
