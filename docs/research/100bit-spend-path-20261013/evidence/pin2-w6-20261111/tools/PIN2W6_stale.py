"""Step 1: which overlay-PIN2-W4 objects are stale against the clash-fixed
PIN2_NEWGATE_r0 (overlay-PIN2)?  A W4 object is stale when the effective
import closure contains PIN2_NEWGATE_r0 or PIN2_NEWGATE_r1_semantic, or when
any direct import's effective object is newer than the W4 object.
usage: python3 -I PIN2W6_stale.py <scan_dir> <out.json>"""
import sys, os, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import PIN2W6_graph as G
G.load(sys.argv[1])
roots = ['PIN2_NEWGATE_r0', 'PIN2_NEWGATE_r1_semantic']
w4 = sorted(m for m, L in G.layer.items() if L == 'overlay-PIN2-W4')
out = []
for m in w4:
    cl = G.closure(m)
    hit = [r for r in roots if r in cl]
    mt = os.path.getmtime(G.path(m))
    newer = [d for d in G.imp[m] if G.path(d) and os.path.getmtime(G.path(d)) > mt]
    out.append(dict(module=m, r0_in_closure=hit, newer_direct_imports=newer,
                    overlay_imports=[d for d in cl if G.layer.get(d) in ('overlay-PIN2', 'overlay-PIN2-W4')].__len__()))
st = [o for o in out if o['r0_in_closure'] or o['newer_direct_imports']]
print('W4 objects', len(w4), 'stale', len(st), 'via r0', sum(1 for o in out if o['r0_in_closure']), 'via mtime', sum(1 for o in out if o['newer_direct_imports']))
json.dump(dict(objects=len(w4), stale=[o['module'] for o in st], detail=out), open(sys.argv[2], 'w'), indent=1)
