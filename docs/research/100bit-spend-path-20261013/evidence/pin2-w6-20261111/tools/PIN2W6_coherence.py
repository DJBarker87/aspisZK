"""mtime/sha coherence check over the effective LEAN_PATH graph.
For targets T: every overlay object x in T and in closure(T) must be newer
than each direct import's effective object; a release object (objs/base) in
the closure that imports an overlay object is reported as shadow-stale.
usage: python3 -I PIN2W6_coherence.py <scan_dir> <out.json> [Module ...|--w4]"""
import sys, os, json, hashlib
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import PIN2W6_graph as G
G.load(sys.argv[1])
T = sys.argv[3:]
if T == ['--w4']: T = sorted(m for m, L in G.layer.items() if L == 'overlay-PIN2-W4')
allm = set(T)
for t in T: allm |= G.closure(t)
OV = ('overlay-PIN2', 'overlay-PIN2-W4', 'overlay-HOST-P1')
MT = ('overlay-PIN2', 'overlay-PIN2-W4')   # mtime order is checked for locally built layers;
# overlay-HOST-P1 holds host-built copies (host receipts, copy mtimes) and is checked only
# as an import target: a local object must be newer than every HOST-P1 import.
bad, shadow, same = [], [], []
for x in sorted(allm):
    px = G.path(x)
    if px is None: bad.append((x, 'no object')); continue
    L = G.layer.get(x, 'base')
    if L in MT:
        mt = os.path.getmtime(px)
        for d in G.imp.get(x, []):
            pd = G.path(d)
            if pd and os.path.getmtime(pd) > mt:
                # a HOST-P1 copy byte-identical to the release object the importer was built
                # against is a copy-mtime artifact, recorded separately, not an incoherence
                rp = f'{G.C}/objs/{d.replace(".", "/")}.olean'
                if G.layer.get(d) == 'overlay-HOST-P1' and os.path.isfile(rp) and open(rp, 'rb').read() == open(pd, 'rb').read():
                    same.append((x, d))
                else: bad.append((x, 'older than import ' + d))
    elif L not in OV:
        ovi = [d for d in G.imp.get(x, []) if G.layer.get(d) in OV]
        if ovi: shadow.append((x, ovi[:3]))
rows = {}
for t in T:
    p = G.path(t)
    rows[t] = dict(layer=G.layer.get(t, 'base'), olean_sha256=hashlib.sha256(open(p, 'rb').read()).hexdigest() if p else None)
print('targets', len(T), 'closure', len(allm), 'incoherent overlay objects', len(bad), 'shadow-stale release objects', len(shadow), 'older-than-identical-HOST-P1-copy', len(same))
for b in bad[:20]: print('  INCOHERENT', *b)
for s in shadow[:20]: print('  SHADOW', *s)
json.dump(dict(targets=len(T), closure=len(allm), incoherent=bad, older_than_identical_host_copy=same, shadow_stale=shadow, objects=rows), open(sys.argv[2], 'w'), indent=1)
