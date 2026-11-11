# usage: python3 -I resolve.py <tree.txt> <outdir> Module...
# writes the release source of each module whose basename path has exactly one distinct blob
import sys, subprocess, os, collections
tree, out = sys.argv[1], sys.argv[2]
by = collections.defaultdict(dict)
for line in open(tree):
    meta, path = line.rstrip('\n').split('\t')
    blob = meta.split()[2]
    by[path.split('/')[-1]].setdefault(blob, []).append(path)
for m in sys.argv[3:]:
    rel = m.replace('.', '/') + '.lean'
    cands = {b: [p for p in ps if p == rel or p.endswith('/' + rel)] for b, ps in by[rel.split('/')[-1]].items()}
    cands = {b: ps for b, ps in cands.items() if ps}
    if len(cands) == 1:
        b, ps = next(iter(cands.items()))
        dst = os.path.join(out, rel); os.makedirs(os.path.dirname(dst), exist_ok=True)
        open(dst, 'wb').write(subprocess.run(['git', 'cat-file', '-p', b], capture_output=True, check=True).stdout)
        print(f"{rel}\t{ps[0]}\t{b}\tdistinct_blobs=1")
    else:
        print(f"{rel}\tAMBIGUOUS\t{' '.join(cands)}\tdistinct_blobs={len(cands)}")
