"""Second pass of PIN2W6_nonjf_scan for modules whose release source is not a
unique blob: scan EVERY research candidate blob of the module name (a module is
flagged if any candidate carries a 26 October native limb or 1455/1530).
usage: python3 -I PIN2W6_nonjf_scan2.py <NONJF-SCAN.json> <out.json>"""
import sys, json, re, collections, subprocess
W = '/Users/dominic/ZK/.worktrees/pin2-lean'
EV = W + '/docs/research/100bit-spend-path-20261013/evidence'
D = json.load(open(EV + '/pin2-w5-20261111/provenance-26oct/DERIVED-26OCT.json'))
where = {limb for st in ('tx1', 'tx2') for t, v in D[st].items() for x in v.values() for limb in x if limb >= 1 << 16} - {2147483647, 2147483648, 4294967295, 4294967296}
idx = collections.defaultdict(set)
for l in open('/private/tmp/claude-501/-Users-dominic-ZK/3db59790-41f3-4c53-ae90-3fc42a8cab96/scratchpad/w6/research-lean.tsv'):
    b, p = l.rstrip('\n').split('\t'); idx[p.rsplit('/', 1)[-1][:-5]].add(b)
mods = json.load(open(sys.argv[1]))['no_source']
blobs = sorted({b for m in mods for b in idx.get(m, ())})
p = subprocess.Popen(['git', '-C', W, 'cat-file', '--batch'], stdin=subprocess.PIPE, stdout=subprocess.PIPE)
text = {}
for b in blobs:
    p.stdin.write((b + '\n').encode()); p.stdin.flush()
    hdr = p.stdout.readline().split(); n = int(hdr[2]); text[b] = p.stdout.read(n).decode(errors='replace'); p.stdout.read(1)
out = {}; none = []
for m in mods:
    if not idx.get(m): none.append(m); continue
    hits = []
    for b in idx[m]:
        s = re.sub(r'--.*', '', text[b])
        nat = {int(n) for n in re.findall(r'(?<![\w.])\d{5,}(?![\w.])', s)} & where
        lens = set(re.findall(r'(?<![\w.])(1455|1530)(?![\w.])', s))
        if nat or lens: hits.append(dict(blob=b, native=sorted(nat)[:8], lengths=sorted(lens)))
    if hits: out[m] = dict(candidates=len(idx[m]), hits=hits)
print('modules', len(mods), 'candidate blobs', len(blobs), 'no candidate on research', len(none), 'flagged', len(out))
for m, r in sorted(out.items()): print(' ', m, r['candidates'], [(h['blob'][:10], h['lengths'], h['native'][:3]) for h in r['hits']])
json.dump(dict(flagged=out, no_candidate=none), open(sys.argv[2], 'w'), indent=1)
