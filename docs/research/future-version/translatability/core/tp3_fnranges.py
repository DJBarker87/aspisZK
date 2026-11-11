import sys, re, hashlib
def ranges(path, names):
    lines = open(path).read().split('\n'); out = {}
    for n in names:
        pat = re.compile(r'^(\s*)(pub(\([a-z]+\))? )?(const )?fn %s\b' % re.escape(n))
        hits = [i for i, l in enumerate(lines) if pat.match(l)]
        if not hits: out[n] = None; continue
        i = hits[0]; ind = pat.match(lines[i]).group(1)
        # include preceding attribute lines
        s = i
        while s > 0 and lines[s-1].strip().startswith('#['): s -= 1
        j = i
        while not (lines[j].startswith(ind + '}') and len(lines[j].rstrip()) == len(ind) + 1): j += 1
        body = '\n'.join(lines[s:j+1]) + '\n'
        out[n] = (s + 1, j + 1, hashlib.sha256(body.encode()).hexdigest())
    return out
old, new = sys.argv[1], sys.argv[2]; names = sys.argv[3].split(',')
a, b = ranges(old, names), ranges(new, names)
for n in names:
    print('\t'.join([n, str(a[n][:2]) if a[n] else '-', a[n][2] if a[n] else '-', str(b[n][:2]) if b[n] else '-', b[n][2] if b[n] else '-']))
