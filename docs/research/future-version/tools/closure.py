import os, re, sys, json
src = sys.argv[1]
roots = sys.argv[2:]
imp = re.compile(r'^import\s+(\S+)', re.M)
files = {f[:-5] for f in os.listdir(src) if f.endswith('.lean')}
def imports(m):
    p = os.path.join(src, m + '.lean')
    if not os.path.exists(p): return []
    txt = open(p, errors='replace').read()
    return imp.findall(txt)
seen = {}
stack = list(roots)
while stack:
    m = stack.pop()
    if m in seen: continue
    seen[m] = imports(m)
    for d in seen[m]:
        if d not in seen: stack.append(d)
local = {m for m in seen if m in files}
ext = {m for m in seen if m not in files}
print(json.dumps({"local": sorted(local), "external_roots": sorted({e.split('.')[0] for e in ext})}))
