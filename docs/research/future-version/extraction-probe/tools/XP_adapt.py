#!/usr/bin/env python3
"""Aspis extraction probe: turn one Aeneas emission (four files in a sub-directory, module-system headers) into four flat
Lean modules that fv_lean.sh can compile one at a time against the R1 (L187) objects.
Text changes, all of them naming or header changes, none touching a definition body unless listed in RULES:
  * header: `module`, `public import`, `@[expose] public section` -> plain `import`; sub-directory imports -> flat names;
  * the two *_Template files are used as they are (their axioms stand for the opaque and external items);
  * RULES (optional JSON list of [regex, replacement, reason]) for library spelling differences found by compiling.
usage: XP_adapt.py <raw dir> <namespace> <flat prefix> <out dir> [rules.json]"""
import json, re, sys, hashlib
from pathlib import Path
raw, ns, pre, out = Path(sys.argv[1]), sys.argv[2], sys.argv[3], Path(sys.argv[4])
rules = json.loads(Path(sys.argv[5]).read_text()) if len(sys.argv) > 5 else []
out.mkdir(parents=True, exist_ok=True)
names = {'TypesExternal_Template.lean': 'TypesExternal', 'Types.lean': 'Types', 'FunsExternal_Template.lean': 'FunsExternal', 'Funs.lean': 'Funs'}
rep = {}
for f, n in names.items():
    p = raw / f
    if not p.exists(): continue
    t = p.read_text(); src_sha = hashlib.sha256(t.encode()).hexdigest()
    t = re.sub(r'(?m)^module\n', '', t)
    t = re.sub(r'(?m)^public import ', 'import ', t)
    t = re.sub(r'(?m)^@\[expose\] public section\n', '', t)
    t = re.sub(r'(?m)^import %s\.(\w+)$' % re.escape(ns), lambda m: 'import %s%s' % (pre, m.group(1)), t)
    used = []
    for i, (pat, repl, why) in enumerate(rules):
        t2 = re.sub(pat, repl, t)
        if t2 != t: used.append(i)
        t = t2
    t = '-- Aspis extraction probe: adapted copy of %s (raw sha256 %s); see XP_adapt.py\n' % (f, src_sha) + t
    (out / (pre + n + '.lean')).write_text(t)
    rep[pre + n] = dict(raw=f, raw_sha256=src_sha, rules_used=used, sha256=hashlib.sha256(t.encode()).hexdigest())
print(json.dumps(rep, indent=1))
