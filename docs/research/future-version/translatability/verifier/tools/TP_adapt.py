#!/usr/bin/env python3
"""Aspis extraction probe: turn one Aeneas emission (four files in a sub-directory, module-system headers) into four flat
Lean modules that fv_lean.sh can compile one at a time against the R1 (L187) objects.
Text changes, all of them naming or header changes, none touching a definition body unless listed in RULES:
  * header: `module`, `public import`, `@[expose] public section` -> plain `import`; sub-directory imports -> flat names;
  * the two *_Template files are used as they are (their axioms stand for the opaque and external items);
  * RULES (optional JSON list of [regex, replacement, reason] or [regex, replacement, reason, [modules]]) for library
    spelling differences found by compiling; a rule with a module list applies only to those of TypesExternal, Types,
    FunsExternal, Funs.
usage: XP_adapt.py <raw dir> <namespace> <flat prefix> <out dir> [rules.json]"""
import json, re, sys, hashlib
from pathlib import Path
raw, ns, pre, out = Path(sys.argv[1]), sys.argv[2], sys.argv[3], Path(sys.argv[4])
rules = json.loads(Path(sys.argv[5]).read_text()) if len(sys.argv) > 5 else []
out.mkdir(parents=True, exist_ok=True)
ATOM = re.compile(r'^[A-Za-z_«][\w.«»\']*$|^\d+#\w+$|^\(\)$')
KEYWORD = re.compile(r'^(if|then|else|let|match|do|with|massert|fun|termination_by|decreasing_by|partial_fixpoint|end|namespace|def|\|)\b|^\|')
def join_broken(text):
    """The emitter formats with a margin of 80 columns (Translate.ml: Format.pp_set_margin fmt 80; no option changes
    it). In deeply nested code its indentation reaches the limit and it then puts the function and each argument of an
    application on lines of their own AT ONE COLUMN. Lean reads lines at one column as separate statements. This step
    joins them: where an expression starts (after a line ending in `←`, `:=` or `=>`, or after `then` / `else`), a
    line that is a single name, followed at the same indentation by one or more arguments (a name, a literal, `()`, or
    a parenthesised group, taken to its closing parenthesis), becomes one line. Nothing else is touched."""
    L = text.split('\n'); out = []; i = 0
    def ind(s): return len(s) - len(s.lstrip())
    while i < len(L):
        line = L[i]; s = line.strip(); prev = out[-1].strip() if out else ''
        starts = prev.endswith('←') or prev.endswith(':=') or prev.endswith('=>') or prev in ('then', 'else')
        if starts and ATOM.match(s) and not KEYWORD.match(s):
            k = ind(line); j = i + 1; parts = [s]
            while j < len(L) and L[j].strip() and ind(L[j]) == k and not KEYWORD.match(L[j].strip()):
                a = L[j].strip()
                if ATOM.match(a):
                    parts.append(a); j += 1
                elif a.startswith('('):
                    grp = [a]; depth = a.count('(') - a.count(')'); j += 1
                    while depth > 0 and j < len(L):
                        grp.append(L[j].strip()); depth += L[j].count('(') - L[j].count(')'); j += 1
                    parts.append(' '.join(grp))
                else:
                    break
            if len(parts) >= 2:
                out.append(' ' * k + ' '.join(parts)); i = j; continue
        out.append(line); i += 1
    return '\n'.join(out)
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
    for i, rule in enumerate(rules):
        pat, repl, why = rule[:3]
        if len(rule) > 3 and n not in rule[3]: continue   # a rule may name the modules it applies to
        if pat == '@join-broken-applications':
            t2 = join_broken(t)
            if t2 != t: used.append(i)
            t = t2; continue
        t2 = re.sub(pat, repl.replace('NAMESPACE', ns), t)
        if t2 != t: used.append(i)
        t = t2
    t = '-- Aspis extraction probe: adapted copy of %s (raw sha256 %s); see XP_adapt.py\n' % (f, src_sha) + t
    (out / (pre + n + '.lean')).write_text(t)
    rep[pre + n] = dict(raw=f, raw_sha256=src_sha, rules_used=used, sha256=hashlib.sha256(t.encode()).hexdigest())
print(json.dumps(rep, indent=1))
