#!/usr/bin/env python3
"""X7 gate (v): read before write and write order, on the raw Funs.lean of one program. X2c's checks (b) and (c) of
fv_x2c_emission_checks.py, with several boundary names (the verifier program has two) and a reference emission.
(b) read before write (conservative, textual): a definition is "reading" if it calls a read external of the config
    (`AccountInfo.try_borrow_data`, ...) or a reading definition, "writing" if it calls a write boundary or a writing
    definition (fixed point). A definition is flagged if, in its text, a call of a reading name follows a call of a
    writing name. A flag passes only if it is listed in the config's `examined_flags` with the reading that cleared
    it (the Pool's two flags were examined by X2c; the verifier program's by X7, written there).
(c) write order: for every definition that calls a boundary directly, the boundary calls in text order with their
    argument text. The sequence must equal the reference emission's (the workers' final emissions, whose orders they
    compared with the frozen handlers: X2c run c9 for the Pool, write-boundary.md; X1b run G for close_checkpoint,
    README-stage2b.md item C).
usage: fv_emit_gate_writeorder.py <program config.json> <raw dir>   (report on stdout; gate line last)"""
import json, re, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from fv_emit_lean import blocks

NAME = re.compile(r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)+')


def analyse(raw, bnd, reads):
    bl = [b for b in blocks(Path(raw) / 'Funs.lean') if b['kind'] in ('def', 'theorem', 'abbrev')]
    names = {b['lean'] for b in bl}
    calls = {}
    for b in bl:
        seq = []
        for m in NAME.finditer(b['text']):
            c = m.group(0)
            if c != b['lean'] and (c in names or c in bnd or c in reads):
                seq.append((m.start(), c))
        calls[b['lean']] = seq
    reading, writing = set(reads), set(bnd)
    changed = True
    while changed:
        changed = False
        for n, seq in calls.items():
            cs = {c for _, c in seq}
            if n not in reading and cs & reading: reading.add(n); changed = True
            if n not in writing and cs & writing: writing.add(n); changed = True
    flags = {}
    for n, seq in calls.items():
        fw = next((p for p, c in seq if c in writing), None)
        if fw is None: continue
        later = sorted({c for p, c in seq if p > fw and c in reading})
        if later: flags[n] = later
    order = {}
    for b in bl:
        L = b['text'].split('\n')
        hits = []
        for k, l in enumerate(L):
            for nme in sorted(bnd, key=len, reverse=True):
                if re.search(r'(?<![\w.])' + re.escape(nme) + r'(?![\w])', l):
                    arg = ' '.join(x.strip() for x in L[k:k + 4])
                    arg = arg[arg.index(nme):]
                    m = re.match(re.escape(nme) + r'((?:\s+(?:[A-Za-z0-9_#.]+|\([^()]*\)))*)', arg)
                    hits.append('%s%s' % (nme, m.group(1) if m else ''))
                    break
        if hits: order[b['lean']] = (b['decl'], hits)
    return writing - set(bnd), flags, order


cfg, raw = json.loads(Path(sys.argv[1]).read_text()), sys.argv[2]
bnd, reads = set(cfg['write_boundaries']), set(cfg['read_externals'])
w, flags, order = analyse(raw, bnd, reads)
rw, rflags, rorder = analyse(cfg['reference_raw'], bnd, reads)
ex = cfg.get('examined_flags', {})
ok = True
print('== (b) read before write: %d definitions write (directly or through calls)' % len(w))
for n in sorted(w): print('   writes: %s' % n)
for n, later in sorted(flags.items()):
    v = ('examined: ' + ex[n]) if n in ex else 'NOT EXAMINED'
    print('  FLAG %s: reading call(s) %s after its first writing call; %s' % (n, later, v))
    ok &= n in ex
print('  flags %d (reference %s: %d)' % (len(flags), cfg['reference_label'], len(rflags)))
print('== (c) boundary calls in emission order (argument text), against the reference emission')
for n in sorted(set(order) | set(rorder)):
    a, r = order.get(n), rorder.get(n)
    same = a is not None and r is not None and a[1] == r[1]
    ok &= same
    print('  %s%s' % (n, ' (Funs.lean line %d)' % a[0] if a else ''))
    for h in (a[1] if a else []): print('      %s' % h)
    print('    %s' % ('same sequence as the reference' if same else ('DIFFERS from the reference: %s' % (r[1] if r else 'absent there'))))
for n in cfg.get('writers_checked', []):
    if n not in w and n not in order:
        print('  NOTE: %s is not a writing definition here' % n)
print('gate (v) read before write and write order: %s' % ('pass' if ok else 'FAIL'))
sys.exit(0 if ok else 1)
