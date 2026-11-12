#!/usr/bin/env python3
"""X2c: three checks on one Aeneas emission of the Pool (coordinator item 3), program-independent apart from the
arguments.

usage: fv_x2c_emission_checks.py <raw dir (Funs.lean, FunsExternal_Template.lean)> <boundary Lean name>
                                 <read external Lean name>[,<more>] <source dir>[,<more>] <boundary source file>

(a) single route. Source: every `try_borrow_mut_data`, `try_borrow_mut_lamports`, `.data.borrow_mut()` and
    `.lamports.borrow_mut()` in the given source dirs, with file, line, enclosing function and whether it is inside a
    `#[cfg(test)]` item. Emission: every name in Funs.lean or the external template that contains `borrow_mut` or
    `lamports_mut`. Pass iff the emission has no mutable-handle name except inside the boundary's own (bodiless)
    declaration, and every non-test source site is either in the boundary file or in a function that has no emitted
    definition (not reached from the roots).
(b) read before write. The emitted definitions are parsed; a definition is "reading" if it calls a read external or
    a reading definition, "writing" if it calls the boundary or a writing definition (fixed point). A definition is
    flagged if, in its text, a call of a reading name appears after a call of a writing name.
(c) write order. For every definition that calls the boundary directly, each call in text order with its argument
    text (up to the end of the call's lines).
Exit status 0 iff (a) passes and (b) flags nothing."""
import os, re, sys


def parse_defs(text):
    """Returns [(name, start, end)] for top-level `def`/`axiom` items (name may be on the next line)."""
    lines = text.split('\n')
    starts = []
    for i, line in enumerate(lines):
        m = re.match(r'^(?:@\[[^\]]*\]\s*)?(?:noncomputable |private |partial |unsafe )*(def|axiom|opaque|theorem)\b\s*(\S*)', line)
        if m:
            name = m.group(2)
            if not name and i + 1 < len(lines):
                name = lines[i + 1].strip().split()[0] if lines[i + 1].strip() else ''
            starts.append((i, name))
    out = []
    for k, (i, name) in enumerate(starts):
        j = starts[k + 1][0] if k + 1 < len(starts) else len(lines)
        # stop the body at the doc comment of the next item
        out.append((name, i, j))
    return lines, out


NAME = re.compile(r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)+')


def enclosing_fn(lines, idx):
    for j in range(idx, -1, -1):
        m = re.search(r'\bfn\s+([A-Za-z_][A-Za-z0-9_]*)', lines[j])
        if m and not lines[j].lstrip().startswith('//'):
            return m.group(1)
    return '?'


def test_ranges(lines):
    """Line ranges of items under #[cfg(test)] or #[cfg(all(test, ...))] (brace matched)."""
    ranges = []
    i = 0
    while i < len(lines):
        if re.match(r'\s*#\[cfg\((?:all\()?test\b', lines[i]):
            depth, j, seen = 0, i + 1, False
            while j < len(lines):
                depth += lines[j].count('{') - lines[j].count('}')
                if '{' in lines[j]:
                    seen = True
                if seen and depth <= 0:
                    break
                if not seen and lines[j].rstrip().endswith(';'):
                    break
                j += 1
            ranges.append((i, j))
            i = j + 1
        else:
            i += 1
    return ranges


def main():
    raw, boundary, reads, srcs, boundary_file = sys.argv[1], sys.argv[2], sys.argv[3].split(','), sys.argv[4].split(','), sys.argv[5]
    funs = open(os.path.join(raw, 'Funs.lean')).read()
    ext = open(os.path.join(raw, 'FunsExternal_Template.lean')).read()
    lines, defs = parse_defs(funs)
    names = {d[0] for d in defs}
    ok = True

    print('== (a) single route')
    emitted_short = {n.split('.')[-1] for n in names}
    src_sites = []
    for root in srcs:
        for dp, _, fs in os.walk(root):
            for f in sorted(fs):
                if not f.endswith('.rs'):
                    continue
                path = os.path.join(dp, f)
                sl = open(path).read().split('\n')
                tr = test_ranges(sl)
                for i, l in enumerate(sl):
                    if re.search(r'try_borrow_mut_data|try_borrow_mut_lamports|\.data\.borrow_mut\(\)|\.lamports\.borrow_mut\(\)', l) and not l.lstrip().startswith('//'):
                        in_test = any(a <= i <= b for a, b in tr)
                        fn = enclosing_fn(sl, i)
                        src_sites.append((path, i + 1, fn, in_test))
    for path, line, fn, in_test in src_sites:
        rel = path.split('/src/')[-1] if '/src/' in path else path
        is_boundary = os.path.abspath(path) == os.path.abspath(boundary_file)
        emitted = fn in emitted_short
        if in_test:
            verdict = 'test only'
        elif is_boundary:
            verdict = 'boundary (opaque by name)'
        elif emitted:
            verdict = 'FAIL: in an emitted (translated) function'
            ok = False
        else:
            verdict = 'not reached: no emitted definition'
        print('  source %s:%d fn %s: %s' % (rel, line, fn, verdict))
    em = sorted(set(re.findall(r'[A-Za-z0-9_.]*(?:borrow_mut|lamports_mut)[A-Za-z0-9_.]*', funs)))
    ex = sorted(set(re.findall(r'[A-Za-z0-9_.]*(?:borrow_mut|lamports_mut)[A-Za-z0-9_.]*', ext)))
    print('  emission Funs.lean names with a mutable handle: %s' % (em or 'none'))
    print('  emission external template names with a mutable handle: %s' % (ex or 'none'))
    if em or ex:
        ok = False
    bdecl = re.findall(r'^axiom (' + re.escape(boundary) + r')\b', ext, re.M)
    print('  boundary %s: %s' % (boundary, 'bodiless axiom in the external template' if bdecl else 'NOT FOUND as an axiom'))
    if not bdecl or boundary in names:
        ok = False
        print('  FAIL: the boundary must be bodiless and have no definition in Funs.lean')

    print('== (b) read before write')
    body = {n: '\n'.join(lines[i:j]) for n, i, j in defs}
    calls = {}
    for n, t in body.items():
        seq = []
        for m in NAME.finditer(t):
            c = m.group(0)
            if c != n and (c in names or c == boundary or c in reads):
                seq.append((m.start(), c))
        calls[n] = seq
    reading, writing = set(reads), {boundary}
    changed = True
    while changed:
        changed = False
        for n, seq in calls.items():
            cs = {c for _, c in seq}
            if n not in reading and cs & reading:
                reading.add(n); changed = True
            if n not in writing and cs & writing:
                writing.add(n); changed = True
    flags = 0
    for n, seq in calls.items():
        first_write = next((p for p, c in seq if c in writing), None)
        if first_write is None:
            continue
        later_reads = [c for p, c in seq if p > first_write and c in reading]
        if later_reads:
            flags += 1
            print('  FLAG %s: reading call(s) %s after its first writing call' % (n, sorted(set(later_reads))))
    print('  definitions that write (directly or through calls): %d; flagged: %d' % (len(writing) - 1, flags))
    for n in sorted(writing - {boundary}):
        print('    writes: %s' % n)
    if flags:
        ok = False

    print('== (c) boundary calls in emission order')
    for n, i, j in defs:
        t = lines[i:j]
        hits = [k for k, l in enumerate(t) if boundary in l]
        if not hits:
            continue
        print('  %s (Funs.lean lines %d-%d)' % (n, i + 1, j))
        for k in hits:
            arg = ' '.join(x.strip() for x in t[k:k + 4])
            arg = arg[arg.index(boundary):]
            depth, end = 0, len(arg)
            print('    line %d: %s' % (i + k + 1, arg[:220]))
    print('overall', 'pass' if ok else 'FAIL')
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
