#!/usr/bin/env python3
"""X2d item 2: planted reads in a COPY of a real emission, to show that fv_emit_read_after_write.py fires on the
emitted shapes themselves (not only on the hand-written planted files). A tool record, not a proof.

usage: fv_x2d_raw_mutants.py <Funs.lean> <out dir> <tool.py> <write name> <read names> <roots> <mutation> [<mutation> ...]
  mutation = <definition>:<anchor>:<read name>
    Inserts, inside <definition>, right after the statement that contains the first occurrence of <anchor> (a name),
    a line `let x2d_planted ← <read name> x2d_account` at that statement's indentation. The copy is written to
    <out dir>/<k>/Funs.lean and the tool is run on it with the given roots. The original file is not changed.
Prints, per mutation, the inserted line number and the tool's verdict lines; exit status 0 iff the tool reports
FAIL for every mutation."""
import os, re, subprocess, sys


def mutate(lines, definition, anchor, read):
    start = next(i for i, l in enumerate(lines) if re.match(r'^(def|impl_def)\s*$', l) and lines[i + 1].strip().split()[0] == definition
                 or re.match(r'^(def|impl_def)\s+' + re.escape(definition) + r'(\s|$)', l))
    end = next((i for i in range(start + 1, len(lines)) if lines[i] and not lines[i][0].isspace()), len(lines))
    hit = next(i for i in range(start, end) if anchor in lines[i])
    # the statement containing the anchor begins at the last line at or above `hit` whose indentation is not greater
    # than that of the following lines of the statement; take the line itself if it starts with 'let' or the anchor
    s = hit
    while s > start and (not re.match(r'\s*(let\b|' + re.escape(anchor) + r')', lines[s]) or lines[s - 1].rstrip().endswith('←')):
        s -= 1
    ind = len(lines[s]) - len(lines[s].lstrip())
    e = s + 1
    while e < end and (len(lines[e]) - len(lines[e].lstrip())) > ind:
        e += 1
    lines.insert(e, ' ' * ind + 'let x2d_planted ← %s x2d_account' % read)
    return e + 1


def main():
    src, out, tool, write, reads, roots = sys.argv[1:7]
    muts = sys.argv[7:]
    base = open(src).read().split('\n')
    ok = True
    for k, m in enumerate(muts):
        definition, anchor, read = m.split(':')
        lines = list(base)
        at = mutate(lines, definition, anchor, read)
        d = os.path.join(out, str(k))
        os.makedirs(d, exist_ok=True)
        open(os.path.join(d, 'Funs.lean'), 'w').write('\n'.join(lines))
        r = subprocess.run([sys.executable, '-I', tool, '--funs', os.path.join(d, 'Funs.lean'), '--write', write, '--read', reads,
                            '--root', roots], capture_output=True, text=True)
        verdicts = [l for l in r.stdout.split('\n') if l.startswith('== root') or 'read after write in' in l or l.startswith('overall')]
        print('mutation %d: %s, read inserted at line %d; tool exit %d' % (k, m, at, r.returncode))
        for v in verdicts:
            print('   ' + v)
        ok &= r.returncode != 0
    print('all mutations reported' if ok else 'SOME MUTATION NOT REPORTED')
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
