#!/usr/bin/env python3
"""X2c: compare the handler-state dumps of the frozen and the rewritten Pool test trees (fv_x2c_test.sh with
X2C_STATE_DUMP). Each dump file is one test; each record is one handler call: the handler, its result, whether
every account passed in is unchanged, and every account's key, owner, lamports and complete data before and after.

usage: fv_x2c_compare_dumps.py <frozen dump dir> <rewrite dump dir>
Prints one row per test (calls, Ok/Err counts, rejected calls that changed an account, identical or not) and the
first differing record of any test that differs. Exit status 0 iff every test's records are byte-identical and both
directories hold the same tests with the same exit codes."""
import os, re, sys

REC = re.compile(r'^(initialize|checkpoint|deposit|terminal) result=(.*) unchanged=(true|false)$')


def records(path):
    out, cur = [], None
    for line in open(path):
        m = REC.match(line.rstrip('\n'))
        if m:
            cur = [m.group(1), m.group(2), m.group(3), []]
            out.append(cur)
        else:
            cur[3].append(line.rstrip('\n'))
    return out


def main():
    a, b = sys.argv[1], sys.argv[2]
    ok = True
    ea, eb = open(os.path.join(a, 'exit-codes.txt')).read(), open(os.path.join(b, 'exit-codes.txt')).read()
    if ea != eb:
        ok = False
        print('exit codes differ:')
        sa, sb = set(ea.splitlines()), set(eb.splitlines())
        for line in sorted(sa ^ sb):
            print('  ', 'frozen' if line in sa else 'rewrite', line)
    fa = sorted(f for f in os.listdir(a) if f.endswith('.txt') and f != 'exit-codes.txt')
    fb = sorted(f for f in os.listdir(b) if f.endswith('.txt') and f != 'exit-codes.txt')
    if fa != fb:
        ok = False
        print('test sets differ:', sorted(set(fa) ^ set(fb)))
    total = dict(calls=0, ok=0, err=0, err_changed=0)
    print('%-95s %5s %4s %4s %11s %s' % ('test', 'calls', 'ok', 'err', 'err_changed', 'identical'))
    for f in fa:
        if f not in fb:
            continue
        ra, rb = records(os.path.join(a, f)), records(os.path.join(b, f))
        same = ra == rb
        ok &= same
        n_ok = sum(1 for r in ra if r[1] == 'Ok(())')
        n_err = len(ra) - n_ok
        n_err_changed = sum(1 for r in ra if r[1] != 'Ok(())' and r[2] == 'false')
        for k, v in (('calls', len(ra)), ('ok', n_ok), ('err', n_err), ('err_changed', n_err_changed)):
            total[k] += v
        print('%-95s %5d %4d %4d %11d %s' % (f[:-4], len(ra), n_ok, n_err, n_err_changed, 'yes' if same else 'NO'))
        if not same:
            for i, (x, y) in enumerate(zip(ra, rb)):
                if x != y:
                    print('   first difference at call %d: frozen %s %s / rewrite %s %s' % (i, x[0], x[1], y[0], y[1]))
                    for la, lb in zip(x[3], y[3]):
                        if la != lb:
                            for j, (p, q) in enumerate(zip(la.split(' ['), lb.split(' ['))):
                                if p != q:
                                    print('     account field %d: frozen %s' % (j, p[:160]))
                                    print('     account field %d: rewrite %s' % (j, q[:160]))
                                    break
                            break
                    break
            if len(ra) != len(rb):
                print('   call counts differ: %d / %d' % (len(ra), len(rb)))
    print('totals', total)
    print('overall', 'identical' if ok else 'DIFFERENT')
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
