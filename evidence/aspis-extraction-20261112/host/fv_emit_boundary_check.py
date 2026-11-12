#!/usr/bin/env python3
"""X7 gate (vi): grammar check of the account write boundaries and of the hash call.

usage: fv_emit_boundary_check.py [--only name,...] <rust file>...      forms D, Z, L (account writes)
       fv_emit_boundary_check.py --hash <name> <rust file>             form H (the hash call), separate

Forms D, Z and L are X2c's checker, fv_x2c_write_boundary_check.py, imported UNCHANGED (its file is not edited; its
tokenizer still rejects every string or character literal, so nothing here loosens those three forms). The first
usage simply runs it.

Form H is a clearly separate fourth form for `SolanaDigest::digest_into` (programs/r1-cost-probe/src/lib.rs), the
runtime hash call of PIN-RULES section 5: a method with exactly two cfg-gated branches, each ONE runtime call whose
arguments are the method's parameters, and nothing else. Token for token (comments, whitespace and the two parameter
names are free; nothing else is):

    [#[inline] | #[inline(always)]]
    fn NAME(&self, PARTS: &[&[u8]], OUT: &mut [u8; 32]) {
        #[cfg(target_os = "solana")]
        [#[allow(deprecated)]]
        unsafe {
            solana_program::syscalls::sol_sha256(PARTS as *const _ as *const u8, PARTS.len() as u64, OUT.as_mut_ptr());
        }
        #[cfg(not(target_os = "solana"))]
        {
            *OUT = hashv(PARTS).to_bytes();
        }
    }

So: on SBF one call of the runtime's `sol_sha256` syscall whose three arguments are the parts slice (as a raw
pointer), its length (as u64) and the output buffer's pointer; on the host one call of the SDK's `hashv` over the same
parts, its value stored into the output parameter. No arithmetic beyond the two casts the syscall's signature needs,
no branch on data, no loop, no other call, no read of anything but the parameters, no third branch. The only string
literal accepted is `"solana"`, and only in the two cfg attributes (form H has its own tokenizer; X2c's is not used
for it). Exit status 0 iff the function is found exactly once and matches."""
import re, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
import fv_x2c_write_boundary_check as X2C   # forms D, Z, L, unchanged

TOKH = re.compile(r'\s+|//[^\n]*|/\*.*?\*/|"solana"|[A-Za-z_][A-Za-z0-9_]*|[0-9]+|[^\sA-Za-z0-9_]', re.S)


def tokens_h(text):
    out, pos = [], 0
    while pos < len(text):
        m = TOKH.match(text, pos)
        if not m:
            raise X2C.Fail('untokenizable input at offset %d' % pos)
        t = m.group(0)
        pos = m.end()
        if t.isspace() or t.startswith('//') or t.startswith('/*'):
            continue
        if t in ('"', "'"):
            raise X2C.Fail('string or char literal other than "solana" at line %d' % (text.count('\n', 0, m.start()) + 1))
        out.append((t, text.count('\n', 0, m.start()) + 1))
    return out


def check_h(c):
    first = c.line()
    if c.peek() == '#':
        c.seq('# [ inline')
        if c.peek() == '(':
            c.seq('( always )')
        c.take(']')
    c.take('fn')
    name = c.ident()
    c.seq('( & self ,')
    parts = c.ident()
    c.seq(': & [ & [ u8 ] ] ,')
    out = c.ident()
    c.seq(': & mut [ u8 ; 32 ] ) {')
    if parts == out:
        raise X2C.Fail('the two parameters have one name')
    # SBF branch
    c.seq('# [ cfg ( target_os = "solana" ) ]')
    if c.peek() == '#':
        c.seq('# [ allow ( deprecated ) ]')
    c.seq('unsafe { solana_program : : syscalls : : sol_sha256 (')
    if c.ident() != parts: raise X2C.Fail('line %d: first syscall argument is not the parts parameter' % c.line())
    c.seq('as * const _ as * const u8 ,')
    if c.ident() != parts: raise X2C.Fail('line %d: second syscall argument is not the length of the parts parameter' % c.line())
    c.seq('. len ( ) as u64 ,')
    if c.ident() != out: raise X2C.Fail('line %d: third syscall argument is not the output parameter' % c.line())
    c.seq('. as_mut_ptr ( ) ) ; }')
    # host branch
    c.seq('# [ cfg ( not ( target_os = "solana" ) ) ] { *')
    if c.ident() != out: raise X2C.Fail('line %d: the host branch does not store into the output parameter' % c.line())
    c.seq('= hashv (')
    if c.ident() != parts: raise X2C.Fail('line %d: hashv is not applied to the parts parameter' % c.line())
    c.seq(') . to_bytes ( ) ; } }')
    return name, first, c.t[c.i - 1][1]


def check_hash(path, name):
    text = open(path).read()
    found = list(re.finditer(r'(?m)^[ \t]*(?:#\[inline[^\]\n]*\]\s*\n[ \t]*)?fn[ \t]+' + re.escape(name) + r'\b', text))
    if len(found) != 1:
        return False, (name, 0, 0, 'FAIL', 'found %d definitions' % len(found))
    start = found[0].start()
    k = text.index('{', found[0].end())
    depth = 0
    while k < len(text):
        if text[k] == '{': depth += 1
        elif text[k] == '}':
            depth -= 1
            if depth == 0: break
        k += 1
    off = text.count('\n', 0, start)
    try:
        toks = [(t, l + off) for t, l in tokens_h(text[start:k + 1])]
        c = X2C.Cursor(toks, 0)
        n, a, b = check_h(c)
        if c.i != len(toks):
            raise X2C.Fail('trailing tokens after the function')
        return True, (n, a, b, 'pass', '')
    except (X2C.Fail, ValueError) as exc:
        return False, (name, off + 1, text.count('\n', 0, k) + 1, 'FAIL', str(exc))


def main():
    a = sys.argv[1:]
    if a and a[0] == '--hash':
        ok, (n, f, l, v, why) = check_hash(a[2], a[1])
        print('file %s' % a[2])
        print('  %-4s %s lines %d-%d (%d lines) form H%s' % (v, n, f, l, l - f + 1 if f else 0, (': ' + why) if why else ''))
        print('overall', 'pass' if ok else 'FAIL')
        sys.exit(0 if ok else 1)
    sys.argv = [sys.argv[0]] + a
    X2C.main()


if __name__ == '__main__':
    main()
