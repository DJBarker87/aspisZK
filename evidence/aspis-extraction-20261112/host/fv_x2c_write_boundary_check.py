#!/usr/bin/env python3
"""X2c: grammar check for account write-boundary functions (Solana SDK `AccountInfo`), program-independent.

usage: fv_x2c_write_boundary_check.py <rust file> [<rust file> ...]

Every `fn` item in each file must match one of the two accepted forms below, token for token (comments, whitespace
and the parameter and local names are free; nothing else is). Exit status 0 iff every function passes and at least
one function was found.

Form D (account data):
    [#[inline] | #[inline(always)] | #[inline(never)]]
    [pub | pub(crate)] fn NAME(ACC: &AccountInfo<LT>, START: usize, END: usize, SRC: &[u8]) -> ProgramResult {
        let mut G = match ACC.try_borrow_mut_data() { Ok(X) => X, Err(E) => return Err(E), };
        G[START..END].copy_from_slice(SRC);
        Ok(())
    }
  (the four parameters in any order; SRC may also be `&[u8; N]` with N a literal or an UPPER_CASE constant path)

Form L (lamports of one account):
    [attribute as above] [pub | pub(crate)] fn NAME(ACC: &AccountInfo<LT>, AMOUNT: u64) -> ProgramResult {
        let mut G = match ACC.try_borrow_mut_lamports() { Ok(X) => X, Err(E) => return Err(E), };
        **G = AMOUNT;
        Ok(())
    }

So: one SDK borrow of one account's mutable handle with the error returned unchanged; one assignment or
`copy_from_slice` whose destination range and source are parameters; no arithmetic, branch, loop, other call, read
of the account's contents or second account. LT is `'_` or one lifetime parameter declared on the function. The
match arms may appear in either order; a trailing comma after the last arm is optional.

The tokenizer is deliberately small: identifiers, lifetimes, integer literals, and single punctuation characters
(so `..` is two `.` tokens and `->` is `-` `>`). String and char literals are rejected outright (no accepted form
contains one)."""
import re, sys

TOKEN = re.compile(r"\s+|//[^\n]*|/\*.*?\*/|'[A-Za-z_][A-Za-z0-9_]*(?!')|[A-Za-z_][A-Za-z0-9_]*|[0-9][0-9_]*(?:usize|u64|u32|u8)?|[^\sA-Za-z0-9_]", re.S)


def tokens(text):
    out, pos = [], 0
    while pos < len(text):
        m = TOKEN.match(text, pos)
        if not m:
            raise ValueError("untokenizable input at offset %d" % pos)
        t = m.group(0)
        pos = m.end()
        if t.isspace() or t.startswith('//') or t.startswith('/*'):
            continue
        if t in ('"', "'"):
            raise ValueError("string or char literal at offset %d" % m.start())
        out.append((t, text.count('\n', 0, m.start()) + 1))
    return out


IDENT = re.compile(r"[a-z_][a-z0-9_]*$")
CONST = re.compile(r"(?:[a-z_][a-z0-9_]*::)*[A-Z][A-Z0-9_]*$|[0-9][0-9_]*(?:usize)?$")


class Fail(Exception):
    pass


class Cursor:
    def __init__(self, toks, i):
        self.t, self.i = toks, i

    def peek(self, k=0):
        return self.t[self.i + k][0] if self.i + k < len(self.t) else None

    def take(self, expected=None):
        if self.i >= len(self.t):
            raise Fail("unexpected end of file")
        tok = self.t[self.i][0]
        if expected is not None and tok != expected:
            raise Fail("line %d: expected %r, found %r" % (self.t[self.i][1], expected, tok))
        self.i += 1
        return tok

    def seq(self, text):
        for piece in text.split():
            self.take(piece)

    def ident(self):
        tok = self.take()
        if not IDENT.match(tok) or tok in ('let', 'mut', 'match', 'return', 'fn', 'pub', 'if', 'else', 'loop', 'while', 'for', 'unsafe', 'self'):
            raise Fail("line %d: expected a name, found %r" % (self.t[self.i - 1][1], tok))
        return tok

    def line(self):
        return self.t[min(self.i, len(self.t) - 1)][1]


def parse_type(c, lifetimes):
    """Returns 'acc', 'usize', 'u64', 'bytes'; anything else fails."""
    if c.peek() == '&':
        c.take('&')
        if c.peek() == '[':
            c.seq('[ u8')
            if c.peek() == ';':
                c.take(';')
                n = c.take()
                while c.peek() == ':' and c.peek(1) == ':':
                    c.seq(': :')
                    n += '::' + c.take()
                if not CONST.match(n):
                    raise Fail("line %d: array length %r is not a literal or constant" % (c.line(), n))
            c.take(']')
            return 'bytes'
        c.seq('AccountInfo <')
        lt = c.take()
        if lt != "'_" and lt not in lifetimes:
            raise Fail("line %d: lifetime %r not declared" % (c.line(), lt))
        c.take('>')
        return 'acc'
    ty = c.take()
    if ty in ('usize', 'u64'):
        return ty
    raise Fail("line %d: parameter type %r is outside the grammar" % (c.line(), ty))


def parse_borrow(c, acc_name, method):
    """let mut G = match ACC.METHOD() { Ok(X) => X, Err(E) => return Err(E), };  -> G"""
    c.seq('let mut')
    guard = c.ident()
    c.seq('= match')
    if c.ident() != acc_name:
        raise Fail("line %d: the borrow is not taken on the account parameter" % c.line())
    c.take('.')
    if c.take() != method:
        raise Fail("line %d: the borrow method is not %s" % (c.line(), method))
    c.seq('( ) {')
    arms = set()
    for k in range(2):
        head = c.take()
        if head == 'Ok' and 'ok' not in arms:
            c.take('(')
            x = c.ident()
            c.seq(') = >')
            if c.ident() != x:
                raise Fail("line %d: the Ok arm does not return its binding unchanged" % c.line())
            arms.add('ok')
        elif head == 'Err' and 'err' not in arms:
            c.take('(')
            e = c.ident()
            c.seq(') = > return Err (')
            if c.ident() != e:
                raise Fail("line %d: the Err arm does not return the borrow error unchanged" % c.line())
            c.take(')')
            arms.add('err')
        else:
            raise Fail("line %d: unexpected match arm %r" % (c.line(), head))
        if k == 0:
            c.take(',')
        elif c.peek() == ',':
            c.take(',')
    c.seq('} ;')
    return guard


def check_fn(c):
    """c is positioned at the first token of an item. Returns (name, first line, last line)."""
    first = c.line()
    if c.peek() == '#':
        c.seq('# [ inline')
        if c.peek() == '(':
            c.take('(')
            if c.take() not in ('always', 'never'):
                raise Fail("line %d: inline argument outside the grammar" % c.line())
            c.take(')')
        c.take(']')
    if c.peek() == 'pub':
        c.take('pub')
        if c.peek() == '(':
            c.seq('( crate )')
    c.take('fn')
    name = c.ident()
    lifetimes = set()
    if c.peek() == '<':
        c.take('<')
        lt = c.take()
        if not lt.startswith("'") or lt == "'_":
            raise Fail("line %d: only one lifetime parameter is allowed" % c.line())
        lifetimes.add(lt)
        c.take('>')
    c.take('(')
    params = []
    while c.peek() != ')':
        pname = c.ident()
        c.take(':')
        params.append((pname, parse_type(c, lifetimes)))
        if c.peek() == ',':
            c.take(',')
    c.take(')')
    c.seq('- > ProgramResult {')
    kinds = sorted(k for _, k in params)
    names = [n for n, _ in params]
    if len(set(names)) != len(names):
        raise Fail("duplicate parameter names")
    by = {}
    for n, k in params:
        by.setdefault(k, []).append(n)
    if kinds == ['acc', 'bytes', 'usize', 'usize']:
        acc = by['acc'][0]
        guard = parse_borrow(c, acc, 'try_borrow_mut_data')
        if c.ident() != guard:
            raise Fail("line %d: the write is not through the borrowed guard" % c.line())
        c.take('[')
        start = c.ident()
        c.seq('. .')
        end = c.ident()
        c.seq('] . copy_from_slice (')
        src = c.ident()
        c.seq(') ;')
        if (start, end) not in [(by['usize'][0], by['usize'][1]), (by['usize'][1], by['usize'][0])] or start == end:
            raise Fail("line %d: the destination range is not given by the two usize parameters" % c.line())
        if src != by['bytes'][0]:
            raise Fail("line %d: the source is not the byte parameter" % c.line())
        form = 'D'
    elif kinds == ['acc', 'u64']:
        acc = by['acc'][0]
        guard = parse_borrow(c, acc, 'try_borrow_mut_lamports')
        c.seq('* *')
        if c.ident() != guard:
            raise Fail("line %d: the assignment is not through the borrowed guard" % c.line())
        c.take('=')
        if c.ident() != by['u64'][0]:
            raise Fail("line %d: the assigned value is not the amount parameter" % c.line())
        c.take(';')
        form = 'L'
    else:
        raise Fail("parameter list %s is outside the grammar" % kinds)
    c.seq('Ok ( ( ) ) }')
    return name, first, c.t[c.i - 1][1], form


def check_file(path):
    text = open(path).read()
    toks = tokens(text)
    c = Cursor(toks, 0)
    results, ok = [], True
    # Leading `use` items are allowed (imports only).
    while c.peek() is not None:
        if c.peek() == 'use':
            while c.take() != ';':
                pass
            continue
        start = c.i
        try:
            name, first, last, form = check_fn(c)
            results.append((name, first, last, form, 'pass', ''))
        except Fail as exc:
            ok = False
            # report the item name if one can be found, then skip to the end of the item's braces
            j, name = start, '?'
            while j < len(toks) and toks[j][0] != 'fn':
                j += 1
            if j + 1 < len(toks):
                name = toks[j + 1][0]
            depth, k, seen = 0, j, False
            while k < len(toks):
                if toks[k][0] == '{':
                    depth += 1; seen = True
                elif toks[k][0] == '}':
                    depth -= 1
                    if seen and depth == 0:
                        break
                k += 1
            results.append((name, toks[start][1], toks[min(k, len(toks) - 1)][1], '-', 'FAIL', str(exc)))
            c.i = k + 1
    return ok and bool(results), results


def main():
    all_ok = True
    for path in sys.argv[1:]:
        ok, results = check_file(path)
        all_ok &= ok
        print("file %s" % path)
        if not results:
            print("  FAIL no function found")
        for name, first, last, form, verdict, why in results:
            print("  %-4s %s lines %d-%d (%d lines) form %s%s" % (verdict, name, first, last, last - first + 1, form, (': ' + why) if why else ''))
    print("overall", "pass" if all_ok else "FAIL")
    sys.exit(0 if all_ok else 1)


if __name__ == '__main__':
    main()
