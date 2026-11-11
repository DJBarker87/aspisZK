"""Literal substitutions for generators that hard-code 26 October native
verifier values (W5 HARDCODED.json).  Each entry maps a generator to
(name, fn(code, values) -> code).  values = DERIVED-26OCT.json in check mode
(the substitution must then be the identity) or PIN2W5_VALUES.json in pin2 mode.
Every fn asserts that it replaced exactly one occurrence."""
import re
def one(pattern, repl):
    def fn(code, V):
        new, n = re.subn(pattern, lambda m: repl(m, V), code, flags=re.M)
        assert n == 1, (pattern, n)
        return new
    return fn
q22 = lambda V: [V['tx1']['5'][str(i)][0] for i in range(22)]
def qlist(m, V): return m.group(1) + '[' + ','.join(map(str, q22(V))) + ']'
SUBS = {
 'evidence/fixture-tx2c-20261026/JFn_generate_arrays.py': [
   ('q = tx1 tag5 indices 0..21 (checkpoint queries)', one(r'^( q=)\[[0-9,]+\](?=\[i\]$)', qlist))],
 'evidence/fixture-tx2c-20261026/JFn_generate_values.py': [
   ('query = tx1 tag5 indices 0..21 (checkpoint queries)', one(r'^(   query=)\[[0-9,]+\](?=\[i\]$)', qlist))],
}
