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

def rep(old, new_check, new_pin2, count=1):
    def fn(code, mode):
        new = new_check if mode == 'check' else new_pin2
        assert code.count(old) == count, (old, code.count(old))
        return code.replace(old, new)
    return fn
# JFp_generate_input.py (NDO_JFp_InitBytes): public length 1455 -> 1520, frame 1530 -> 1595,
# SHA blocks: 23 head + tail (24 rest defs) -> 24 head + tail (25 rest defs); the binding
# tail chunks JFs_Cell04/05 of the PIN2 JFs_SerializedBytes are 32-byte items like digests.
PARAM = {
 'evidence/joint-fixture10-20261026/JFp_generate_input.py': [
   ('public length word', rep("(core.num.U32.to_le_bytes 1455#u32).val']", "(core.num.U32.to_le_bytes 1455#u32).val']", "(core.num.U32.to_le_bytes 1520#u32).val']")),
   ('32-byte chunk rule', rep("32 if 'Digest' in x else", "32 if 'Digest' in x else", "32 if ('Digest' in x or 'JFs_Cell0' in x) else")),
   ('frame length', rep("assert sum(lengths)==1530", "assert sum(lengths)==1530", "assert sum(lengths)==1595")),
   ('rest definitions', rep("for block in range(24):", "for block in range(24):", "for block in range(25):")),
   ('step theorems', rep(" if block<23:", " if block<23:", " if block<24:")),
   ('last rest', rep("theorem last : rest23=JFp_SeedHash.tail := by\\n  simp only [rest23,", "theorem last : rest23=JFp_SeedHash.tail := by\\n  simp only [rest23,", "theorem last : rest24=JFp_SeedHash.tail := by\\n  simp only [rest24,")),
   ('regroup steps', rep("for i in range(23))+',last]", "for i in range(23))+',last]", "for i in range(24))+',last]")),
   ('native length word', rep("root 1455#u32)).map Fin.val = numeric", "root 1455#u32)).map Fin.val = numeric", "root 1520#u32)).map Fin.val = numeric")),
 ],
}
