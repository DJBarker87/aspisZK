#!/usr/bin/env python3
"""X1 stage 2, item B, line-preserving form (B2). CM31::inv without the function passed by value: the body of
inv_with with M31::inv written in place; the same field operations in the same order (norm = a*a + b*b; one M31::inv
of the norm; a*inv; (-b)*inv). The rewritten function keeps the frozen number of source lines (390-392), so every
panic location after it in field.rs keeps its line number. inv_with is unchanged (still used by
cm31_batch_inverse_with). The differential test of fv_x1_rwB.py is appended at the end of the file."""
import sys
from pathlib import Path
T = Path(sys.argv[1]); assert 'src-frz-a' not in str(T)
p = T / 'crates/aspis-core/src/field.rs'; t = p.read_text()
old = '''    pub fn inv(self) -> CM31 {
        self.inv_with(M31::inv)
    }
'''
new = '''    pub fn inv(self) -> CM31 {
        let inv_norm = self.a.mul(self.a).add(self.b.mul(self.b)).inv(); CM31 { a: self.a.mul(inv_norm), b: self.b.neg().mul(inv_norm) } // X1: inv_with's body with M31::inv in place
    }
'''
assert t.count(old) == 1; t = t.replace(old, new)
src = Path(__file__).with_name('fv_x1_rwB.py').read_text()
test = src[src.index("t += '''") + len("t += '''"):src.index("'''\np.write_text(t)")]
t += test
p.write_text(t); print('ok')
