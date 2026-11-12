#!/usr/bin/env python3
"""X1 stage 2, item I: binders that shadow module names in the emitted Lean are renamed, nothing else changes (same
lines): the parameter `compact` of compact::expand_values, check_values, expand_semantic becomes `encoded`; the local
`weights` of weights::factored_s2_libra_weights becomes `libra_w`. Run after item F if F is applied (F's test module
keeps the frozen body under its own name)."""
import re, sys
from pathlib import Path
T = Path(sys.argv[1]); assert 'src-frz-a' not in str(T)
def rename(path, fn_head, old, new):
    p = T / path; t = p.read_text()
    a = t.index(fn_head); b = t.index('\n}\n', a) + 3
    body = t[a:b]; nb = re.sub(r'(?<![\w:])%s(?!\w|::)' % old, new, body)
    assert nb != body, (path, fn_head)
    p.write_text(t[:a] + nb + t[b:]); print('ok', path, fn_head, body.count(old))
rename('crates/aspis-r1-cost-probe/src/compact.rs', 'pub fn expand_values(', 'compact', 'encoded')
rename('crates/aspis-r1-cost-probe/src/compact.rs', 'pub fn check_values(', 'compact', 'encoded')
rename('crates/aspis-r1-cost-probe/src/compact.rs', 'pub fn expand_semantic(', 'compact', 'encoded')
rename('crates/aspis-r1-cost-probe/src/weights.rs', 'factored_s2_libra_weights', 'weights', 'libra_w')
