#!/usr/bin/env python3
"""Diagnostic: which package definitions used (not carried) by a check file depend on sorryAx.
usage: sorrydiag.py CHECKTAG  -> writes check/CHECKTAG-diag/RwCheck.lean (a list of #print axioms on package names)"""
import sys, json, pathlib
W = pathlib.Path('/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111')
t = sys.argv[1]; r = json.load(open(W / 'check' / t / 'mkcheck.json')); O = W / 'check' / (t + '-diag'); O.mkdir(parents=True, exist_ok=True)
L = ['import ProverPin2.Funs', '']
for k in r['package_definitions_used_not_carried']:
    n = k['name']; L.append(f'#print axioms {"" if k.get("package_axiom_used_in_place_of_the_emitted_body") else "ProverPin2."}{n}')
(O / 'RwCheck.lean').write_text('\n'.join(L) + '\n'); print(len(L) - 2)
