#!/usr/bin/env python3
"""Aspis extraction probe: list the Aspis functions of a Charon run with their body kind. Reads only. usage: XP_decls.py <run> [all]"""
import json, sys, collections
from pathlib import Path
E = Path(__file__).resolve().parent
d = json.load(open(E / 'runs' / sys.argv[1] / 'declarations.json'))
print(len(d), dict(collections.Counter(str(x['body']) for x in d)))
show_all = len(sys.argv) > 2
for x in sorted(d, key=lambda x: x['name']):
    if show_all or x['name'].startswith(('aspis_', 'solana_')):
        print('%-12s %s' % (str(x['body'])[:12], x['name']))
