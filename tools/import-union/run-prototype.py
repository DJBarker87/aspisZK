#!/usr/bin/env python3
"""Compile each copied cone dependency once, from the changed Types upward."""
import json, pathlib, subprocess, sys
ROOT = pathlib.Path(__file__).resolve().parents[2]
E = ROOT/'docs/research/100bit-spend-path-20261013/evidence/import-coll-20261021'
modules = [r['module'] for r in json.loads((E/'copy-provenance.json').read_text())]
start = sys.argv[1] if len(sys.argv)>1 else modules[0]
for module in modules[modules.index(start):]:
 print('Focused target:', module, flush=True)
 result = subprocess.run([sys.executable,str(ROOT/'tools/import-union/compile.py'),module,'1'])
 if result.returncode: raise SystemExit(result.returncode)
