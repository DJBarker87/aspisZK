#!/usr/bin/env python3
"""PCUD_mkbundle.py BK ROUND : build PRVEq_bundle_<BK><ROUND>.lean from the labels of gen/bundles.json[BK] (current PRVEq_<label>.lean files)."""
import json,subprocess,sys
bk,rnd=sys.argv[1:3];ms=json.load(open('gen/bundles.json'))[bk]
files=[f'PRVEq_{l}.lean' for l in ms]
subprocess.check_call(['python3','-B','PCUD_bundle.py',f'PRVEq_bundle_{bk}{rnd}.lean',f'gen/bundle_{bk}{rnd}_offsets.json',*files])
