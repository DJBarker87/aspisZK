#!/usr/bin/env python3
"""PCUC_mkbundle.py BK ROUND : build PRVEq_bundle_<BK><ROUND>.lean from gen/bundles.json[BK] (current PRVEq_<label>.lean files)."""
import json,subprocess,sys
bk,rnd=sys.argv[1:3];ms=json.load(open('gen/bundles.json'))[bk]
subprocess.check_call(['python3','-B','PCUC_bundle.py',f'PRVEq_bundle_{bk}{rnd}.lean',f'gen/bundle_{bk}{rnd}_offsets.json',*[f'PRVEq_{l}.lean' for l in ms]])
