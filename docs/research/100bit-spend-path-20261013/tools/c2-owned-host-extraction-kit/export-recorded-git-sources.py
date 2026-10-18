#!/usr/bin/env python3
"""Export committed top-level model source candidates; read-only Git input."""
from pathlib import Path
import argparse,hashlib,json,subprocess
ROOT=Path(__file__).resolve().parents[5]
ap=argparse.ArgumentParser();ap.add_argument('--revision',required=True);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args()
ref=subprocess.check_output(['git','-C',str(ROOT),'rev-parse',a.revision]).decode().strip();prefix='docs/research/100bit-spend-path-20261013/lean/'
paths=subprocess.check_output(['git','-C',str(ROOT),'ls-tree','-r','--name-only',ref,prefix]).decode().splitlines();files={}
for path in paths:
 rel=path[len(prefix):]
 if '/' in rel or not rel.endswith('.lean'):continue
 b=subprocess.check_output(['git','-C',str(ROOT),'show',ref+':'+path]);files[rel[:-5]]={'path':path,'sha256':hashlib.sha256(b).hexdigest(),'source':b.decode()}
a.out.write_text(json.dumps({'revision':ref,'modules':files},sort_keys=True)+'\n');print(json.dumps({'revision':ref,'source_candidates':len(files),'sha256':hashlib.sha256(a.out.read_bytes()).hexdigest()}))
