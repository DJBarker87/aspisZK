#!/usr/bin/env python3
"""Current source correspondence; no compiler or source mutation."""
from pathlib import Path
import hashlib,json,subprocess,importlib.util,argparse
R=Path(__file__).resolve().parents[5];B=R/'docs/research/100bit-spend-path-20261013';H=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
ap=argparse.ArgumentParser();ap.add_argument('--revision',default='0e82f19aa985abe3e419bf1be7ce4212e8387b18');ap.add_argument('--check',action='store_true');args=ap.parse_args();rev=subprocess.check_output(['git','-C',str(R),'rev-parse',args.revision],text=True).strip();old=B/'tools/tx1-caller-extraction-kit/input-accumulator';p=json.loads((old/'source-pins.json').read_text());out=[]
for c in p['cuts']:
 raw=subprocess.check_output(['git','-C',str(R),'show',rev+':'+c['path']]);b=(old/'fragments'/f"{c['name']}.rs").read_bytes();assert sha(b)==c['sha256'],c['name'];
 if b not in raw:
  assert c['name']=='verify_observed',c['name'];out.append({'name':c['name'],'path':c['path'],'old_sha256':sha(b),'status':'changed actual body extracted and explicitly bound by new verify-prefix model; old opaque boundary not reused','new_sha256':json.loads((H/'input/source-pins.json').read_text())['cuts'][2]['sha256']});continue
 start=raw.index(b);out.append({**c,'source_file_sha256':sha(raw),'start_byte':start,'end_byte_exclusive':start+len(b),'start_line':raw[:start].count(b'\n')+1,'unchanged_sha256':sha(b)})
# Actual accepted Prefix::parse and all wire dependencies; no staged parse body.
wire=B/'tools/prefix-aggregate-extraction-kit';wp=json.loads((wire/'source-pins.json').read_text())
spec=importlib.util.spec_from_file_location('prefix_cuts',wire/'extract.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);fresh=m.outputs();fp=json.loads(fresh['source-pins.json']);assert fresh['lib.rs']==(wire/'lib.rs').read_bytes()
assert [(c['name'],c['path'],c['sha256']) for c in fp['declaration_cuts']]==[(c['name'],c['path'],c['sha256']) for c in wp['declaration_cuts']]
for path,h in fp['source_files'].items():assert sha(subprocess.check_output(['git','-C',str(R),'show',rev+':'+path]))==h
wirecuts=fp['declaration_cuts']
record={'revision':rev,'accepted_tx1_revision':p['revision'],'unchanged_tx1_cuts':out,'wire_cuts':wirecuts,'wire_source_files':fp['source_files'],'wire_lib_sha256':sha(fresh['lib.rs']),'rule':'Exact declaration bytes must occur in current git source; full enclosing source files rehashed. Current prefix extraction is fe80; later authorized transcript-only query trace rewrite does not change these declarations.'}
raw=(json.dumps(record,indent=2,sort_keys=True)+'\n')
if args.check:assert(H/'current-source-repin.json').read_text()==raw
else:(H/'current-source-repin.json').write_text(raw)
print(json.dumps({'revision':rev,'unchanged_tx1_cuts':len(out),'wire_cuts':len(wirecuts)}))
