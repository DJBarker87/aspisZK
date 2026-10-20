#!/usr/bin/env python3
"""Compare retained adapter cut and all Rust files labelled in its extraction."""
import hashlib,importlib.util,json,re,subprocess
from pathlib import Path
E=Path(__file__).resolve().parent; ROOT=E.parents[4];R=ROOT/'docs/research/100bit-spend-path-20261013'
sha=lambda b:hashlib.sha256(b).hexdigest()
spec=importlib.util.spec_from_file_location('cut',R/'tools/adapter-reconstruct-extraction-kit/extract.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
pins=json.loads((R/'tools/adapter-reconstruct-extraction-kit/source-pins.json').read_text())
rev=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip();src=(ROOT/m.SOURCE).read_text();cuts=[]
for old in pins['cuts']:
 s,lo,hi=m.cut(src,old['name']);h=sha(s.encode());cuts.append(dict(name=old['name'],current_start_line=lo,current_end_line=hi,sha256=h,pinned_sha256=old['sha256'],equal=h==old['sha256']))
# Keep full diffs: these establish exactly where nonidentical files changed.
fun=(R/'lean/extracted-adapter-reconstruct-20261016/AspisR1AdapterReconstruct/Funs.lean').read_text()
typ=(R/'lean/extracted-adapter-reconstruct-20261016/AspisR1AdapterReconstruct/Types.lean').read_text()
paths=sorted(set(re.findall("Source: '(crates/[^']+)'",fun+typ)))
rs=[]
for p in paths:
 old=subprocess.check_output(['git','show',pins['source_revision']+':'+p],cwd=ROOT);new=(ROOT/p).read_bytes()
 rs.append(dict(path=p,pinned_sha256=sha(old),current_sha256=sha(new),equal=old==new))
diff=subprocess.check_output(['git','diff','--unified=0',pins['source_revision'],'--',*paths],cwd=ROOT)
(E/'dependency-diff.patch').write_bytes(diff)
obj=dict(source_revision=rev,pinned_revision=pins['source_revision'],cuts=cuts,dependencies=rs,dependency_diff_sha256=sha(diff))
(E/'source-comparison.json').write_text(json.dumps(obj,indent=2)+'\n')
assert all(c['equal'] for c in cuts)
print(json.dumps(obj,indent=2))
