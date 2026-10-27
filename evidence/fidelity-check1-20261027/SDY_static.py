from pathlib import Path
import re,json,hashlib,subprocess
E=Path(__file__).resolve().parent
raw=Path('evidence/extraction-assoc2-20261027/XRj_L013/sources/XRj_generated/XRh_Release/Funs.lean')
s=raw.read_text(); lines=s.splitlines();decl='';hits=[];allwild=[]
for i,l in enumerate(lines):
 if l == 'def' or l.startswith('def '):decl=l[4:].strip() or lines[i+1].strip()
 if re.search(r'let \([^\n]*\b_\b',l):
  block='\n'.join(lines[i:i+8]); row=dict(line=i+1,declaration=decl,binding=l.strip(),context=block)
  allwild.append(row)
  if re.search(r'let \([^)]*,\s*_\s*\)\s*←',l) and re.search(r'(next|index_mut|to_slice_mut|into_iter)',block):hits.append(row)
(E/'SDY_scan.json').write_text(json.dumps(dict(raw=str(raw),sha256=hashlib.sha256(raw.read_bytes()).hexdigest(),line_count=len(lines),method='all tuple let bindings containing underscore; accessor callbacks checked in eight-line context, then manually classified',callback_candidates=hits,all_tuple_wildcards=allwild),indent=2)+'\n')
(E/'SDY_source_pins.json').write_text(json.dumps({'revision':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'frozen_revision':'4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','raw_sha256':hashlib.sha256(raw.read_bytes()).hexdigest()},indent=2)+'\n')
print(json.dumps(hits,indent=2))
