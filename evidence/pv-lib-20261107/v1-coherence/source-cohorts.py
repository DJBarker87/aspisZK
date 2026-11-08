"""Compare merged declarations' source files with all supplying input commits."""
import json,pathlib,subprocess,hashlib
E=pathlib.Path('evidence/pv-lib-20261107/v1-coherence');i=json.loads((E/'INVENTORY.json').read_text());out={};pins=dict(A='fbc60bd811d',B='43fa17cd4a5',C='87e34a2b2af')
for lane,rev in pins.items():
 tree=subprocess.check_output(['git','ls-tree','-r',rev,'lean'],text=True);blobs={l.split('\t')[1]:l.split()[2] for l in tree.splitlines()}
 for m,v in i['sources'].items():
  if v['path'] in blobs:
   b=subprocess.check_output(['git','show',rev+':'+v['path']]);h=hashlib.sha256(b).hexdigest();out.setdefault(m,[]).append(dict(lane=lane,revision=rev,path=v['path'],git_blob=blobs[v['path']],sha256=h,equals_merged=h==v['sha256']))
(E/'SOURCE_COHORTS.json').write_text(json.dumps(out,indent=2)+'\n')
changed=[(m,v) for m,vs in out.items() for v in vs if not v['equals_merged']];print('source cohort comparisons',sum(map(len,out.values())),'differences',len(changed));print(changed[:5])
