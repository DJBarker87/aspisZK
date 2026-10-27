from pathlib import Path
import json,hashlib,sys
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';E=R/'evidence/pv-reach-20261027/resume5'
rows=[]
for a,b,label in [(3,3,'Exceptional5'),(0,36,'Half5A'),(37,73,'Half5B')]:
 t='import R1Z.PV_RE_ComposedContextsGenerator5\n'
 for i in range(a,b+1):
  chunk=(L/f'PV_RE_ComposedChunk{i:03}.lean').read_text().split('\n',1)[1]
  chunk=chunk.replace(f'PV_RE_ComposedSuffix{i:03}',f'PV_RE_ComposedSuffix5_{i:03}').replace('pv_composed_source_contexts','pv_composed5_source_contexts')
  t+='\n'+chunk
 p=L/f'PV_RE_{label}.lean';assert p.read_text()==t
 rows.append(dict(module='R1Z/'+p.stem,chunks=list(range(a,b+1)),sha256=hashlib.sha256(t.encode()).hexdigest(),next_consumer='PV_RE_FinalAudit5A/B then FinalAudit5C'))
(E/'group-manifest.json').write_text(json.dumps(rows,indent=2)+'\n');print('3 groups validated; scalar matcher guarded before reduction')
