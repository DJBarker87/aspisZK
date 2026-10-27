"""Exact name/import-only copies for the producer's colliding ownership chain."""
from pathlib import Path
import re,json,hashlib,sys
E=Path(__file__).resolve().parent
roots=[Path('lean'),Path('evidence/leaf-p6-10-20261027'),Path('evidence/leaf-p6-12-20261027')]
paths={};order=[]
def visit(m):
 if m in paths:return
 p=next((r/(m+'.lean') for r in roots if (r/(m+'.lean')).is_file()),None)
 if p is None:raise RuntimeError(m)
 paths[m]=p
 for d in re.findall(r'^import (\S+)',p.read_text(),re.M):
  if d.startswith(('LPl_','LPn_','LPs_CheckDomain')):visit(d)
 order.append(m)
visit('LPs_ExpandDomain');visit('LPs_ProducerTotal')
# Each copied declaration namespace also receives this job's prefix.
replacements=[(m,'LPt_'+m) for m in sorted(paths,key=len,reverse=True)]
replacements += [('LPl_Kit_','LPt_LPl_Kit_'),('LPl_A','LPt_LPl_A'),('LPl_C','LPt_LPl_C'),('LPl_G','LPt_LPl_G'),('LPl.','LPt_LPl.'),('LPl\n','LPt_LPl\n'),('LPn.','LPt_LPn.'),('LPs_CheckDomain','LPt_LPs_CheckDomain'),('LPs_ExpandDomain','LPt_LPs_ExpandDomain'),('LPs_ProducerTotal','LPt_LPs_ProducerTotal'),('core.slice.iter.Windows','LPt_External.core.slice.iter.Windows'),('aspis_core.field.wide_exact.WideExact','LPt_External.aspis_core.field.wide_exact.WideExact'),('aspis_core.r0.domain.FibreIndex','LPt_External.aspis_core.r0.domain.FibreIndex')]
# Prefix every root declaration in FunsExternal, preserving imported library names.
external='\n'.join((roots[1]/n).read_text() for n in ['LPl_Kit_FunsExternal.lean','LPl_Kit_FieldExternal.lean'])
for name in re.findall(r'^def\s+([A-Za-z_][A-Za-z0-9_.]*)',external,re.M):
 if '.' in name:replacements.append((name,'LPt_External.'+name))
# Simultaneous lexical name replacement avoids replacing newly-prefixed names twice.
replacements=dict(replacements)
pattern=re.compile('|'.join(re.escape(x) for x in sorted(replacements,key=len,reverse=True)))
rows=[]
for m in order:
 p=paths[m];src=p.read_text();dst=pattern.sub(lambda hit:replacements[hit[0]],src)
 target=Path('lean')/('LPt_'+m+'.lean')
 if '--check' in sys.argv:assert target.read_text()==dst,target
 else:target.write_text(dst)
 rows.append(dict(original=str(p),module='LPt_'+m,source_sha256=hashlib.sha256(src.encode()).hexdigest(),sha256=hashlib.sha256(dst.encode()).hexdigest()))
(E/'LPt_COPY_PLAN.json').write_text(json.dumps(dict(replacements=replacements,modules=rows),indent=2)+'\n')
print(len(rows),'exact name/import-only copies checked')
