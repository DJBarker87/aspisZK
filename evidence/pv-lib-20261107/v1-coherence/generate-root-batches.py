"""Partition the root UNION, never the source/object cohort. Arrays only vary."""
import pathlib,json,lzma,hashlib
E=pathlib.Path(__file__).parent;roots=json.loads((E/'AUDIT_ROOTS.json').read_text())['roots'];report=json.loads(lzma.decompress((E/'ROOT_IMPORT_PREFLIGHT.json.xz').read_bytes()));base=pathlib.Path('lean/PV_LIB_SPEC_RawAuditSession19.lean').read_text();a=base.index('    (#[`');z=base.index('\n  let env ←',a);body=base[:a]+'    (v1Modules, v1Roots)'+base[z:];batches=[]
for k in range(0,len(roots),125):
 rs=roots[k:k+125];ms=sorted({report['root_providers'][r] for r in rs});name=f'PV_LIB_V1_RawAuditBatch{k//125:02d}';decls=['-- V1_ARRAYS_BEGIN']
 for label,values in [('Modules',ms),('Roots',rs)]:
  names=[]
  for j in range(0,len(values),64):
   n='v1'+label+str(j//64);names.append(n);decls.append('@[noinline] private def '+n+' : Array Name := #['+', '.join('`'+v for v in values[j:j+64])+']')
  decls.append('@[noinline] private def v1'+label+' : Array Name := '+' ++ '.join(names))
 decls.append('-- V1_ARRAYS_END');s=body.replace('open Lean Elab Command\n','open Lean Elab Command\n\n'+'\n'.join(decls)+'\n');p=pathlib.Path('lean',name+'.lean');p.write_text(s);batches.append(dict(name=name,modules=ms,roots=rs,source_sha256=hashlib.sha256(s.encode()).hexdigest()))
assert [r for b in batches for r in b['roots']]==roots
(E/'ROOT_BATCHES.json').write_text(json.dumps(dict(cohort=report['source_revision'],same_object_mapping=True,root_count=len(roots),batches=batches),indent=2)+'\n');print(len(batches),'root batches;',len(roots),'roots; one object mapping')
