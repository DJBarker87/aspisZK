#!/usr/bin/env python3
"""Read-only transitive project source/object provenance audit, beyond one Lean root."""
import pathlib,subprocess,json,hashlib,re,sys
root=pathlib.Path(__file__).resolve().parents[2];e=root/'evidence/pv-srcid3-20261026';rev=subprocess.check_output(['git','rev-parse','research'],text=True).strip()
paths=subprocess.check_output(['git','ls-tree','-r','--name-only',rev],cwd=root,text=True).splitlines();paths=[p for p in paths if p.endswith('.lean')]
manifest=json.loads(subprocess.check_output(['git','show',rev+':evidence/envj-rebuild-20261026/EJR_final-inventory.json'],cwd=root,text=True));selected={r['module'].replace('/','.'):r['sha256'] for r in manifest['selected'] if r['workspace']=='joint'}
library_profiles=json.loads(subprocess.check_output(['git','show',rev+':evidence/envj-rebuild-20261026/EJR_library-source-provenance.json'],cwd=root,text=True))
selected.update({r['module'].replace('/','.'):r['source_sha256'] for r in library_profiles})
# The older Fmt archive has a type axiom; the existing repaired profile is required.
selected['Aeneas.Std.Core.Fmt']='daeafff88224be0870aadb6c3bad73ae7c9375c2de9bbceb177ed2d183d6bdc5'
cache={};rows={};external=set();visiting=set();branchbase=root/'docs/research/v8-r0-zk-20261009/lean'

def lean_imports(data):
 text=data.decode();out=[];i=0;depth=0;string=False
 while i<len(text):
  c=text[i];pair=text[i:i+2]
  if depth:
   if pair=='/-':depth+=1;i+=2;continue
   if pair=='-/':depth-=1;i+=2;continue
   out.append('\n' if c=='\n' else ' ');i+=1;continue
  if string:
   if c=='\\':i+=2;out.append(' ');continue
   if c=='"':string=False
   out.append('\n' if c=='\n' else ' ');i+=1;continue
  if pair=='/-':depth=1;i+=2;continue
  if pair=='--':
   j=text.find('\n',i);i=len(text) if j<0 else j;continue
  if c=='"':string=True;out.append(' ');i+=1;continue
  out.append(c);i+=1
 cleaned=''.join(out);imports=[]
 for line in cleaned.splitlines():
  m=re.match(r'^\s*(?:(?:public|private|meta)\s+)*import\s+(.+)',line)
  if m:imports.extend(m.group(1).split())
 return imports

def blob(p):
 if p not in cache:cache[p]=subprocess.check_output(['git','show',rev+':'+p],cwd=root)
 return cache[p]
def sha(b):return hashlib.sha256(b).hexdigest()
def visit(m):
 if m in rows or m in external or m in visiting:return
 visiting.add(m)
 suffix=m.replace('.','/')+'.lean';canonical='docs/research/v8-r0-zk-20261009/lean/'+suffix
 hits=[p for p in paths if p.endswith('/'+suffix)]
 bp=branchbase/suffix
 branch=m.startswith('R1Z.PV_Src_') and bp.exists()
 if not hits and not branch:external.add(m);return
 if canonical in hits:p=canonical
 else:
  clean=[p for p in hits if '/lean/' in p and '/evidence/' not in p and '/lean-candidates/' not in p]
  chosen=clean or [p for p in hits if sha(blob(p))==selected.get(m)] or hits
  p=sorted(chosen)[0] if chosen else None
 data=bp.read_bytes() if branch else blob(p)
 info=dict(module=m,source_path=str(bp.relative_to(root)) if branch else p,source_sha256=sha(data),research_source_exists=bool(hits),research_source_path=p,research_source_sha256=sha(blob(p)) if p else None,all_research_candidates=[dict(path=q,sha256=sha(blob(q))) for q in hits])
 info['source_matches_research']=p is not None and data==blob(p)
 info['imports']=lean_imports(data);rows[m]=info
 for d in info['imports']:visit(d)
for p in sorted((branchbase/'R1Z').glob('PV_Src_*.lean')):visit('R1Z.'+p.stem)
mods=sorted(set(rows)|external)
code='''import pathlib,json,hashlib
h=pathlib.Path('/home/dombarker/project-offloads');j=h/'aspis-joint-20261019';env=json.loads((h/'r1-privacy-build-integration-20261019/env/J.json').read_text());roots=[str(j/'objects')]+env['LEAN_PATH'].split(':');out=[]
for m in MODS:
 x={'module':m};rel=m.replace('.','/')
 for kind,ext,rs in [('object','.olean',roots),('host_source','.lean',[str(j/'sources')])]:
  found=next((pathlib.Path(r)/(rel+ext) for r in rs if (pathlib.Path(r)/(rel+ext)).is_file()),None)
  x[kind+'_path']=str(found) if found else None;x[kind+'_sha256']=hashlib.sha256(found.read_bytes()).hexdigest() if found else None;x[kind+'_bytes']=found.stat().st_size if found else None
 out.append(x)
print(json.dumps(out))
'''.replace('MODS',repr(mods))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -'],input=code,text=True,capture_output=True,check=True);objects={r['module']:r for r in json.loads(r.stdout)}
for m,r in rows.items():r.update(objects[m]);r['host_source_matches_research']=r['research_source_sha256'] is not None and r['host_source_sha256']==r['research_source_sha256']
out=dict(research_revision=rev,branch_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),project_modules=list(rows.values()),external_modules=[objects[m] for m in sorted(external)],missing_objects=[m for m,x in objects.items() if not x['object_path']],scope='Project sources recursively resolved across all repository roots; package source closure not claimed',merge_gate=False)
(e/(sys.argv[1] if len(sys.argv)>1 else 'resume6-full-closure.json')).write_text(json.dumps(out,indent=2)+'\n');print('project modules',len(rows),'external module roots',len(external),'missing',len(out['missing_objects']),'source/research mismatches',sum(not x['source_matches_research'] for x in rows.values()))
