"""Resolve the actual installed dictionary closure, in lead-authority order."""
import pathlib,json,subprocess,hashlib,re
R=pathlib.Path(__file__).resolve().parents[2];E=R/'evidence/pv-reach-20261027/resume9';A=R/'evidence/pv-reach-20261027/resume7'
inv=json.loads((A/'EJR_final-inventory.json').read_text());pins={}
for r in sorted(inv['selected'],key=lambda r:r.get('workspace')=='joint'):
 if r.get('resolution'):pins[r['module'].replace('/','.')]=r
freeze=json.loads((A/'final-source-freeze.json').read_text());fr={r['module']:r for r in freeze['sources']}
ext={r['module'].replace('/','.') for r in json.loads((A/'external-object-manifest.json').read_text())}
tracked=subprocess.check_output(['git','ls-files','*.lean','*.lean.txt'],text=True).splitlines();L='docs/research/v8-r0-zk-20261009/lean/'
aliases={r['module']:r['path'] for r in json.loads((E.parent/'extraction-pins.json').read_text())}
# Committed replay dry8 snapshots explicitly name their module in the filename.
for q in tracked:
 if q.startswith('evidence/replay-dry8-20261026/RPz7_'):
  name=pathlib.Path(q).stem.removeprefix('RPz7_').replace('_','.')
  aliases.setdefault(name,q)
for q in tracked:
 if q.startswith('evidence/pv-rw19-resume-20261026/retained-source-inputs/') and q.endswith('.lean.txt'):
  aliases[pathlib.Path(q).name.removesuffix('.lean.txt')]=q
# Rebuild2 authority supplements the initial final inventory.
for q in (R/'evidence/envj-rebuild2-20261026').glob('*payload.json'):
 x=json.loads(q.read_text())
 for z in x.get('rows',[]):
  if all(k in z for k in ['module','blob','revision','path','source_sha256']):
   pins.setdefault(z['module'].replace('/','.'),dict(sha256=z['source_sha256'],resolution={k:z[k] for k in ['blob','revision','path']},record=str(q.relative_to(R))))
conflicts=[]
head=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();rows={};order=[]
def git(ref):return subprocess.check_output(['git','show',ref])
def visit(m,parent=None):
 if m in rows or m in ext:return
 p=aliases.get(m,L+m.replace('.','/')+'.lean')
 if p not in tracked and m not in pins and m not in fr:
  hits=[x for x in tracked if pathlib.Path(x).name==m.split('.')[-1]+'.lean' and not x.startswith('evidence/')]
  suffix=[x for x in hits if x.endswith(m.replace('.','/')+'.lean')]
  if len(suffix)==1:hits=suffix
  canonical=[x for x in suffix if '/lean/prover-rw-20261023/' in x]
  if len(canonical)==1:hits=canonical
  siblings=[x for x in hits if parent and pathlib.Path(x).parent==pathlib.Path(parent).parent]
  if len(siblings)==1:hits=siblings
  assert len(hits)==1,('ambiguous HEAD module',m,len(hits),hits[:5])
  p=hits[0]
 if m in pins:
  q=pins[m];z=q['resolution'];data=git(z['blob']);authority='EJR';path=z['path'];rev=z['revision'];blob=z['blob'];assert hashlib.sha256(data).hexdigest()==q['sha256']
  if p in tracked and not p.startswith('evidence/replay-dry8-') and git(head+':'+p)!=data: conflicts.append(dict(module=m,selected_path=path,selected_sha256=hashlib.sha256(data).hexdigest(),tracked_path=p,tracked_sha256=hashlib.sha256(git(head+':'+p)).hexdigest(),ruling='h5 prime: EJR/freeze wins'))
 elif m in fr:
  q=fr[m];path=q['path'];rev=freeze['revision'];data=git(rev+':'+path);blob=subprocess.check_output(['git','rev-parse',rev+':'+path],text=True).strip();authority='freeze';assert hashlib.sha256(data).hexdigest()==q['sha256']
  if p in tracked and not p.startswith('evidence/replay-dry8-') and git(head+':'+p)!=data: conflicts.append(dict(module=m,selected_path=path,selected_sha256=hashlib.sha256(data).hexdigest(),tracked_path=p,tracked_sha256=hashlib.sha256(git(head+':'+p)).hexdigest(),ruling='h5 prime: EJR/freeze wins'))
 else:
  assert p in tracked,('unresolved',m);path=p;rev=head;data=git(head+':'+p);blob=subprocess.check_output(['git','rev-parse',head+':'+p],text=True).strip();authority='h5'
 text=data.decode()
 # Strip nested Lean block comments before scanning module headers.
 clean=[];depth=0;i=0
 while i<len(text):
  if text[i:i+2]=='/-':depth+=1;i+=2
  elif depth and text[i:i+2]=='-/':depth-=1;i+=2
  else:
   if not depth:clean.append(text[i])
   i+=1
 imports=[name for line in re.findall(r'^(?:(?:public|private|meta)[ \t]+)*import[ \t]+([^\n]+)', ''.join(clean), re.M) for name in line.split('--')[0].split() if re.fullmatch(r'[A-Za-z0-9_.]+',name)]
 rows[m]=dict(module=m,authority=authority,path=path,revision=rev,blob=blob,sha256=hashlib.sha256(data).hexdigest(),imports=imports)
 for i in imports:visit(i,path)
 order.append(m)
visit('R1Z.PV_Src_NativeInput')
visit('R1Z.PV_Src_PublicDeploymentAssociation')
visit('R1Z.PV_Src_ExternalAssociation')
visit('R1Z.PV_Src_RecordAssociation')
visit('R1Z.PV_Src_FrozenFixtures')
(E/'native-source-cohort-conflicts.json').write_text(json.dumps(conflicts,indent=2)+'\n')
extra={r['module']:r for r in json.loads((A/'additional-freeze-matches.json').read_text())} if (A/'additional-freeze-matches.json').exists() else {}
for m,r in rows.items():
 if m in extra:r['authority']='freeze';r['authority_record']=extra[m]['authority_record']
(E/'native-project-closure.json').write_text(json.dumps([rows[m] for m in order],indent=2)+'\n')
print('closure',len(rows),'h5',sum(r['authority']=='h5' for r in rows.values()))
for m in order:
 if rows[m]['authority']=='h5':print(m)
