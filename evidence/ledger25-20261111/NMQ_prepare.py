from pathlib import Path
import json,lzma,hashlib,re
E=Path(__file__).resolve().parent;P=E.parent/'ledger24-20261110';Q=E.parent/'tx2-entry5-20261110';R=E.parent/'root-transport-20261110'
C='/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NMQ_20261111'
def raw(p):
 if p.exists():return p.read_bytes()
 return lzma.decompress(Path(str(p)+'.xz').read_bytes())
def J(p):return json.loads(lzma.decompress(p.read_bytes()) if p.suffix=='.xz' else raw(p))
roots=set(J(P/'NLX_AUDIT_ROOTS.json')['roots']);expected={};seeds=[];paths=[];conflicts=[]
for folder,pre in [(P,'NLX'),(Q,'NMN'),(R,'NMF')]:
 rp=folder/(pre+'_AUDIT_ROOTS.json')
 if rp.exists():roots.update(J(rp).get('roots',[]))
 for l in raw(folder/(pre+'_EXPECTED_IMPORTS.jsonl')).decode().splitlines():
  x=json.loads(l);m=x['module'];v=x['imports']
  if m in expected and expected[m]!=v:conflicts.append(m)
  expected[m]=v
 ex=J(folder/(pre+'_EXPORT.json'));base=ex.get('export',ex.get('path',ex.get('directory')))
 for row in ex['files']:
  src=row.get('path',base+'/'+row.get('name',''));seeds.append(dict(tag=pre,path=src,relative=src[len(base)+1:],sha256=row['sha256'],bytes=row['bytes']))
 paths+=[C+'/'+pre+'_seed']
paths += J(P/'NLX_PATHS.json')+J(Q/'NMN_ENV.json')['LEAN_PATH'].split(':')+J(R/'NMF_ENV.json')['LEAN_PATH'].split(':')
# Keep predecessor batch shapes that completed, including the pre-split L023 replacement.
old=J(P/'NLX_AUDIT_ROOTS.json');plan=J(P/'NLX_AUDIT_GROUPS.json')
groups=[old['groups'][r['group']] for r in plan['required']];oldroots={r for g in groups for r in g};extra=sorted(roots-oldroots);groups+=[extra]
assert len(groups)==33 and len(oldroots)==11370 and not conflicts
for n,x in [('AUDIT_ROOTS',dict(roots=sorted(roots),groups=groups)),('AUDIT_MODULES',[['NMQ_COMBINED_IMPORT']]*len(groups)),('SEED_INPUTS',seeds),('PATHS',list(dict.fromkeys(paths))),('EXPECTED_CONFLICTS',conflicts)]:
 (E/('NMQ_'+n+'.json')).write_text(json.dumps(x,indent=1)+'\n')
(E/'NMQ_COMBINED_IMPORT.lean').write_text('import NLX_COMBINED_IMPORT\nimport NMN_COMBINED_IMPORT\nimport NMF_COMBINED_IMPORT\nimport RPx_Deployed\n#print axioms NMN_064.root\n#print axioms NMF_GameRoot.root0_or_existing_collision\n#print axioms AspisR1.RPx_Deployed.deployed\n')
for n in ['Driver','OwnerStatements']:(E/('NMQ_'+n+'.lean')).write_text((P/('NLX_'+n+'.lean')).read_text().replace('NLX_','NMQ_'))
s='import NMQ_COMBINED_IMPORT\nset_option pp.proofs false\n'
for n in ['NMN_064.root','NMN_064.RowSpec','NMN_064.Domain','NMN_064.G','NMN_064.Law','NMN_064.Native','NMN_Headline.root0_or_collision','NMF_GameRoot.root0_or_existing_collision']:
 s+='#print '+n+'\n'
s+='#print axioms NMN_064.root\n#print axioms NMF_GameRoot.root0_or_existing_collision\n'
(E/'NMQ_HypothesisReview.lean').write_text(s)
for p in E.glob('NMQ_*.lean'):expected[p.stem]=list(dict.fromkeys(['Init']+re.findall(r'^import ([\w.]+)',p.read_text(),re.M)))
(E/'NMQ_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=m,imports=v))+'\n'for m,v in sorted(expected.items())))
# Owned client adaptations; shared infrastructure is copied unchanged.
for n in ['run','batch','setup','pin','scope40']:
 s=(P/('NLX_'+n+'.py')).read_text().replace('NLX_','NMQ_').replace('codex-cx-ledger24-20261110', 'codex-cx-ledger8-cache-20261104/NMQ_20261111')
 s=s.replace('NMQ_20261110','NMQ_20261111').replace("E.parent/'ledger23-20261110/NLS_CLOSURE_PINS.json.xz'","E.parent/'ledger24-20261110/NLX_CLOSURE_PINS.json.xz'")
 if n=='setup':
  a=s.index('closure_inputs=[]');b=s.index("code='''",a)
  s=s[:a]+"closure_inputs=[]\nfor folder,pre in [(E.parent/'ledger24-20261110','NLX'),(E.parent/'tx2-entry5-20261110','NMN'),(E.parent/'root-transport-20261110','NMF')]:\n p=folder/(pre+'_CLOSURE_PINS.json.xz');sha=(folder/(pre+'_CLOSURE_PINS.json.sha256')).read_text().strip();closure_inputs.append(dict(hex=p.read_bytes().hex(),sha256=sha))\n"+s[b:]
 if n=='run':
  # Preserve the exact optimized ledger24 raw ax2 binary. It reads legacy-named manifest aliases privately.
  s=s.replace("if kind=='lean':\n", "if kind=='lean':\n",1)
  s=s.replace("if target=='NMQ_OwnerStatements':files['NMQ_AUDIT_ROOTS.json']=(E/'NMQ_AUDIT_ROOTS.json').read_text()", "if target=='NMQ_OwnerStatements':files['NMQ_AUDIT_ROOTS.json']=(E/'NMQ_AUDIT_ROOTS.json').read_text()")
  s=s.replace("'NMQ_generated/NMQ_ProofDriver.lean',",'')
  s=s.replace("B+'/NMQ_objects']", "B+'/NMQ_objects']")
  # Every scope: host-share check, before reservation/upload/submission. No launch on refusal.
  marker='for disk_retry in range(7):'
  share='''while True:
 r=ssh('python3',"""import subprocess,pathlib,json
units=subprocess.check_output(['systemctl','--user','list-units','--type=scope','--state=running','--no-legend','--no-pager'],text=True).splitlines();found=[]
for line in units:
 unit=line.split()[0];cg=subprocess.check_output(['systemctl','--user','show',unit,'-p','ControlGroup','--value'],text=True).strip();p=pathlib.Path('/sys/fs/cgroup'+cg)
 try:pids=(p/'cgroup.procs').read_text().split()
 except FileNotFoundError:continue
 for pid in pids:
  try:cwd=str(pathlib.Path('/proc/'+pid+'/cwd').resolve(strict=True))
  except (FileNotFoundError,PermissionError,ProcessLookupError):continue
  if cwd.startswith('/home/dombarker/project-offloads/codex-cx-'):found.append(unit);break
print(json.dumps(dict(scopes=found,count=len(found))))
""")
 assert r.returncode==0,r.stderr
 share_info=json.loads(r.stdout)
 with (E/'NMQ_ATTEMPTS.jsonl').open('a')as f:f.write(json.dumps(dict(attempt=a,event='share_check' if share_info['count']<2 else 'wait',reason='Stream A scope share',host=share_info))+'\\n')
 if share_info['count']<2:break
 time.sleep(180)
'''
  s=s.replace(marker,share+marker)
 if n=='batch':
  s=s.replace("'NMQ_native/'+('NMQ_Driver' if mode.startswith('scan') else 'NMQ_ProofDriver')", "'NMQ_native/'+('NMQ_Driver' if mode.startswith('scan') else 'NMQ_ProofDriver')")
 (E/('NMQ_'+n+'.py')).write_text(s)
print(json.dumps(dict(roots=len(roots),new_roots=len(extra),groups=len(groups),seeds=len(seeds),conflicts=conflicts)))
