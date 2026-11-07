"""Recover direct archived package configurations with command-to-LLBC source links."""
from pathlib import Path
import json,subprocess,hashlib,lzma,collections
E=Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest()
d=json.load(open(E/'NML_INPUT_MAP.json'));files=subprocess.check_output(['git','ls-tree','-r','--name-only','HEAD','docs/research/100bit-spend-path-20261013/evidence','evidence'],text=True).splitlines()
proc=subprocess.Popen(['git','cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
def blob(p):
 proc.stdin.write(('HEAD:'+p+'\n').encode());proc.stdin.flush();h=proc.stdout.readline().split();b=proc.stdout.read(int(h[2]));assert proc.stdout.read(1)==b'\n';return b
supp=[]
for g in d['groups']:
 if not g['archive_sources'] or g['mappings']:continue
 packets={a['manifest']['path'].split('/evidence/')[0]+'/evidence/'+a['manifest']['path'].split('/evidence/')[1].split('/')[0] if '/evidence/' in a['manifest']['path'] else '/'.join(a['manifest']['path'].split('/')[:2]) for a in g['archive_sources']}
 ps=[p for p in files if any(p.startswith(q+'/') for q in packets)]
 commands=[];llbc=[]
 for p in ps:
  if p.endswith(('.llbc','.llbc.xz')):
   try:
    raw=blob(p);doc=json.loads(lzma.decompress(raw) if p.endswith('.xz') else raw);t=doc['translated'];contents={sha(f['contents'].encode()) for f in t.get('files',[]) if f and isinstance(f.get('contents'),str)}
    llbc.append(dict(path=p,git_blob=subprocess.check_output(['git','rev-parse','HEAD:'+p],text=True).strip(),contents=contents,options=t.get('options',{})))
   except (ValueError,KeyError):pass
  if not p.endswith(('command.json','receipt.json','environment.json')):continue
  try:raw=blob(p);x=json.loads(raw)
  except (ValueError,UnicodeDecodeError):continue
  cmd=x.get('command') if isinstance(x,dict) else x
  if not isinstance(cmd,list) or not all(isinstance(v,str) for v in cmd):continue
  for i,v in enumerate(cmd):
   if v.endswith('/charon') or ('aeneas' in Path(v).name and '-namespace' in cmd):
    commands.append(dict(path=p,sha256=sha(raw),git_blob=subprocess.check_output(['git','rev-parse','HEAD:'+p],text=True).strip(),command=cmd[i:],cwd=x.get('cwd') if isinstance(x,dict) else None));break
 acs=[c for c in commands if '-namespace' in c['command'] and c['command'][c['command'].index('-namespace')+1] in g['namespace']]
 recovered=[]
 for ac in acs:
  llbcname=Path(ac['command'][-1]).name
  for cc in [c for c in commands if '--dest-file' in c['command'] and Path(c['command'][c['command'].index('--dest-file')+1]).name==llbcname]:
   for src in g['archive_sources']:
    linked=[l for l in llbc if Path(l['path'].removesuffix('.xz')).name==llbcname and src['sha256'] in l['contents'] and all([cc['command'][j+1] for j,v in enumerate(cc['command'][:-1]) if v==flag]==l['options'].get(opt,[]) for flag,opt in [('--start-from','start_from'),('--include','include'),('--opaque','opaque')])]
    if not linked:continue
    recovered.append(dict(archive_manifest=src['manifest'],archive_input=src,archive_llbc={k:v for k,v in linked[0].items() if k!='contents'},receipt_paths=[cc['path'],ac['path']],receipt_git_blob=cc['git_blob'],receipt_sha256=cc['sha256'],aeneas_receipt=ac,namespace=g['namespace'][0],roots=[cc['command'][i+1] for i,v in enumerate(cc['command'][:-1]) if v=='--start-from'],reference_sha256=src['sha256'],source=dict(git_blob=src['git_blob'],paths=[src['input_path']],bytes=len(blob(src['input_path']))),charon_command=cc['command'],aeneas_command=ac['command'],outputs={},toolchain='nightly-2026-09-17',basis='Exact command output LLBC basename + LLBC embedded full input SHA256 matches archived package input; same producing packet. Executables will use mandated NCO pins.'))
 g['mappings'].extend(recovered)
 if recovered:g['status']='RECOVERED_LLBC_LINKED_PACKAGE';supp.append(dict(group=g['group'],configurations=len(recovered)))
(E/'NML_INPUT_MAP.json').write_text(json.dumps(d,indent=2)+'\n')
print(json.dumps(dict(additional_groups=supp)))
