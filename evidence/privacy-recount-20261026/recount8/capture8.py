from pathlib import Path
import subprocess,json,hashlib,os,re,datetime
P=Path(__file__).resolve().parent;B=P.parent
old=json.loads((B/'recount7/pins.json').read_text()); branches=old['branches'].copy();branches.update(research='research',rw='de194795b3',runjoin='codex/pv-runjoin-20261026',b3p6='codex/pv-b3p6-20261028',rjdec='codex/pv-rjdec-20261028',rdb2d='codex/pv-rdb2d-20261028',rdcd3='codex/pv-rdcd3-20261028')
revs=old['revisions'].copy()
for k in ['research','rw','runjoin','b3p6','rjdec','rdb2d','rdcd3']:revs[k]=subprocess.check_output(['git','rev-parse',branches[k]],text=True).strip()
pins=dict(branches=branches,revisions=revs,captured_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),live_snapshots=['runjoin','b3p6','rjdec','rdb2d','rdcd3'],fixed_candidate='de194795b3',worktree_base='19c1bd58b7',policy='Immutable point-in-time heads; later branch progress excluded.',budget=dict(Lean=30,Kani=0,used_Lean=0,used_Kani=0,env_J='61600-61699',consumed_IDs=[]))
(P/'pins.json').write_text(json.dumps(pins,indent=2)+'\n')
manifest=[];cache={};prior={}
for d in ['recount4','recount5','recount6','recount7']:
 for x in json.loads((B/d/'manifest.json').read_text()):
  p=B/d/x['snapshot']
  if p.exists():prior[x['blob']]=p.resolve()
def read(k,path):
 if (k,path) in cache:return cache[k,path]
 q=subprocess.run(['git','show',revs[k]+':'+path],capture_output=True)
 if q.returncode:cache[k,path]=None;return None
 raw=q.stdout;blob=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest();f=prior.get(blob,P/'objects'/(blob+'.txt'))
 if not f.exists():f.parent.mkdir(exist_ok=True);f.write_bytes(raw)
 manifest.append(dict(ref=k,revision=revs[k],path=path,blob=blob,sha256=hashlib.sha256(raw).hexdigest(),snapshot=os.path.relpath(f,P)));cache[k,path]=raw.decode(errors='replace');return cache[k,path]
audit=[];rows=json.loads((B/'recount7/rows7.json').read_text())
active=['research','rw','runjoin','b3p6','rjdec','rdb2d','rdcd3']
for r in rows:
 path,_,decl=r.get('definition','').partition('#');ss=[];missing=[]
 for k in sorted(set(active+[x['ref'] for x in r['definition_witnesses7']])):
  s=read(k,path) if path else None
  if s is None:missing.append(k)
  else:ss.append({**next(x for x in reversed(manifest) if x['ref']==k and x['path']==path),'declaration':decl})
 audit.append(dict(id=r['id'],definition=r.get('definition'),sources=ss,missing=missing,changed_from7=[x['ref'] for x in ss if x['sha256'] not in {y['sha256'] for y in r['definition_witnesses7']}]))
# Sources and explicit worker reports/row packets, not indiscriminate build output.
for k in active:
 paths=subprocess.check_output(['git','ls-tree','-r','--name-only',revs[k],'evidence','docs/research/v8-r0-zk-20261009/lean','design','docs/research/100bit-spend-path-20261013/design'],text=True).splitlines()
 for path in paths:
  worker=bool(re.search(r'evidence/pv-(rdb1|rdb2|rdcd|rdeac|fscan2|2tnv|b3p6|runjoin|rjdec|dlib2|kstub|gate6)',path))
  lean=path.endswith('.lean') and bool(re.search(r'/(PV_(RDB|RDCD|RDEAC|B3P|RunJoin|RJDec|2T|FXM|DL)|PV_B3_)',path))
  selected=worker and (path.endswith('.md') or re.search(r'/(rows/[^/]+|rows|audit|summary|combined-audit|restoration|row-audit|diagnostic-provenance|attempts|pending-replay|final-source-pins|final-source-identity|RESUME-SEQUENCING)\.json$',path))
  if lean or selected:read(k,path)
 for path in ['docs/research/v8-r0-zk-20261009/LOG.md','design/PRIVACY-LEDGER-20261026.md','docs/research/100bit-spend-path-20261013/design/SECURITY-CONTRACT-20261021.md']:read(k,path)
(P/'definition-audit8.json').write_text(json.dumps(audit,indent=1)+'\n');(P/'manifest.json').write_text(json.dumps(manifest,indent=1)+'\n')
print('Captured',len(audit),'row definitions;',len(manifest),'source witnesses;',len(list((P/'objects').glob('*'))),'new objects')
