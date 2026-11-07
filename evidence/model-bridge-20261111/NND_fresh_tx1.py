"""Token-checked fresh frozen body replay on coherent canonical type owners.
Never replaces a differing token stream by a historical definition.
"""
from pathlib import Path
import re,json,hashlib,subprocess,difflib
E=Path(__file__).resolve().parent
rev=subprocess.check_output(['git','rev-parse','codex/cx-tx1-owned-20261107'],text=True).strip()
sha=lambda b:hashlib.sha256(b).hexdigest()
rows=json.loads((E/'NND_REUSE.json').read_text())
def read(path):
 b=subprocess.check_output(['git','show',rev+':'+path]);dst=E/'NND_reuse'/'NMT_fresh'/path.removeprefix('evidence/tx1-owned-20261111/')
 dst.parent.mkdir(parents=True,exist_ok=True)
 if dst.exists():assert dst.read_bytes()==b
 else:dst.write_bytes(b)
 r=dict(revision=rev,path=path,sha256=sha(b),use='immutable fresh frozen extraction provenance; no templates imported')
 if r not in rows:rows.append(r)
 return b.decode()
adapter=json.loads(Path('docs/research/100bit-spend-path-20261013/lean/AdapterRw-emission-adapter.json').read_text())
old=Path('docs/research/100bit-spend-path-20261013/lean/AdapterRwModel.lean').read_text()
def decl(text,name):
 m=re.search(r'^def '+re.escape(name)+r'(?:\s|$)',text,re.M);assert m,name
 rest=text[m.start():];n=rest.find('\n/-- ')
 if n<0:rest=rest[:rest.rfind('\nend ')]
 else:rest=rest[:n]
 return rest.strip()
report=[]
for family,name,mod in [('first','first_decoded','NND_FreshFirstDecoded'),('stage1_owned','r1_pool_adapter.owned.stage1_owned','NND_FreshStage1')]:
 raw=read('evidence/tx1-owned-20261111/NMT_extracted/'+family+'/raw/NMT_'+family+'/Funs.lean')
 pins=json.loads(read('evidence/tx1-owned-20261111/NMT_extracted/'+family+'/NMT_PINS.json'))
 assert pins['frozen_revision']=='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387' and pins['aeneas_exit']==0
 read('evidence/tx1-owned-20261111/NMT_extracted/'+family+'/NMT_DECLARATIONS.json')
 body=decl(raw,name);body=body.replace('def '+name,'def fresh (ops : Ops)',1)
 changes=[]
 for symbol,slot in sorted(adapter['boundaries'].items(),key=lambda x:-len(x[0])):
  pattern=r'(?<![\w.])'+re.escape(symbol)+r'(?![\w.])'
  body,n=re.subn(pattern,'ops.'+slot,body)
  if n:changes.append(dict(symbol=symbol,replacement='ops.'+slot,count=n))
 threaded=['first_decoded','observer','SolanaDigest.Insts.Aspis_coreDigestDigest32',*adapter['threaded_ops'] ] if 'threaded_ops' in adapter else []
 # The adapter manifest calls the transitive-consumer list ops_consumers.
 consumers=next((v for k,v in adapter.items() if isinstance(v,list) and 'first_decoded' in v),[])
 threaded=sorted(set(consumers+['first_decoded','observer','SolanaDigest.Insts.Aspis_coreDigestDigest32']),key=len,reverse=True)
 for symbol in threaded:
  if symbol==name:continue
  pattern=r'(?<![\w.])'+re.escape(symbol)+r'(?![\w.])'
  body,n=re.subn(pattern,'('+symbol+' ops)',body)
  if n:changes.append(dict(symbol=symbol,replacement='('+symbol+' ops)',count=n))
 canonical=decl(old,name).replace('def '+name,'def fresh',1)
 tokens=lambda s:re.findall(r'\w+|[^\s\w]',s)
 eq=tokens(body)==tokens(canonical)
 r=dict(family=family,name=name,raw_sha256=sha(raw.encode()),changes=changes,token_equal=eq)
 if not eq:
  r['diff']='\n'.join(difflib.unified_diff(tokens(canonical),tokens(body)))[:10000]
  (E/(mod+'.pending')).write_text(body+'\n')
 else:
  # Token-equal canonical whitespace repairs Aeneas's column68 clipping.
  header='import AdapterRwModel\nset_option autoImplicit false\nnoncomputable section\nnamespace '+mod+'\nopen Aeneas Aeneas.Std Result ControlFlow Error AdapterRw\n'
  if family=='first':
   footer='''
theorem source (ops : Ops)
 (p : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (pub proof : Slice U8) (k : Usize) :
 fresh ops p pub proof k = first_decoded ops p pub proof k := rfl
'''
  else:
   footer='''
/-- Parent body only: the opaque frozen require_zero boundary still needs
its own native/symbolic transport; it is not discharged by this equality. -/
theorem source (ops : Ops) (p : solana_pubkey.Pubkey)
 (a : Slice r1_pool_adapter.owned.OwnedAccount) (d : Slice U8) :
 fresh ops p a d = r1_pool_adapter.owned.stage1_owned ops p a d := rfl
'''
  (E/(mod+'.lean')).write_text(header+canonical+'\n'+footer+'#print axioms source\nend '+mod+'\nend\n')
 report.append(r)
(E/'NND_REUSE.json').write_text(json.dumps(rows,indent=1)+'\n')
(E/'NND_TX1_REPLAY.json').write_text(json.dumps(report,indent=1)+'\n')
print(json.dumps([{k:v for k,v in r.items() if k!='diff'} for r in report]))
