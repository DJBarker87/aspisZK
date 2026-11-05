"""599-row NIM successor; promotions are contingent on the final full gate."""
from pathlib import Path
import json,lzma,hashlib,subprocess,collections,re
E=Path(__file__).resolve().parent;R=E.parents[1]
H=lambda raw:hashlib.sha256(raw).hexdigest()
def get(path):
 p=R/path
 if p.exists():return p.read_bytes()
 return subprocess.check_output(['git','show','HEAD:'+str(path)],cwd=R)
def J(path):
 raw=get(path);return json.loads(lzma.decompress(raw)if str(path).endswith('.xz')else raw)
def put(n,x):
 raw=(json.dumps(x,indent=1,sort_keys=True)+'\n').encode();p=E/n
 if len(raw)>20_000_000:
  p.with_name(p.name+'.xz').write_bytes(lzma.compress(raw,preset=6));p.with_name(p.name+'.sha256').write_text(H(raw)+'\n')
 else:p.write_bytes(raw)
def names(x,allowed):
 mp=J('evidence/ledger12-20261107/NIR_NAMESPACE_MAP.json')
 aliases={}
 for n in allowed:
  parts=n.split('.')
  for i in range(len(parts)-1):aliases.setdefault('.'.join(parts[i:]),set()).add(n)
 out=set()
 def visit(v):
  if isinstance(v,str):
   for token in [v]+re.findall(r'(?<![\w.])[A-Za-z_][\w]*(?:\.[A-Za-z_][\w]*)+',v):
    bits=token.split('.');offset=1 if bits[0]=='AspisR1'else 0
    if bits[offset]in mp:bits[offset]=mp[bits[offset]]
    token='.'.join(bits)
    if token in allowed:out.add(token)
    elif 'AspisR1.'+token in allowed:out.add('AspisR1.'+token)
    else:
     found=aliases.get(token,set())
     if len(found)==1:out.update(found)
  elif isinstance(v,dict):
   for z in v.values():visit(z)
  elif isinstance(v,list):
   for z in v:visit(z)
 visit(x);return sorted(out)
def build(final=False):
 b=J('evidence/ledger11-20261107/NII_LEDGER.json.xz');nim=J('evidence/owner-dedupe-20261107/NIM_LEDGER_DELTA.json')
 by={r['row']:r for r in b['rows']};assert len(by)==599
 for d in nim['rows']:by[d['row']]['composed_status']=d['status']
 assert collections.Counter(r['composed_status']for r in by.values())=={'CLOSED':407,'OPEN':192}
 nimby={d['row']:d for d in nim['rows']}
 owners={json.loads(l[len('NIR_OWNER '):])['root']:json.loads(l[len('NIR_OWNER '):])for l in (E/'NIR_L014/stdout.log').read_text().splitlines()if l.startswith('NIR_OWNER ')}
 for l in (E/'NIR_L031/stdout.log').read_text().splitlines():
  if l.startswith('NIR_OWNER '):
   x=json.loads(l[len('NIR_OWNER '):]);owners[x['root']]=x
 assert len(owners)==len(J('evidence/ledger12-20261107/NIR_AUDIT_ROOTS.json')['roots'])
 neb=J('evidence/slice-q-compose-20261029/NEB_EDGES.json');nebc={r['row']:r for r in neb['row_certificates']}
 sinv=J('evidence/slice-s-join-20261105/NGI_CERT_INVENTORY.json.xz');sby={r['row']:r for r in sinv}
 nig=J('evidence/slice-d-pair4-20261107/NIG_CLOSED.json')['functions'][0]
 qcert=J('evidence/ledger12-20261107/NIR_Q_CERTIFICATES.json')['rows']
 scan=[json.loads(l)for l in (E/'NIR_LOADED_scan.jsonl').read_text().splitlines()];mods={r['module']for r in scan}
 assert all(not r['dangling']and not r['duplicate_owners']and r['imports_match']for r in scan)
 audit=J('evidence/ledger12-20261107/NIR_AUDIT.json')if final else None
 if final:assert audit['full_composition_pass'] and audit['required_roots']==len(owners)
 rows=[];missing=[];mismatches=[]
 for rid,r in by.items():
  status=r['composed_status'];cert=None;ns=[];dir=None
  # Prefer newest explicit row packet; never union an old broader domain into a new packet.
  if rid in nimby:
   d=nimby[rid];cert=d;ns=d['model_theorems'];dir='evidence/slice-d-entry'+('3-20261106'if d['provider']=='NHJ'else'4-20261106')
  else:
   for key in ['NII_certificate','NHO_certificate','NGZ_certificate']:
    if key in r:cert=r[key];break
   if cert is None:
    for key in ['NFX_certificates','NFK_certificates','NEZ_certificates']:
     if rid in b.get(key,{}):cert=b[key][rid];break
   if cert is None:cert=nebc.get(rid,r)
   ns=names(cert,owners)
  if rid in qcert:
   cert=qcert[rid]['packet'];ns=names(cert,owners);dir=str(Path(qcert[rid]['source']).parent)
  if rid in sby:
   cert=sby[rid];ns=sorted({t['canonical_name']for t in cert['theorems']});dir='evidence/slice-s-join-20261105'
   for t in cert['theorems']:
    assert t['canonical_name']in owners
    if owners[t['canonical_name']]['owner_module']!=t['canonical_module']:mismatches.append(dict(row=rid,theorem=t['canonical_name'],expected=t['canonical_module'],actual=owners[t['canonical_name']]['owner_module']))
  if rid=='TX2:045':
   cert=nig;ns=[nig['lean_root']]+nig['associated_laws'];dir='evidence/slice-d-pair4-20261107';status='CLOSED'if final else'QUALIFIED'
  if dir is None:
   def pathin(x):
    if isinstance(x,dict):
     for k,v in x.items():
      if k in ['path','receipt','review'] and isinstance(v,str)and v.startswith('evidence/'):return str(Path(v).parent)
     for v in x.values():
      q=pathin(v)
      if q:return q
    elif isinstance(x,list):
     for v in x:
      q=pathin(v)
      if q:return q
   dir=pathin(cert)or('evidence/slice-q-compose-20261029'if rid in nebc else'evidence/ledger11-20261107')
  ns=list(dict.fromkeys(ns));assert all(n in owners for n in ns),(rid,ns)
  coverage_root=None
  if status=='CLOSED' and not ns and rid not in sby:
   # The adopted Q forest has replaced several historical packet interfaces.
   # Record the enclosing certificate owner explicitly; do not invent a leaf theorem.
   if r.get('NEN_slice')=='Q':
    coverage_root='AspisR1.NFS_QueryLoopRoot.root'
    ns=[coverage_root];dir='evidence/slice-q-accum-20261104'
   else:missing.append(rid)
  bindings=[dict(root=n,owner_module=owners[n]['owner_module'],obligation_statement_sha256=H(owners[n]['obligation_statement'].encode()))for n in ns]
  owner=bindings[0]['owner_module']if bindings else ('NGI_COMBINED_IMPORT'if rid in sby else None)
  obligation=dict(function=r['function'],frozen_revision=b['frozen_revision'],frozen_body_sha256=r['frozen_body_sha256'],certificate=cert,named_hypotheses=r.get('named_hypotheses',[]),inventory_domain_obligations=r.get('inventory_domain_obligations',[]),caller_domain_obligations=r.get('caller_domain_obligations',[]),kernel_roots=[owners[n]for n in ns])
  raw=json.dumps(obligation,sort_keys=True,separators=(',',':')).encode();oh=H(raw)
  rows.append(dict(row=rid,function=r['function'],transaction=r['transaction'],slice=r.get('NEN_slice'),status=status,owner_module=owner,owner_role='enclosing canonical Q certificate; historical leaf names superseded'if coverage_root else'kernel declaration'if bindings else'transparent certificate forest'if rid in sby else'OPEN producer',root_owners=bindings,evidence_dir=dir,obligation_statement_hash=oh,obligation=obligation,frozen_body_sha256=r['frozen_body_sha256'],canonical_callees=r['canonical_callees'],previous_status=r['composed_status']))
 assert not mismatches,mismatches[:3]
 put('NIR_OWNER_CHECK.json',dict(status='PASS'if not missing else'INCOMPLETE',missing_closed_roots=missing,wrong_canonical_owner=mismatches,rows=len(rows),root_bindings=sum(len(r['root_owners'])for r in rows),scan='NIR_L008',selected_root_manifest=['NIR_L014/stdout.log','NIR_L031/stdout.log'],enclosing_Q_certificate_rows=[r['row']for r in rows if r['owner_role'].startswith('enclosing')],scope='Every selected owner module is loaded in the clean full scan. Per-row direct roots and enclosing canonical certificate roots are distinguished; no invented leaf theorem or new native credit.'))
 put('NIR_LEDGER.json',dict(schema_version=1,basis='NIM canonical-owner gate',basis_delta='evidence/owner-dedupe-20261107/NIM_LEDGER_DELTA.json',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),headline='AspisR1.RPx_Deployed.deployed',frozen_revision=b['frozen_revision'],status_semantics='CLOSED means composed conditional hybrid row under original domain and retained trust; never premise removal',gate='PASS'if final else'PENDING_RAW_AUDIT',security_target_established=False,counts=dict(collections.Counter(r['status']for r in rows)),rows=rows,trust_rows=b['trust_rows']))
 print(json.dumps(dict(rows=len(rows),counts=dict(collections.Counter(r['status']for r in rows)),missing=missing)))
 return rows,b,owners
if __name__=='__main__':build('--final'in __import__('sys').argv)
