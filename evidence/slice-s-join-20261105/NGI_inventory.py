"""Enumerate all selected historical theorem records before environment lookup."""
from pathlib import Path
import json,lzma,hashlib,re,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1];P=E.parent
J=lambda p:json.loads(p.read_text());H=lambda b:hashlib.sha256(b).hexdigest()
a=J(P/'slice-s-retarget2-20261104/NGE_PROVENANCE.json');b=J(P/'slice-s-retarget3-20261104/NGF_PROVENANCE.json')
ren={};owner={}
for x in [a,b]:
 for dest,key in [(ren,'namespace_map'),(owner,'module_owner')]:
  for n,v in x[key].items():
   assert n not in dest or dest[n]==v,('mapping conflict',key,n,dest.get(n),v)
   dest[n]=v
pat=re.compile(r'(?<![A-Za-z0-9_])('+'|'.join(map(re.escape,sorted(ren,key=len,reverse=True)))+r')(?![A-Za-z0-9_])')
base=J(P/'slice-s-retarget-20261104/NFY_CERTIFICATES.json');byname={t['legacy_name']:t for row in base['rows'] for t in row['canonical_theorem_associations']}
ledger=json.loads(lzma.decompress((P/'ledger7-20261104/NFX_LEDGER.json.xz').read_bytes()));rows=[]
def walk(v,out):
 if isinstance(v,dict):
  if isinstance(v.get('name'),str) and isinstance(v.get('source'),dict) and 'statement' in v:out.append(v)
  for z in v.values():walk(z,out)
 elif isinstance(v,list):
  for z in v:walk(z,out)
for r in ledger['rows']:
 spec=J(R/'docs/research/100bit-spend-path-20261013/design/VERTICAL-SLICES-20261029.json')['slices']['S']
 if r['function'] not in spec['functions']:continue
 c=ledger.get('NFK_certificates',{}).get(r['row'],ledger.get('NEZ_certificates',{}).get(r['row'],r));records=[];walk(c,records);refs=[]
 for t in records:
  old=byname.get(t['name'],{'canonical_module':{'NEQ_DecodeScalar':'NFY_Part005'}.get(t['name'].split('.')[0],t['name'].split('.')[0])});refs.append(dict(legacy_name=t['name'],canonical_name=pat.sub(lambda m:ren[m.group()],t['name']),canonical_module=owner.get(old['canonical_module'],old['canonical_module']),source=t['source'],statement_before=t['statement'],statement_after=pat.sub(lambda m:ren[m.group()],t['statement'])))
 rows.append(dict(row=r['row'],function=r['function'],certificate_sha256=H(json.dumps(c,sort_keys=True).encode()),theorems=refs))
raw=json.dumps(rows,indent=1).encode()+b'\n';(E/'NGI_CERT_INVENTORY.json.xz').write_bytes(lzma.compress(raw));(E/'NGI_CERT_INVENTORY.json.sha256').write_text(H(raw)+'\n')
names=sorted({t['canonical_name'] for r in rows for t in r['theorems']});assert len(names)==261
assert set(names)<=set(J(E/'NGI_AUDIT_ROOTS.json')['roots'])
# Six independent kernel-loaded inventory parts; no declaration is re-proved.
for i in range(6):
 ns=names[i*len(names)//6:(i+1)*len(names)//6]
 text='''import Lean
import NGI_COMBINED_IMPORT
open Lean
run_cmd do
 let env ← getEnv
 logInfo m!"NGI_CERT_MODULES {(toJson (env.header.moduleNames.map (fun n => n.toString))).compress}"
 for n in (#['''+','.join('`'+n for n in ns)+'''] : Array Name) do
  let entry := match env.find? n with
   | none => Json.mkObj [("name",toJson n.toString),("found",toJson false)]
   | some ci => Json.mkObj [("name",toJson n.toString),("found",toJson true),
       ("is_theorem",toJson ci.isTheorem),("module_idx",toJson ((env.getModuleIdxFor? n).map ModuleIdx.toNat)),
       ("type",toJson (reprStr ci.type))]
  logInfo m!"NGI_CERT_ENTRY {entry.compress}"
'''
 (E/f'NGI_CertificatePart{i:02}.lean').write_text(text)
print(json.dumps(dict(selected_certificates=len(rows),records=sum(len(r['theorems']) for r in rows),names=len(names))))
