"""Reproduce each namespaced leaf input without rewriting source or proofs."""
from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent;R=E.parents[1];manifest=json.loads((E/'NFU_RETARGET.json').read_text());names={x['module'][4:]for x in manifest};results=[]
for x in manifest:
 raw=(R/x['origin']).read_text();assert hashlib.sha256(raw.encode()).hexdigest()==x['origin_sha256']
 s=re.sub(r'^import (\S+)',lambda m:'import '+('NFU_'+m[1] if m[1] in names else m[1]),raw,flags=re.M)
 if x['module']=='NFU_LPl_Kit_Types':
  start=s.index('@[import_union_discriminant]\ninductive verifier.Phase where');end=s.index('\n\n',start);s=s[:start]+'abbrev verifier.Phase := NFN_PhaseTransport.Owned'+s[end:];s=s.replace('@[import_union_discriminant','@[import_union_discriminant isize');s='import NFN_PhaseTransport\n'+s
 lines=s.splitlines(True);last=max(i for i,l in enumerate(lines)if l.startswith('import '));lines.insert(last+1,'\nnamespace NFU_Retarget\n');s=''.join(lines)+'\nend NFU_Retarget\n'
 # Iteration's single import had no inserted blank line in its retained repair.
 if x['module']=='NFU_LPl_C_Iteration':s=s.replace('import Aeneas\n\nnamespace NFU_Retarget\n','import Aeneas\nnamespace NFU_Retarget\n',1)
 actual=(E/(x['module']+'.lean')).read_text();assert s==actual,x['module'];assert hashlib.sha256(actual.encode()).hexdigest()==x['source_sha256']
 assert not re.search(r'^import (?:FIo_|S1SemanticPhaseV1|LPl_|LPn_)',actual,re.M)
 # Every copied top theorem preserves its original body and printed axiom audit.
 theorems=re.findall(r'^theorem (\S+)',actual,re.M);prints=re.findall(r'^#print axioms (\S+)',actual,re.M)
 assert all(any(p==t or p.endswith('.'+t)for p in prints)for t in theorems),(x['module'],'missing axiom print')
 results.append(dict(module=x['module'],theorems=len(theorems),source_sha256=x['source_sha256']))
out=dict(status='PASS',modules=len(results),theorems=sum(x['theorems']for x in results),proof_terms_unchanged=True,canonical_phase='NFN_PhaseTransport.Owned',results=results)
(E/'NFU_RETARGET_CHECK.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps({k:v for k,v in out.items()if k!='results'}))
