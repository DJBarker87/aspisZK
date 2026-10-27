"""Read-only retained LLBC/type-hole evidence; does not synthesize representations."""
from pathlib import Path
import hashlib,json,sys
p=Path(sys.argv[1]);i=Path(sys.argv[2]);out=Path(sys.argv[3]);x=json.loads(p.read_text());t=x.get('translated',x)
def name(d):return '.'.join(z['Ident'][0] for z in d['item_meta']['name'] if 'Ident' in z)
types={name(d):d for d in t['type_decls'] if d}
rows=[]
for a in json.loads(i.read_text())['types']:
 n=a['name'];d=types.get(n)
 rows.append(dict(id=a['id'],name=n,retained_type_id=d['def_id'] if d else None,kind=d['kind'] if d else 'Synthetic/assumed carrier from adapter',opacity=d['item_meta']['opacity'] if d else None,span=d['item_meta']['span'] if d else None,generics=d['generics'] if d else None,layout=d['layout'] if d else None,native_association='OPEN',required='Retained transparent extraction or native wrapper contract with carrier/effect transport under existing D188/P6; an arbitrary ExternalTypes update would only choose an interpreter.'))
result=dict(retained_llbc=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size,rows=rows,foreign_opaque=sum(z['kind']=='Opaque' for z in rows),opaque_UInt_dependent_function_entries=[137,138,139,140,161,162],changed_trust=False,root_premises_removed=0)
out.write_text(json.dumps(result,indent=2)+'\n');print(dict(types=len(rows),opaque=result['foreign_opaque']))
