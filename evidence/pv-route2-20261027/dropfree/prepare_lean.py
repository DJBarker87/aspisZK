from pathlib import Path
import re,json,sys,hashlib
D=Path(__file__).resolve().parent;L=D/'lean';L.mkdir(exist_ok=True);rows=[];adapters=[]
for key in sys.argv[1:]:
 op,suffix=key.split('-');module=f'PV_R2_DF_{op}_{suffix}'
 for phase in ['Types','Funs']:
  p=D/f'generated-{key}'/(phase+'.lean');s=p.read_text();rawhash=hashlib.sha256(s.encode()).hexdigest()
  s=re.sub(r'import \S+\.Types',f'import {module}_Types',s)
  # Existing pinned-backend compatibility: shifts expect U32, not emitted I32.
  before=s
  s=re.sub(r'(wrapping_sh[lr] [^\n]+?) (\d+)#i32',r'\1 \2#u32',s)
  adapters.append(dict(module=module+'_'+phase,raw_sha256=rawhash,shift_literal_port=before!=s))
  names=re.findall(r'^(?:def|structure|inductive) ([\w.]+)',s,re.M)
  s=s.replace('end '+module,'\n'.join('#print axioms '+n for n in names)+'\nend '+module)
  name=module+'_'+phase;(L/(name+'.lean')).write_text(s);rows.append(dict(module=name,op=int(op),kind='emission '+phase,file=str(L/(name+'.lean'))))
(D/'rows.json').write_text(json.dumps(rows,indent=2)+'\n');(D/'adapters.json').write_text(json.dumps(adapters,indent=2)+'\n')
