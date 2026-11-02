"""Check fresh exact raw/internal reference replay against retained declarations."""
from pathlib import Path
import re,json,hashlib,difflib
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def defs(s):
 out={}
 for b in re.split(r'(?=^/-- \[)',s,flags=re.M):
  m=re.search(r'^(?:def|structure|inductive) (\S+)',b,re.M)
  if m:out[m[1]]=b[m.start():].split('\nend ')[0].split('\n#print')[0].strip()
 return out
old={};origin={}
for p in sorted((D/'lean').glob('PV_B3P_P227_*.lean'))+sorted((D/'lean').glob('PV_B3P_E227_*.lean'))+[D/'lean/PV_B3P_SelectEmission227.lean']:
 for n,b in defs(p.read_text()).items():
  if n not in old:old[n]=b;origin[n]=p

def normalized(s):
 s=re.sub(r'(Std.U64.wrapping_shr public1.transition.live_snapshot.next_pair_index\s+)(\d+)#usize',lambda m:m[1]+m[2]+'#u32' if int(m[2])<20 else m[0],s)
 s=s.replace('Std.U32.wrapping_shl 1#u32 10#i32','Std.U32.wrapping_shl 1#u32 10#u32').replace('Std.U32.wrapping_shl 1#u32 20#i32','Std.U32.wrapping_shl 1#u32 20#u32').replace('Std.Usize.wrapping_shr row 4#i32','Std.Usize.wrapping_shr row 4#u32').replace('31#i32','31#u32').replace('Std.U64.wrapping_shl i2 shift','Std.U64.wrapping_shl i2 (UScalar.cast .U32 shift)').replace('Std.U64.wrapping_shl i7 shift','Std.U64.wrapping_shl i7 (UScalar.cast .U32 shift)').replace('Std.U64.wrapping_shl i12 shift','Std.U64.wrapping_shl i12 (UScalar.cast .U32 shift)').replace('Std.U64.wrapping_shl i17 shift','Std.U64.wrapping_shl i17 (UScalar.cast .U32 shift)')
 s=re.sub(r'\s*\(by simp only \[List.length_cons,\s*List.length_nil\]; rfl\)','',s)
 # Remove only named length-proof applications, never executable arguments.
 while '(PV_B3P_Length227.size' in s:
  a=s.index('(PV_B3P_Length227.size');d=1;i=a+1
  while d:d+=(s[i]=='(')-(s[i]==')');i+=1
  s=s[:a]+s[i:]
 return ' '.join(re.findall(r'"(?:\\.|[^"])*"|[A-Za-z_][\w.]*|[0-9]+|[^\s]',s))
import sys
group=sys.argv[1]; assert group in ['leading','copy','schedule','packed','projected']
O=R/('reference-'+group)
# Reverse the previously recorded pure let-lifting, with no evaluation or
# data changes. This checks the retained declarations themselves, not a model
# initializer chosen merely because it happens to have the same name.
const_name='reference_copy_terminal.constants.COPY_PATTERNS'
if group in ['copy','schedule']:
 p=D/'lean/PV_B3P_E227_06.lean';c=p.read_text();lifted={}
 for block in re.split(r'(?=^(?:private )?def )',c,flags=re.M):
  m=re.match(r'(?:private )?def (reference_copy_terminal.constants.\w+) [\s\S]*?:=([\s\S]*)',block)
  if m:
   body=m[2].split('\n@[irreducible]')[0].split('\nend ')[0].strip();lifted[m[1]]=body
 assert len(lifted)==30,len(lifted)
 prefix='reference_copy_terminal.constants.'
 records=[]
 for i in range(14):
  body=lifted[prefix+f'pattern_{i}']
  body=re.sub(re.escape(prefix)+r'pattern_let_(a\d*)\b',r'\1',body);records.append(body)
 initializer=lifted[const_name]
 for i in reversed(range(14)):
  initializer=re.sub(re.escape(prefix+f'pattern_{i}')+r'\b',lambda m:records[i],initializer)
 lets='\n'.join('let '+('a'if i==0 else'a'+str(i))+' := '+lifted[prefix+'pattern_let_'+('a'if i==0 else'a'+str(i))]for i in range(15))
 old[const_name]=old[const_name].split(':=',1)[0]+':=\n'+lets+'\n'+initializer
 constant_roundtrip=dict(retained_module=str(p),sha256=sha(p),lifted_shared_values=15,lifted_records=14,operation='reverse pure let lifting into exact original ordered initializer; compare all tokens; no data normalization')
else:constant_roundtrip=None
rows=[]
for n,b in defs((O/'generated/Funs.lean').read_text()).items():
 assert n in old,n
 assert normalized(b)==normalized(old[n]), n+' differs: '+str(list(difflib.unified_diff(normalized(b).split(), normalized(old[n]).split()))[:40])
 rows.append(dict(declaration=n,raw_declaration_sha256=hashlib.sha256(b.encode()).hexdigest(),retained_module=str(origin[n]),retained_module_sha256=sha(origin[n])))
types=defs((O/'generated/Types.lean').read_text());retained={}
for p in [D/'lean/PV_B3P_SelectEmission227.lean',D/'lean/PV_B3P_CompleteTypes227.lean']:retained.update(defs(p.read_text()))
for n,b in types.items():assert n in retained and normalized(b)==normalized(retained[n]),n
x=dict(group=group,inputs_sha256=sha(O/'inputs.json'),outputs_sha256=sha(O/'outputs.json'),declarations=rows,same_origin_same_features_types=list(types),constant_roundtrip=constant_roundtrip,type_and_port_modules={str(p):sha(p)for p in [D/'lean/PV_B3P_SelectEmission227.lean',D/'lean/PV_B3P_CompleteTypes227.lean',D/'lean/PV_B3P_Shift227.lean',D/'lean/PV_B3P_ShiftPorts227.lean']},ports=['shift31_value and shift4_value of Shift227; shift10_value/shift20_value and count0_value..count19_value of ShiftPorts227; u8 widening; proof-only length erasure; pure constant let-lifting reversed with full token comparison'],holes=[],status='Reference provenance only; local source interpretation and compiled Result equality required separately; full cone remains open',V370='retained D381/D386')
(R/('REFERENCE-'+group.upper()+'-D547.json')).write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps(dict(group=group,declarations=len(rows),types=len(types),holes=[])))
