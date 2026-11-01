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
for p in sorted((D/'lean').glob('PV_B3P_P227_*.lean'))+sorted((D/'lean').glob('PV_B3P_E227_*.lean')):
 for n,b in defs(p.read_text()).items():
  if n not in old:old[n]=b;origin[n]=p

def normalized(s):
 s=s.replace('31#i32','31#u32').replace('Std.U64.wrapping_shl i2 shift','Std.U64.wrapping_shl i2 (UScalar.cast .U32 shift)').replace('Std.U64.wrapping_shl i7 shift','Std.U64.wrapping_shl i7 (UScalar.cast .U32 shift)').replace('Std.U64.wrapping_shl i12 shift','Std.U64.wrapping_shl i12 (UScalar.cast .U32 shift)').replace('Std.U64.wrapping_shl i17 shift','Std.U64.wrapping_shl i17 (UScalar.cast .U32 shift)')
 s=re.sub(r'\s*\(by simp only \[List.length_cons,\s*List.length_nil\]; rfl\)','',s)
 # Remove only named length-proof applications, never executable arguments.
 while '(PV_B3P_Length227.size' in s:
  a=s.index('(PV_B3P_Length227.size');d=1;i=a+1
  while d:d+=(s[i]=='(')-(s[i]==')');i+=1
  s=s[:a]+s[i:]
 return ' '.join(re.findall(r'"(?:\\.|[^"])*"|[A-Za-z_][\w.]*|[0-9]+|[^\s]',s))
rows=[]
for n,b in defs((R/'reference-poseidon/generated/Funs.lean').read_text()).items():
 assert n in old,n
 if normalized(b)!=normalized(old[n]):
  print(n,'\n'.join(list(difflib.unified_diff(normalized(b).split(),normalized(old[n]).split()))[:50]));raise SystemExit(1)
 rows.append(dict(declaration=n,raw_declaration_sha256=hashlib.sha256(b.encode()).hexdigest(),retained_module=str(origin[n]),retained_module_sha256=sha(origin[n]),comparison='all executable tokens and declarations equal after recorded pinned API ports and proof-only array-length erasure'))
types=defs((R/'reference-poseidon/generated/Types.lean').read_text());retained=defs((D/'lean/PV_B3P_SelectEmission227.lean').read_text())
for n,b in types.items():assert normalized(b)==normalized(retained[n]),n
x=dict(scope='N79161',inputs_sha256=sha(R/'reference-poseidon/inputs.json'),outputs_sha256=sha(R/'reference-poseidon/outputs.json'),declarations=rows,same_origin_same_features_types=list(types),ports=['shift31_value','u8_u32_value: widening all U8 shift values to U32','explicit fixed-size Array.make length proofs only'],holes=[],status='Exact raw/internal reference-model association is source-bound by the fresh replay. This alone is NOT deployed-body association; raw still needs full source/from_fn binding or canonical caller proof, internal needs source-step association.',V370='retained D381/D386; no native intrinsic semantics asserted')
(R/'POSEIDON-REFERENCE-D543.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(dict(declarations=len(rows),same_origin_types=len(types),new_holes=[])))
