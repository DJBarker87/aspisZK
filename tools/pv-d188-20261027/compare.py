"""Compare test outputs; these are finite tests, never proof terms."""
from pathlib import Path
import json,re,ast
out=Path('evidence/pv-d188-20261027')
def arrays(s):
 r=[]
 for part in s.split('Aeneas.Std.Result.ok')[1:]:
  if '[' not in part:continue
  a=part.index('[');depth=1;i=a+1
  while depth:
   if part[i]=='[':depth+=1
   elif part[i]==']':depth-=1
   i+=1
  r.append(json.loads(part[a:i]))
 return r

def lean(a):
 rec=json.loads((out/f'{a}-receipt.json').read_text());assert rec['exit']==0
 return arrays((out/f'{a}-out.log').read_text())
def native(tag,label):
 rec=json.loads((out/f'{tag}-receipt.json').read_text());assert rec['exit']==0
 line=next(l for l in (out/f'{tag}-out.log').read_text().splitlines() if l.startswith(label+' '));a=line.index('[');depth=1;i=a+1
 while depth:
  if line[i]=='[':depth+=1
  elif line[i]==']':depth-=1
  i+=1
 return json.loads(line[a:i])
checks=[]
def add(name,a,value,native_tag,label,projection='complete output'):
 n=native(native_tag,label);checks.append(dict(function=name,lean_attempt=a,native_run=native_tag,projection=projection,agree=value==n,emitted=value,native=n));assert value==n,name
add('CM31/QM31.write_le_bytes',28102,lean(28102)[0],'native-001','op72')
# Three sampler inputs are nested in a single printed list; extract all Result payloads.
q=lean(28104)
for i,label in enumerate(['zero','P','P+1','ff']):add('sampler.qm31_sample '+label,28104,q[i],'native-001','qm31 '+label)
r=lean(28106)
for i,label in enumerate(['zero','P','P+1','ff']):add('indexed low_base_p_digits '+label,28106,r[i],'native-001','low '+label,'digits; remaining quotient checked in raw transcript')
for i,label in [(4,'carry'),(5,'one')]:add('indexed add_small_base_p '+label,28106,r[i],'native-001','add '+label,'digit vector; carry checked in raw transcript')
add('state_only_statement_points',28107,lean(28107)[0],'native-002','statement')
p=lean(28108)
add('sha_pad_zero',28108,p[0],'native-002','pad')
add('sha_pad_suffix8',28108,p[1],'native-002','suffix')
add('array_reference',28108,p[2],'native-002','array')
add('sha256_digest_block_u32',28109,lean(28109)[0],'native-002','sha')
add('StateOnlyHidingContext.encode',28111,lean(28111)[0],'native-002','context')
# Debug output of the native field records is flattened without omitting any limb.
line=next(l for l in (out/'native-002-out.log').read_text().splitlines() if l.startswith('powers '));limbs=list(map(int,re.findall(r'M31\((\d+)\)',line)));v=[limbs[i:i+8] for i in range(0,len(limbs),8)];actual=lean(28112)[0];assert actual==v;checks.append(dict(function='prover_powers::powers N=3',lean_attempt=28112,native_run='native-002',projection='all eight limbs of all three outputs',agree=True,emitted=actual,native=v))
t=lean(28115)
for i,label in enumerate(['tuple','forest']):add(label+'::tuple_cells',28115,t[i],'native-004',label)
add('prototype public_bytes',28116,lean(28116)[0],'native-005','public','all 1455 bytes; length checked in raw transcript')
add('prototype weights_new',28117,lean(28117)[0],'native-005','weights','base limb of all 100 factors, with all input values in base field')

# Fresh ordinary-copy run, using its own unchanged integer-only emitted definitions.
for i,label in enumerate(['zero','P','P+1','ff']):add('ordinary-copy low_base_p_digits '+label,28120,lean(28120)[i],'native-001','low '+label,'digits; quotient checked below')
for attempt in [28106,28120]:
 text=(out/f'{attempt}-out.log').read_text()
 qs=list(map(int,re.findall(r'Aeneas.Std.Result.ok\s*\(\[[^\]]+\],\s*(\d+)\)',text)))
 assert qs==[0,0,0,256],(attempt,qs)

add('owned mask cell',28123,lean(28123)[0],'native-006','cell')
l=(out/'28123-out.log').read_text();n=(out/'native-006-out.log').read_text();assert re.search(r'Result.ok 6',l) and re.search(r'^basis 6$',n,re.M)
checks.append(dict(function='owned basis_cell M31',lean_attempt=28123,native_run='native-006',projection='updated output element',agree=True,emitted=6,native=6))
h=lean(28124)
add('Full active_rows',28124,h[0],'native-007','active','first eight flags, including every selected row')
add('Full source_active_flags_loop',28124,h[1],'native-007','flags','first 32 flags; static update carried through all 1024 iterations')
assert 'Result.ok (some 7)' in (out/'28124-out.log').read_text() and 'dependent Some(7)' in (out/'native-007-out.log').read_text()
checks.append(dict(function='Full mask_dependent_step',lean_attempt=28124,native_run='native-007',projection='updated column3',agree=True,emitted=7,native=7))
add('Full count_level',28124,h[2],'native-007','count','all 16 carried level entries; n=2 and missing=1 retained in raw logs')
add('Full scan_query_words',28124,h[3],'native-007','scan','all 22 accepted words; advance block retained in raw logs')

for attempt,label in [(28126,'boolean'),(28128,'basis_cell'),(28129,'extend'),(28130,'basis'),(28131,'assignment'),(28134,'accumulate')]:
 add('isolated Full '+label,attempt,lean(attempt)[0],'native-008',label,'written base limbs; actual primitive leaves and literal constants supplied, not a whole native dictionary')
for attempt,label in [(28135,'balance_m31'),(28136,'balance_qm31')]:
 text=(out/f'{attempt}-out.log').read_text();rec=json.loads((out/f'{attempt}-receipt.json').read_text());assert rec['exit']==0
 value=int(re.search(r'Aeneas.Std.Result.ok (\d+)',text)[1]);line=next(l for l in (out/'native-008-out.log').read_text().splitlines() if l.startswith(label+' '));n=int(line.split()[1]);assert value==n
 checks.append(dict(function='isolated Full '+label,lean_attempt=attempt,native_run='native-008',projection='written dependent cell; whole Result/native effects not established',agree=True,emitted=value,native=n))
# Reuse the specifically measured raw-kit results; no fresh raw replay is claimed.
raw={"zero":([0]*8,0),"P":([0]*8,2147483647),"P+1":([1]*8,2147483648),"ff":([255]*8,4294967295)}
raw_checks=[]
for label,(digits,q) in raw.items():
 line=next(l for l in (out/'native-001-out.log').read_text().splitlines() if l.startswith('low '+label+' '))
 n=ast.literal_eval(line.split(' ',2)[2]);raw_checks.append(dict(function='raw-kit low_base_p_digits '+label,emission_evidence='SDX_FINDING.reused.md: Q2/XRn; inherited Lean result',native_run='native-001',emitted=[digits,q],native=n,agree=(digits,q)==n))
assert [c['agree'] for c in raw_checks]==[True,False,False,False]
(out/'differential.json').write_text(json.dumps(dict(kind='finite testing; no proof credit',checks=checks,inherited_raw_kit_checks=raw_checks,all_compared_projections_agree=all(c['agree'] for c in checks)),indent=2)+'\n');print(len(checks),'agree')
