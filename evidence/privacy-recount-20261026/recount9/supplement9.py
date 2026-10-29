from auditlib9 import *
# Merge separately captured immutable witnesses without resolving any moving ref.
if (P/'independent-manifest9.json').exists():
 for x in json.loads((P/'independent-manifest9.json').read_text()):
  if (x['ref'],x['path']) not in ix:ix[x['ref'],x['path']]=x;manifest.append(x)
out={};checks=[]
def check(n,b):
 checks.append(dict(check=n,pass_=bool(b)));assert b,n
D='evidence/pv-b3p6-20261028/'
x=json.loads(read('b3p6',D+'resume12/identity-audit.json'))
lex=re.compile(r'//[^\n]*|/\*[\s\S]*?\*/|r(\#*)"[\s\S]*?"\1|"(?:\\.|[^"\\])*"|\w+|[^\s]')
def tokens(s):return [(m[0],m.start(),m.end()) for m in lex.finditer(s) if not m[0].startswith(('//','/*'))]
def close(ts,i):
 d=1;j=i+1
 while d:d+=(ts[j][0]=='{')-(ts[j][0]=='}');j+=1
 return j
def modtext(s,name):
 ts=tokens(s);ms=[i+2 for i in range(len(ts)-2) if [t[0] for t in ts[i:i+3]]==['mod',name,'{']];assert len(ms)==1
 i=ms[0];j=close(ts,i);return s[ts[i][2]:ts[j-1][1]]
def funcs(s):
 ts=tokens(s);out=[]
 for i in range(len(ts)-2):
  if ts[i][0]!='fn':continue
  j=i+2;depth=0
  while j<len(ts):
   v=ts[j][0]
   if depth==0 and v in ['{',';']:break
   if v in ['(','[']:depth+=1
   if v in [')',']']:depth-=1
   j+=1
  if j==len(ts) or ts[j][0]==';':continue
  k=close(ts,j);text=s[ts[i][1]:ts[k-1][2]];tt=[v[0] for v in ts[i:k]];out.append((hashlib.sha256(text.encode()).hexdigest(),hashlib.sha256('\0'.join(tt).encode()).hexdigest(),tt))
 return out
expanded={n:read('b3p6',D+'resume12/expanded-'+n+'.rs') for n in ['owned','statement','deployed']}
for n,s in expanded.items():check('expanded '+n,hashlib.sha256(s.encode()).hexdigest()==x['expanded_hashes'][n])
mods={'terminal':('host_terminal','reference_terminal'),'copy':('host_copy_terminal','reference_copy_terminal'),'field':('host_terminal_field','reference_field'),'poseidon':('state_only_poseidon','reference_poseidon')};tables={}
for fam,(src,owned) in mods.items():
 tables[fam,'source']=funcs(modtext(expanded['statement' if fam=='poseidon' else 'deployed'],src));tables[fam,'owned']=funcs(modtext(expanded['owned'],owned))
raw=read('b3p6',D+'raw227-composition-resume5/Funs.lean');blocks=re.split(r'(?=^/-- \[)',raw,flags=re.M)
output=json.loads(read('b3p6',D+'resume12/aeneas-outputs.json'));check('actual raw Funs reproduction hash',hashlib.sha256(raw.encode()).hexdigest()==next(v['sha256'] for v in output if v['path'].endswith('Funs.lean')))
inv=json.loads(read('b3p6',D+'resume9/body-inventory.json'))
for v in x['bodies']:
 matches={}
 for side in ['source','owned']:
  a=[z for z in tables[v['family'],side] if z[0]==v[side]['expanded_body_sha256'] and z[1]==v[side]['token_sha256']];check(v['key']+' actual '+side+' body present',bool(a));matches[side]=a[0][2]
 check(v['key']+' actual token equality',matches['source']==matches['owned'])
 if v['bound']:
  loc=inv['bodies'][v['inventory_index']]['owned']['line'];f='reference_'+('copy_terminal' if v['family']=='copy' else v['family'])+'.rs'
  for d in v['model_declarations']:
   a=[b for b in blocks if hashlib.sha256(b.encode()).hexdigest()==d['raw_block_sha256']];check(d['name']+' actual raw block and exact source span',bool(a) and f"Source: '{f}', lines {loc}:" in a[0])
inputs=json.loads(read('b3p6',D+'resume12/aeneas-inputs.json'))
unavailable=[]
for p,h in inputs['inputs'].items():
 s=read('b3p6',p)
 if s is None:unavailable.append(dict(path=p,recorded_sha256=h,qualification='Generated input recorded by extraction receipt; not tracked at snapshot. No independent byte re-hash claimed.'))
 else:check('pinned extractor input '+p,hashlib.sha256(s.encode()).hexdigest()==h)
out['unavailable_generated_input_bytes']=unavailable
# Source-level full statements for skeleton and headline carrier, including root-lean modules.
for path in ['lean/PV_L1E_CountSkeleton.lean','lean/PV_L1E_OriginalCountSkeleton.lean','lean/PV_L1G_Statements.lean','lean/PV_FIB_Restricted.lean','lean/PV_FIB_Termination.lean','lean/PV_RJ4IDB_OpenInputs.lean','lean/PV_RJ4IDB.lean']:
 read('rw',path)
# Existing section6 reports are retained as reports, not fresh compilation claims.
read('rw','evidence/pv-l1g-20261029/REPORT.md')
out['postmacro_raw_extraction_rederived']=True;out['checks']=checks;out['scope']='Independent re-hashing and tokenization of committed expansion bodies, exact raw model blocks and extractor input sources. No extractor or proof run.'
(P/'supplement-audit9.json').write_text(json.dumps(out,indent=1)+'\n');save();print('Supplement checks',len(checks),'PASS')
