"""Symbolic source-schedule audit for V243. Never grants credit on its own.

The interpreter handles exactly the expression/control subset in byte_at. Field
words remain symbolic; only the finite two-variant index/control domain is
expanded. This checks source structure, not native machine execution.
"""
from pathlib import Path
from types import SimpleNamespace
import re,json,hashlib,subprocess
R=Path(__file__).resolve().parents[2];D=R/'evidence/pv-b3p6-20261028';T=R/'tools/pv-b3p6-20261028'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def body(s,anchor):
 a=s.index('{',s.index(anchor));i=a+1;n=1
 while n:
  n+=(s[i]=='{')-(s[i]=='}');i+=1
 return s[a+1:i-1]
def toks(s):
 s=re.sub(r'//[^\n]*|/\*.*?\*/','',s,flags=re.S)
 return re.findall(r'\d+(?:u32|u8|usize)?|[A-Za-z_]\w*|::|>=|<=|==|!=|>>|[^\s]',s)
class Parser:
 def __init__(self,s):self.ts=toks(s);self.i=0
 def at(self):return self.ts[self.i] if self.i<len(self.ts) else None
 def take(self,x=None):
  t=self.at();assert t is not None
  if x is not None:assert t==x,(self.i,x,t)
  self.i+=1;return t
 def block(self,braced=True):
  if braced:self.take('{')
  out=[]
  while self.at() is not None and self.at()!='}':
   if self.at()=='let':
    self.take();name=self.take();self.take('=');v=self.expr();self.take(';');out.append(('let',name,v))
   elif self.at()=='return':
    self.take();v=self.expr();self.take(';');out.append(('return',v))
   elif self.at()=='if':
    self.take();c=self.expr();b=self.block();out.append(('if',c,b))
   else:
    out.append(('return',self.expr()))
    if self.at()==';':self.take()
  if braced:self.take('}')
  return out
 def expr(self,minimum=0):
  t=self.take()
  if t=='(':
   left=self.expr();self.take(')')
  elif t=='if':
   c=self.expr();self.take('{');a=self.expr();self.take('}');self.take('else');self.take('{');b=self.expr();self.take('}');left=('ifexpr',c,a,b)
  elif t[0].isdigit():left=('num',int(re.match(r'\d+',t)[0]))
  else:left=('name',t)
  precedence={'==':1,'!=':1,'>=':1,'<=':1,'<':1,'>':1,'>>':2,'+':3,'-':3,'*':4,'/':4,'%':4}
  while True:
   t=self.at()
   if t=='.':self.take();left=('attr',left,self.take())
   elif t=='[':self.take();ix=self.expr();self.take(']');left=('index',left,ix)
   elif t=='(':
    self.take();args=[]
    if self.at()!=')':
     args.append(self.expr())
     while self.at()==',':self.take();args.append(self.expr())
    self.take(')');left=('call',left,args)
   elif t=='as':self.take();left=('cast',left,self.take())
   elif t in precedence and precedence[t]>=minimum:
    self.take();left=('bin',t,left,self.expr(precedence[t]+1))
   else:return left
class Index:
 pass
def evaluate(e,env):
 tag=e[0]
 if tag=='num':return e[1]
 if tag=='name':return env[e[1]]
 if tag=='attr':return getattr(evaluate(e[1],env),e[2])
 if tag=='index':return evaluate(e[1],env)[evaluate(e[2],env)]
 if tag=='cast':
  v=evaluate(e[1],env)
  assert e[2] in {'u32','u8'}
  # All concrete arithmetic here is a bounded index/shift; actual field
  # truncation is retained symbolically and justified by endian Lean laws.
  return v
 if tag=='call':return evaluate(e[1],env)(*(evaluate(x,env) for x in e[2]))
 if tag=='ifexpr':return evaluate(e[2] if evaluate(e[1],env) else e[3],env)
 if tag=='bin':
  op=e[1];a=evaluate(e[2],env);b=evaluate(e[3],env)
  if op=='>>':assert isinstance(a,Index) and b in range(0,64,8);return ('index',b//8)
  assert isinstance(a,(int,bool)) and isinstance(b,(int,bool)),(op,a,b)
  if op=='+':return a+b
  if op=='-':assert a>=b;return a-b
  if op=='*':return a*b
  if op=='/':assert b;return a//b
  if op=='%':assert b;return a%b
  if op=='==':return a==b
  if op=='!=':return a!=b
  if op=='>=':return a>=b
  if op=='<=':return a<=b
  if op=='<':return a<b
  if op=='>':return a>b
 raise AssertionError(e)
def execute(block,env):
 for stmt in block:
  if stmt[0]=='let':env[stmt[1]]=evaluate(stmt[2],env)
  elif stmt[0]=='return':return evaluate(stmt[1],env)
  elif stmt[0]=='if':
   if evaluate(stmt[1],env):
    out=execute(stmt[2],env)
    if out is not None:return out
  else:raise AssertionError(stmt)
 return None

def words(name,n):return [(name,j) for j in range(n)]
def frontier(name):return [[(name,r,j) for j in range(8)] for r in range(20)]
def fields(values):return [('field',v,j) for v in values for j in range(4)]
def symbolic(w):
 return SimpleNamespace(withdrawal=w,anchor=words('anchor',8),nullifier=words('nullifier',8),asset_id=('asset',),recipient=words('recipient',8),change=words('change',8),withdrawal_amount=('amount',),next_pair_index=Index(),frontier=frontier('frontier'),next_root=words('root',8),next_frontier=frontier('next_frontier'))
def native_schedule(p):
 out=[('constant',int(p.withdrawal))]+fields(p.anchor)+fields(p.nullifier)+fields([p.asset_id])+[('constant',int(not p.withdrawal))]
 if not p.withdrawal:out+=fields(p.recipient)
 out+=fields(p.change)+[('constant',int(p.withdrawal))]
 if p.withdrawal:out+=fields([p.withdrawal_amount])
 out += [('index',j) for j in range(8)]
 out += fields([x for row in p.frontier for x in row])+fields(p.next_root)+fields([x for row in p.next_frontier for x in row])
 return out
native_path=R/'crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs'
native=native_path.read_text();owned=(T/'owned226.rs').read_text();ref=(T/'reference226.rs').read_text()
assert native==subprocess.check_output(['git','show','1e826627aa:'+str(native_path.relative_to(R))],cwd=R,text=True)
assert sha(T/'reference226.rs')==json.loads((D/'preflight226v3.json').read_text())['reference_sha256']
for anchor in ['fn private_public','fn withdrawal_public','fn semantic(self)','pub fn public_bytes(self)']:
 assert toks(body(native,anchor))==toks(body(owned,anchor)),anchor
b=body(native,'pub fn public_bytes(self)');main=b[b.index('let p = self.semantic();'):]
expected='''let p = self.semantic(); let mut out = Vec::new();
out.push(match p.variant { CompiledVariant::PrivateTransfer => 0, CompiledVariant::Withdrawal => 1, });
fields(&mut out, &p.anchor)?; fields(&mut out, &p.nullifier)?; fields(&mut out, &[p.asset_id])?;
out.push(u8::from(p.recipient.is_some()));
if let Some(value) = p.recipient { fields(&mut out, &value)?; }
fields(&mut out, &p.change)?;
out.push(u8::from(p.withdrawal_amount.is_some()));
if let Some(value) = p.withdrawal_amount { fields(&mut out, &[M31(value)])?; }
let source = p.transition.live_snapshot; let after = p.transition.candidate_afterstate;
out.extend_from_slice(&source.next_pair_index.to_le_bytes()); frontier(&mut out, &source.frontier)?;
fields(&mut out, &after.next_root)?; frontier(&mut out, &after.next_frontier)?; Ok(out)'''
assert toks(main)==toks(expected),'native main has an unaccounted call/control change'
assert toks(body(b,'fn fields('))==toks('''for value in values {
if value.0 >= aspis_core::field::P { return Err(Error::Public); }
out.extend_from_slice(&value.0.to_le_bytes()); } Ok(())''')
assert toks(body(b,'fn frontier('))==toks(''.join(f'fields(out, &values[{i}])?;' for i in range(20))+'Ok(())')
parser=Parser(body(ref,'fn byte_at('));ast=parser.block(False);assert parser.i==len(parser.ts)
checked=[]
for withdrawal in [False,True]:
 p=symbolic(withdrawal);events=native_schedule(p);n=1427 if withdrawal else 1455;assert len(events)==n
 for i in range(1472):
  def ok(x):return x if isinstance(x,tuple) else ('constant',x)
  event=execute(ast,dict(p=p,i=i,Ok=ok,M31=lambda x:x,field_byte=lambda x,j:('field',x,j)))
  assert event==(events[i] if i<n else ('constant',0)),(withdrawal,i,event)
 # Every word occurs at four consecutive lanes in source order; arbitrary
 # noncanonical words remain symbolic and are not restricted to fixtures.
 checks=[e for e in events if e[0]=='field']
 assert len(checks)%4==0
 for i in range(0,len(checks),4):assert checks[i:i+4]==[('field',checks[i][1],j) for j in range(4)]
 checked.append(dict(withdrawal=withdrawal,bytes=n,padding=1472-n,field_words=len(checks)//4,symbolic_events_sha256=hashlib.sha256(repr(events).encode()).hexdigest()))
chunk8=body(ref,'fn chunk8(');chunk=body(ref,'fn chunk(');encode=body(ref,'pub fn encode_owned(')
assert list(map(int,re.findall(r'byte_at\(p, base \+ (\d+)\)\?',chunk8)))==list(range(8))
assert list(map(int,re.findall(r'chunk8\(p, base \+ (\d+)\)\?',chunk)))==list(range(0,64,8))
assert re.findall(r'a(\d+)\[(\d+)\]',chunk)==[(str(a),str(b)) for a in range(8) for b in range(8)]
assert list(map(int,re.findall(r'chunk\(p, (\d+)\)\?',encode)))==list(range(0,1472,64))
record=dict(revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),evidence_class='symbolic structural schedule audit; supporting evidence only',native_sha256=sha(native_path),owned_sha256=sha(T/'owned226.rs'),reference_sha256=sha(T/'reference226.rs'),symbolic_variants=checked,word_values='arbitrary symbolic labels; no concrete field fixtures',index_domain='all bytes in both finite serializer layouts plus padding',native_link_credit=False,row_closed=False,retained_obligations=['checked application of the region/Result/Vec/grouping laws to this structural schedule and complete row binding','both-variant nonvacuity and final closure audit'],warning='This source-schedule audit does not itself prove native execution equality or grant closure credit.')
(D/'symbolic-schedule226-resume2.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(dict(schedule_match=True,variants=checked,native_link_credit=False)))
# Exact emitted-source provenance: reproduce only the authorized metadata/import
# port in memory. No emitted or previously proved file is rewritten here.
port=json.loads((D/'port226v3.json').read_text())
t=(D/'raw226-v3/Types.lean').read_text();f=(D/'raw226-v3/Funs.lean').read_text()
pt=t.replace('import Aeneas\n','import Aeneas.Std\nimport Aeneas.Tactic.RustAttributes\n').replace('@[discriminant isize, rust_type','@[rust_type').replace('@[discriminant isize]\n','')
pf=f.replace('import Aeneas\n','import Aeneas.Std\nimport Aeneas.Tactic.RustAttributes\n')
pf=re.sub(r'^import \S+\.Types$', 'import PV_B3P_BytesV3Types226',pf,flags=re.M)
pf+='\n'+''.join('#print axioms PV_B3P_226V3.'+n+'\n' for n in re.findall(r'^def (\S+)',f,re.M))
assert (D/'lean/PV_B3P_BytesV3Types226.lean').read_text()==pt
assert (D/'lean/PV_B3P_BytesV3Emission226.lean').read_text()==pf
assert not re.search(r'index_mut|iter_mut|next_back|index_mut_back',f)
assert re.search(r'pub const P: u32 = 0x7fff_ffff;', (R/'crates/aspis-core/src/field.rs').read_text())
record['checker_source_path']=str(Path(__file__).resolve().relative_to(R))
record['checker_sha256']=sha(Path(__file__))
record['emission_fidelity']=dict(body_edits=False,mutable_writes=0,raw_types_sha256=sha(D/'raw226-v3/Types.lean'),raw_funs_sha256=sha(D/'raw226-v3/Funs.lean'),ported_types_sha256=sha(D/'lean/PV_B3P_BytesV3Types226.lean'),ported_funs_sha256=sha(D/'lean/PV_B3P_BytesV3Emission226.lean'))
plan_source=(D/'lean/PV_B3P_NativePlan226.lean').read_text().split('def plan (p : reference226.OwnedPublic) : List Step :=',1)[1].split('theorem payload_value',1)[0]
plan_expected='[\n  .push (if p.withdrawal then 1#u8 else 0#u8),\n  .fields p.anchor.val, .fields p.nullifier.val, .fields [p.asset_id],\n  .push (if p.withdrawal then 0#u8 else 1#u8),\n  .fields (if p.withdrawal then [] else p.recipient.val),\n  .fields p.change.val, .push (if p.withdrawal then 1#u8 else 0#u8),\n  .fields (if p.withdrawal then [p.withdrawal_amount] else []),\n  .bytes (indexSlice p.next_pair_index), .fields (frontier p.frontier),\n  .fields p.next_root.val, .fields (frontier p.next_frontier) ]\n'
assert toks(plan_source)==toks(plan_expected),'Lean native plan differs from checked native symbolic schedule'
record['native_plan_source_tokens_match']=True
record['differences_and_lean_laws']=[
 dict(difference='Read-only native references and semantic Option fields become copied owned fields; unused pool/domain metadata does not occur in the checked native main',laws=['PV_B3P_ProjectV3Law226.project_exact','PV_B3P_PublicCarrier226V3.roundtrip','PV_B3P_PublicCarrier226V3.reverse_roundtrip']),
 dict(difference='Locally mutated Vec becomes owned Vec state threaded through identical push/extend operations; partial error buffers are unobservable because native returns Err and the Vec is local',laws=['PV_B3P_NativeFieldsVec226.complete_result','PV_B3P_NativeSteps226.complete_result','PV_B3P_NativePlan226.complete_result']),
 dict(difference='The two explicit twenty-row frontier call chains become flattened field sequences, in identical row/lane order',laws=['PV_B3P_ReadTwenty226.same','PV_B3P_NativeIdentities226.frontier_groups','PV_B3P_NativeGroups226.complete_result']),
 dict(difference='Absent optional recipient/amount calls become empty field lists',laws=['PV_B3P_NativeIdentities226.fields_empty','PV_B3P_NativePlan226.payload_value']),
 dict(difference='One canonicality guard and four-byte native endian append become four identical guards followed by individual byte lanes; every failure is Error.Public',laws=['PV_B3P_WordLaw226V3.complete_word','PV_B3P_AppendFields226.repeated_byte_checks','PV_B3P_EndianVerified226V3.word_bytes','PV_B3P_NativeFieldByte226V3.complete_result']),
 dict(difference='Native U64 endian append becomes eight width-bounded shifted byte lanes',laws=['PV_B3P_IndexLane226.native_value','PV_B3P_EndianVerified226V3.index_bytes','PV_B3P_ScalarValue226.index']),
 dict(difference='Reference fixed chunk staging groups the identical sequential byte-check spine into 8/64/1472 cells; all array reads are in bounds',laws=['PV_B3P_ChunkV3Law226.complete_result','PV_B3P_Chunk64Law226.complete_result','PV_B3P_EncodeLaw226.complete_result','PV_B3P_ResultSpine226.collect_append','PV_B3P_BlockProjection226.success_cell','PV_B3P_EncodeSuccess226.success_chunk']),
 dict(difference='Reference evaluates17/45 extra zero padding cells and trims their successful suffix; preceding error/failure/divergence tags are unchanged',laws=['PV_B3P_Padding226.value','PV_B3P_ResultSpine226.padding','PV_B3P_EncodeLength226.success_length','PV_B3P_WholeBuffer226.value']),
 dict(difference='Byte regions use direct indexed projections rather than native nested fields calls; every symbolic cell has the same source field and lane and all dynamic guards have the same order',laws=['PV_B3P_DigestRegionValue226V3.anchor','PV_B3P_DigestRegionValue226V3.nullifier','PV_B3P_LateValue226.recipient','PV_B3P_LateValue226.change','PV_B3P_LateValue226.frontier','PV_B3P_LateValue226.next_root','PV_B3P_LateValue226.next_frontier','PV_B3P_ScalarValue226.asset','PV_B3P_ScalarValue226.amount','PV_B3P_ScalarValue226.index','PV_B3P_Regions226V3.discriminant','PV_B3P_ScalarRegions226.recipient_tag','PV_B3P_ScalarRegions226.withdrawal_tag']),
 dict(difference='Install the callback in the original ProverRwFull carrier, preserving every other operation and both success variants',laws=['PV_B3P_Closure226.complete_result','PV_B3P_Closure226.value','PV_B3P_Closure226.nonvacuity','PV_B3P_Install226V3.source_complete','PV_B3P_Install226V3.error_tag','PV_B3P_Install226V3.fail_tag','PV_B3P_Install226V3.div_tag'])]
if '--finalize' in __import__('sys').argv:
 resolution=json.loads((D/'project-resolution.json').read_text())
 needed=set()
 def visit(m):
  if m in needed or m not in resolution['modules']:return
  needed.add(m)
  for n in resolution['modules'][m]['imports']:visit(n)
 visit('PV_B3P_Closure226')
 assert 'PV_B3P_NativePlan226' in needed
 receipts=[]
 for p in (D/'receipts-resume2').glob('lean-*/receipt/receipt.json'):
  r=json.loads(p.read_text());r['_file']=str(p.relative_to(R));receipts.append(r)
 checked=[]
 for module in sorted(needed):
  a=resolution['modules'][module];assert sha(R/a['path'])==a['sha256']
  good=[r for r in receipts if r['module']==module and r['source_sha256']==a['sha256'] and r['exit_status']==0]
  assert good,('missing exact accepted proof',module)
  r=max(good,key=lambda r:r['attempt']);log=(R/r['_file']).parent/'stdout.log'
  assert 'sorryAx' not in log.read_text()
  assert r['swaps']==0
  checked.append(dict(module=module,source_sha256=a['sha256'],blob=a['blob'],receipt=r['_file'],attempt=r['attempt'],axioms=r['print_axioms']))
 for item in record['differences_and_lean_laws']:
  for law in item['laws']:
   module=law.rsplit('.',1)[0]
   assert module in needed,(law,module)
   entry=next(r for r in checked if r['module']==module)
   log=(R/entry['receipt']).parent/'stdout.log'
   assert "'"+law+"' depends on axioms:" in log.read_text() or "'"+law+"' does not depend on any axioms" in log.read_text(),('law was not audited',law)
 native_receipt=D/'receipts-resume/native226-structural-resume/receipt/receipt.json'
 nr=json.loads(native_receipt.read_text());assert nr['exit_status']==0 and nr['swaps']==0
 assert 'test result: ok' in (native_receipt.parent/'stdout.log').read_text()
 for path,h in json.loads((D/'native226-resume-source-pins.json').read_text()).items():assert sha(R/path)==h,path
 record.update(evidence_class='structural (K-1 substitute)',native_link_credit=True,row_closed=True,row='V243',op=226,checked_lean_modules=checked,retained_obligations=[],finite_validation=dict(classification='same-input native differential; finite validation',comparisons=2884,receipt=str(native_receipt.relative_to(R)),receipt_sha256=sha(native_receipt),reused_unchanged=True),universal_native_machine_equality_claimed=False,trusted_items_added=[],endpoint_scope='Selected callback/source/value requirement only. V165/V167, E1/E2, real RunJoin, client proof-account route and L1/L2/L3 remain substantive.',warning='Structural source argument under ruling(k\u2032), not a Lean theorem of native machine execution or Kani evidence. Compiler/standard-library source reading is explicit; no native equality axiom is introduced.')
(D/'structural226-resume2.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(dict(finalized=record['row_closed'],class_name=record['evidence_class'])))
