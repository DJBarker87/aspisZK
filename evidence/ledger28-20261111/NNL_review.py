"""Independent immutable source/emission/statement/child review; no extraction."""
from pathlib import Path
from types import SimpleNamespace
import json,lzma,hashlib,subprocess,re
E=Path(__file__).resolve().parent;R=Path.cwd();N=E.parent/'tx1-principal-20261111';F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';H=lambda b:hashlib.sha256(b).hexdigest();inputs={}
def raw(path):
 path=str(path);p=Path(path)
 if p.exists():b=p.read_bytes()
 else:
  r=subprocess.run(['git','show','HEAD:'+path],capture_output=True)
  if r.returncode==0:b=r.stdout
  else:
   z=subprocess.check_output(['git','show','HEAD:'+path+'.xz']);b=lzma.decompress(z);assert H(b)==subprocess.check_output(['git','show','HEAD:'+path+'.sha256'],text=True).strip()
 inputs[path]=H(b);return b
def J(path):
 b=raw(path);return json.loads(lzma.decompress(b)if str(path).endswith('.xz')else b)
def put(n,x):(E/('NNL_'+n+'.json')).write_text(json.dumps(x,indent=1)+'\n')
old=J(E.parent/'ledger27-20261111/NNK_LEDGER.json.xz');by={r['row']:r for r in old['rows']};lock=H(subprocess.check_output(['git','show',F+':Cargo.lock']));bc=J('evidence/tx1-owned-20261111/NMT_BC_AUDIT.json');emissions=[];syntax=[]
program=raw('evidence/tx1-owned-20261111/NMT_parameterize.py').decode()
for kind,num in [('tx1',1),('first',2)]:
 base='evidence/tx1-owned-20261111/NMT_extracted/'+kind
 p=J(base+'/NMT_PINS.json');rc=J(f'evidence/tx1-owned-20261111/NMT_E{num:03}/receipt.json')
 assert p['frozen_revision']==F and p['exit']==p['charon_exit']==p['aeneas_exit']==rc['exit_status']==0
 assert p['root_features']==('private-leaf-salts,optimized-terminal,program-build'if kind=='tx1'else'pool-adapter,private-leaf-salts')
 assert p['lock_before']==p['lock_after']==lock
 assert p['candidate_sha256']==H(subprocess.check_output(['git','show',F+':crates/aspis-r1-cost-probe/src/candidate.rs']))
 for name,h in p['outputs'].items():assert H(raw(base+'/'+name))==h,(kind,name)
 assert H(raw(base+'/'+kind+'.llbc'))==p['llbc_sha256']
 s=raw(base+'/raw/NMT_'+kind+'/Funs.lean').decode();assert not re.search(r'\b(?:partial_fixpoint|loop|loop_invariant)\b',s)
 spans=[]
 for z in bc['definitions']:
  if z['function']!=kind:continue
  if 'lines'in z:
   source=subprocess.check_output(['git','show',F+':'+z['file']]);assert H(source)==z['source_sha256']
   segment='\n'.join(source.decode().splitlines()[z['lines'][0]-1:z['lines'][1]]);assert H(segment.encode())==z['span_sha256']
   assert not re.search(r'\bwhile\b|\bloop\s*\{|\bfor\s+\w+\s+in\b',re.sub(r'//[^\n]*|/\*[\s\S]*?\*/','',segment))
  spans.append(z)
 emissions.append(dict(row='TX1:094'if kind=='tx1'else'TX1:328',pins=p,receipt=rc,bc=spans,actual_frozen_source=True))
 class VFile:
  def __init__(self,n):self.n=n
  def read_text(self):return raw(base+'/raw/NMT_'+kind+'/'+self.n).decode()
 class VRoot:
  def __truediv__(self,n):return VFile(n)
 ns=dict(raw=VRoot(),a=SimpleNamespace(function=kind),re=re)
 exec(compile(program[program.index('extern='):program.index("(dest/'Funs.lean').write_text")],'NNL immutable syntax replay','exec'),ns)
 compiled=raw('evidence/tx1-owned-20261111/NMT_lean/NMT_'+kind+'/Funs.lean');assert ns['funs'].encode()==compiled
 syntax.append(dict(function=kind,status='PASS exact bytes',source=base+'/raw/NMT_'+kind+'/Funs.lean',generator_sha256=H(program.encode()),parameterized_sha256=H(compiled),opaque_slots=ns['mapping'],trust='(bm) existing extraction item narrowed by(bc); increased reliance, not removal'))
put('EMISSION_REVIEW',dict(status='PASS',emissions=emissions,new_extraction_runs=0));put('SYNTAX_ASSOCIATION',dict(status='PASS',syntax=syntax))
candidates=[]
for c in J(N/'NNG_CLOSED.json')['candidates']:
 if c['row']not in ['TX1:094','TX1:328']:continue
 children=[]
 for f in by[c['row']]['canonical_callees']:
  matches=[r for r in old['rows']if r['transaction']==by[c['row']]['transaction']and r['function']==f];assert len(matches)==1
  child=matches[0];assert child['status']=='CLOSED'or child['row']=='TX1:094'
  children.append(dict(row=child['row'],function=f,basis_status=child['status'],root_owners=child['root_owners'],required='CLOSED in this same gate, at SAME arguments'))
 receipt=J(N/c['receipt']);assert receipt['exit_status']==0
 module=c['theorem'].split('.')[-2];src=raw(N/(module+'.lean'));assert H(src)==receipt['source_hashes']['NNG_generated/'+module+'.lean']
 candidates.append(dict(**c,gate_admitted=False,gate_status='STATIC_PASS_REPLAY_PENDING',canonical_children=children,basis_obligation_statement_hash=by[c['row']]['obligation_statement_hash'],source_module_sha256=H(src),library_fields='LIB_Instances / LIB_FullInstances concrete CLOSED graphs including F9 total parseShape; no free library parameter',controls='No new native substitution/certificate introduced; (bm) emitted-body route; raw ax2 eight unchanged fidelity fixtures required by this gate'))
put('CANDIDATE_REVIEW',dict(candidates=candidates,gate='PENDING',security_target_established=False))
clauses=[]
for c in candidates:
 for kind in ['caller_domain_obligations','inventory_domain_obligations']:
  for z in by[c['row']]['obligation'][kind]:clauses.append(dict(row=c['row'],kind=kind,original=z,status='PENDING_COMPOSITION_GATE',discharged_by=c['theorem']))
put('CLAUSE_REVIEW',dict(clauses=clauses,revision4=dict(ruling='(bs)',own094=['obs=none','publicDom public','public_bytes.length=1880'],own328=['publicDom public','public_bytes.length=1880'],upward='Caller clause to345; discharged there by RSL.TX1_345.p1880_of_decode / NNG_P1880Discharge.decoder; does not close345'),revision3_R4=dict(status='derived internally094',proof='NNG_TotalParse094.prepare_domain -> NNG_Caller087From094.domain -> RSL.TX1_094.r4_of_scan',same_argument='original proof slice [7031..7495] after SAME successful canonicalScan'),historical_findings=dict(parseShape='SUPERSEDED for current LIB F9; historical contradiction modules never transported',checkpoint_extent='SUPERSEDED by owner-authorized canonical revision4 P1880; no local spec narrowing'),trace=dict(producer='NNG_ProducerFull094.producer',repair='full digest dictionary included at prepare trace call; old NNG_Producer094 is not credited')))
for paths,rev in [(['crates','programs/r1-cost-probe','Cargo.lock'],F),(['programs/aspis-pool'],'b936275465600469312d1f058cdc91ea2a11f3dc')]:
 assert not subprocess.check_output(['git','diff',rev,'HEAD','--',*paths]);assert not subprocess.check_output(['git','diff','HEAD','--',*paths])
put('FROZEN_SOURCE_CHECK',dict(status='PASS',frozen=F,pool='b936275465600469312d1f058cdc91ea2a11f3dc',rebuild_trigger=False,method='git diff frozen HEAD and working tree, all shipped paths byte-identical',ELFs=dict(default='f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4',devnet='63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299',Pool='e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc'),ELF_claim='inherited pins; not rebuilt'))
put('REVIEW_INPUTS',inputs);print('NNL independent static review PASS; composition gate pending')
