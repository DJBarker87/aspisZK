"""Additional checks for the NGY association; inherited predicates unchanged."""
from pathlib import Path
import json,hashlib,re,sys,subprocess
from NGY_io import read,text,raw
E=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def require(p,msg):
 if not p:raise AssertionError(msg)
def attempt(a,passed=True,corrupt=False):
 r=read(E/a/'receipt.json');ad=read(E/(a+'-admission.json'));log=text(E/a/'stdout.log')
 require(ad['exit']==0 and ad['reservation']['allowed'] is True,('admission',a))
 require(r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},('caps',a))
 require(str(r['swaps'])=='0',('swap',a))
 require('timed out' not in log and r['exit_status'] not in [124,137],('excluded resource result',a))
 require(r['exit_status']==0 if passed else r['exit_status']!=0,('verdict',a))
 for n,h in r['source_hashes'].items():require(sha(raw(E/a/'sources'/n))==h,('source pin',a,n))
 if r['kind']=='kani':
  graph=read(E/(a+'-graph-check.json'));lock=read(E/(a+'-lock-check.json'))
  require(graph['graph_matches_frozen'] and not graph['edge_errors'],('graph',a))
  require(lock['unchanged'] and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef',('lock',a))
  require(r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3',('offline optimized',a))
  features=read(E/(a+'-all-crate-features.json'))
  f=next(p['features'] for p in features if p['name']=='aspis-r1-cost-probe')
  require(all(s in f for s in ['default','private-leaf-salts','optimized-terminal','program-build']),('features',a))
  code=text(E/a/'sources/NGY_src/crates/aspis-r1-cost-probe/src/NGY_stages.rs')
  require('static mut' not in code and 'Option<fn' not in code,('K2/K3',a))
  require('KMX_copy_nonoverlapping' in code and 'KMX_copy_from_slice' in code,('KMX',a))
  if corrupt:require('Failed Checks:' in log and 'f_ref' in log and any(f in r['env']['RUSTFLAGS'] for f in ['--cfg NGY_corrupt','--cfg NGY_field_corrupt']),('corruption',a))
  else:require('VERIFICATION:- SUCCESSFUL' in log,('native pass',a))
 elif r['kind']=='lean':
  for line in r['print_axioms']:
   require('sorryAx' not in line and all(re.sub(r'\.\{[^}]+\}$','',x.strip()) in ['propext','Classical.choice','Quot.sound'] for x in re.findall(r'\[([^]]*)\]',line)[0].split(',')) if '[' in line else 'does not depend on any axioms' in line,('axioms',a,line))
 return r

def validate(final=False):
 reused=read(E/'NGY_REUSED.json')
 for path,pin in reused['inputs'].items():
  q=E.parents[1]/path
  require(q.exists() and sha(q.read_bytes())==pin['sha256'],('changed inherited input',path))
 frozen=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:crates/aspis-r1-cost-probe/src/verifier.rs'])
 cut=read(E/'NGY_CUT.json');require(sha(frozen)==cut['frozen_verifier_sha256'] and '\n'.join(frozen.decode().splitlines()[58:60])==cut['frozen_cut'],'frozen source-cut identity')
 require(cut['oracle_cut'].replace('oracle(&mut dot,g[l],scalar,post,reply,&mut log)','dot.push(g[l],scalar)')==cut['frozen_cut'],'source cut substitution')
 require('dot.push' in cut['frozen_cut'] and 'map_err(|_|Error::Parse)?' in cut['frozen_cut'],'complete native error expression')
 for p in E.glob('NGY_*.lean'):
  s=p.read_text();require(not re.search(r'\b(sorry|admit|axiom|native_decide)\b|set_option (maxRecDepth|maxHeartbeats)',s),('forbidden Lean',p.name))
  require('XRn_Join' not in s and 'XRy_ArrayRead' not in s,('forbidden kit',p.name))
 for a in ['NGY_L001','NGY_L002','NGY_L003','NGY_L004']:attempt(a)
 for p,c in [('NGY_K004','NGY_K005'),('NGY_K006','NGY_K007')]:
  x=attempt(p);y=attempt(c,False,True)
  require(x['source_hashes']==y['source_hashes'],('matched source configuration',p,c))
  require(x['module']==y['module'],('matched target',p,c))
 if final:
  matrix=read(E/'NGY_NATIVE_MATRIX.json');covered=set()
  for row in matrix['pairs']:
   a=row['positive'];b=row['control'];x=attempt(a);y=attempt(b,False,True)
   require(x['source_hashes']==y['source_hashes'] and x['module']==y['module'],('matched',a,b))
   require(x['module']=='verifier::NGY_stages::point_'+str(row['point']),('point family',a))
   code=text(E/a/'sources/NGY_src/crates/aspis-r1-cost-probe/src/NGY_stages.rs')
   require('result:Result<(),Error>' in code and 'Out{result,' in code,('full Result',a))
   lo=row['lane_start'];hi=row['lane_end'];flags=x['env']['RUSTFLAGS']
   require((lo,hi)==(0,29) if '--cfg NGY_lower' not in flags and '--cfg NGY_upper' not in flags else ((lo,hi)==(0,15) if '--cfg NGY_lower' in flags else (lo,hi)==(15,29)),('range config',a))
   for lane in range(lo,hi):covered.add((row['point'],lane))
  require(covered=={(p,l) for p in range(6) for l in range(29)},'complete six-point/lane coverage')
  point5=next(r for r in matrix['pairs'] if r['point']==5)
  extra=attempt(point5['additional_field_control'],False,True)
  positive=read(E/point5['positive']/'receipt.json')
  require(extra['source_hashes']==positive['source_hashes'],'field argument control source')
  cut5=cut['point5_oracle_cut'].replace('field_oracle(y1,l,field_reply,&mut field_log,&mut order)','field(y1,l)').replace('dot_oracle5(&mut dot,g[l],scalar,post,push_reply,&mut log,&mut order)','dot.push(g[l],scalar)')
  require(cut5==cut['frozen_cut'],'point5 source erasure')
  roots=read(E/'NGY_AUDIT_ROOTS.json')['roots']
  audit=read(E/'NGY_AUDIT.json');proof=read(E/audit['raw_data']);fixtures=read(E/audit['fixtures_data'])
  require(proof['exit_status']==0 and len(proof['results'])==len(roots) and {r['root'] for r in proof['results']}==set(roots),'complete raw roots')
  require(all(set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for r in proof['results']),'raw axioms')
  wanted={'NEP_Planted.matcher':['NEP_Planted.matchAx'],'NEP_Planted.viaPrivate':['NEP_Planted.privateAx'],'NEP_Planted.proof':['NEP_Planted.proofAx'],'NEP_Planted.viaAux':['NEP_Planted.auxAx'],'NEP_MutateMatch.matcher':[],'NEP_MutatePrivate.viaPrivate':[],'NEP_MutateProof.proof':[],'NEP_MutateAux.viaAux':[]}
  require(fixtures['exit_status']==0 and len(fixtures['results'])==8 and all(r['equal'] and r['walked_axioms']==wanted[r['root']] for r in fixtures['results']),'fixtures')
  baseline={r['module']:r['imports'] for r in map(json.loads,text(E/'NGY_EXPECTED_IMPORTS.jsonl').splitlines())}
  scan=list(map(json.loads,text(E/audit['scan_data']).splitlines()))
  require(len(scan)>13000 and all(not r['dangling'] and not r['duplicate_owners'] and r['imports_match'] and r['imports']==baseline[r['module']] for r in scan),'full coherence scan')
  owners=read(E/'NGY_STATEMENT_ROOTS.json')
  entries=[json.loads(l.split('NGY_CERT_ENTRY ',1)[1]) for l in text(E/'NGY_L029/stdout.log').splitlines() if 'NGY_CERT_ENTRY ' in l]
  require(len(entries)==len(owners) and {r['name'] for r in entries}==set(owners) and all(owners[r['name']]==r['owner'] and r['type'] for r in entries),'kernel type/owner entries')
  require(set(roots)==set(owners)|{'AspisR1.NGU_PreparedClaim.packet','AspisR1.RPx_Deployed.deployed'},'source theorem root coverage')
  fixture_pin=read(E/'NGY_L024/NGY_ProofDriver_BINARY_PIN.json')
  final_pin=read(E/'NGY_L030/NGY_ProofDriver_BINARY_PIN.json')
  require(fixture_pin==final_pin,'same compiled fixture/audit binary')
  for a in audit['final_attempts']:attempt(a)
  require(audit['raw_complete'] and audit['fixtures_pass'] and audit['scan_clean'],'complete audit')
  require(read(E/'NGY_CLOSED.json')['status']=='CLOSED under (ah)','closure')
 print(json.dumps(dict(status='PASS',mode='final' if final else 'focused',checks_added_only=True)))
if __name__=='__main__':validate('--final' in sys.argv)
