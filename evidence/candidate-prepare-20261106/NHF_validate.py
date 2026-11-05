#!/usr/bin/env python3
"""Add gates to unchanged NFK admission predicates. Never promote prepare."""
from pathlib import Path
import json,lzma,hashlib,re,sys,importlib.util,copy,subprocess,time,resource
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parent.parent
STANDARD={'propext','Classical.choice','Quot.sound'}
LOCK='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
KMX='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
sha=lambda raw:hashlib.sha256(raw).hexdigest()
load=lambda n:json.loads((E/n).read_text())
def require(c,m):
 if not c:raise ValueError(m)
spec=importlib.util.spec_from_file_location('NHF_NFK',R/'evidence/ledger6-20261104/NFK_validate.py');N=importlib.util.module_from_spec(spec);spec.loader.exec_module(N)
class Support:
 def support(self,v):
  for i in N.walk(v):
   if isinstance(i,dict) and {'path','sha256'}<=i.keys() and i['path'].startswith(('evidence/','docs/')):
    require(sha((R/i['path']).read_bytes())==i['sha256'],'support pin '+i['path'])
def receipt(a):return load(a+'/receipt.json')
def checked(a,expected=0):
 x=receipt(a);ad=load(a+'-admission.json')
 require(ad['exit']==0 and ad['reservation']['allowed'] is True,'admission '+a)
 require(x['exit_status']==expected and int(x['swaps'])==0,'exit/swap '+a)
 require(x['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},'scope '+a)
 for n,h in x['source_hashes'].items():require(sha((E/a/'sources'/n).read_bytes())==h,'archived source '+a+' '+n)
 return x

def validate(cert,delta,audit,closed,edges):
 require(delta['newly_closed']==['TX1:095'] and delta['new_count']==1 and closed['rows']==['TX1:095'],'only eligible leaf may be promoted')
 require(cert['row']=='TX1:095' and not cert['whole_prepare_closed'] and cert['trust_additions']==cert['trust_removals']==[],'scope/trust')
 require(delta['checks_added_only'] and delta['other_status_changes']==delta['trust_additions']==delta['trust_removals']==delta['shipped_source_changes']==[],'additive only')
 require(not delta['headline_security_target_established'] and not delta['elf_rebuild'],'no release claim')
 require(cert['inner_hypotheses_remaining']==[] and not cert['source_association']['source_body_equality_premise'],'residual inner premise')
 N.certificate_checks(Support(),cert)
 basepath=R/delta['baseline'];require(sha(basepath.read_bytes())==delta['baseline_sha256'],'baseline pin')
 base=json.loads(lzma.decompress(basepath.read_bytes()));by={r['row']:r for r in base['rows']};b=by['TX1:095']
 require(len(by)==599 and b['composed_status']=='OPEN','baseline')
 require(cert['function']==b['function'] and cert['frozen_body_sha256']==b['frozen_body_sha256'],'frozen identity')
 body=(E/'NHF_WIDE_FROZEN_BODY.rs.txt').read_bytes();require(sha(body)==b['frozen_body_sha256'],'frozen body bytes')
 # Exactly one actual callee is replaced; disabled corruption switches erase to original bytes.
 native=E/'NHF_K025/sources/NHF_src/crates/aspis-r1-cost-probe/src/NHF_wide.rs';s=native.read_text()
 cut=s[s.index('\n{\n    Ok(View {')+1:s.index('\n// Full byte/Option')].rstrip()
 cut=cut.replace('log.decode','E::from_le_bytes').replace('+usize::from(cfg!(NHF_bad_decode_arg))','').replace('+usize::from(cfg!(NHF_bad_view))','')
 require(cut==body.decode().rstrip(),'actual frozen local cut association')
 require('AspisR1.NHF_ViewInstalled.result' in cert['theorems'] and cert['decoder_stub_law'].startswith('AspisR1.NHF_ViewDecoder.result'),'installed/full decoder law')
 require(cert['native_positive']==['NHF_K018','NHF_K022','NHF_K025'] and cert['native_corruption']==['NHF_K019','NHF_K023','NHF_K026'] and cert['copy_pairs']==[['NHF_K020','NHF_K021'],['NHF_K088','NHF_K089']],'complete native controls')
 require(sha((R/'evidence/kani-mitig-20261028/KMX_copy_stubs.patch').read_bytes())==KMX,'exact KMX patch')
 for pos,neg in [(18,19),(22,23),(25,26),(20,21),(88,89)]:
  p=f'NHF_K{pos:03d}';n=f'NHF_K{neg:03d}';pr=checked(p);nr=checked(n,1)
  require(pr['source_hashes']==nr['source_hashes'] and pr['native_command']==nr['native_command'],'matched control sources/config')
  control={19:'NHF_bad_view',23:'NHF_bad_decode_arg',26:'NHF_bad_reply',21:'NHF_invert',89:'NHF_invert'}[neg]
  env=copy.deepcopy(nr['env']);env['RUSTFLAGS']=env['RUSTFLAGS'].replace(' --cfg '+control,'')
  require(env==pr['env'] and ' --cfg '+control in nr['env']['RUSTFLAGS'],'same configuration with intended mutation only')
  for a,r in [(p,pr),(n,nr)]:
   graph=load(a+'-graph-check.json');lock=load(a+'-lock-check.json');src=load(a+'-source-check.json')
   require(graph['graph_matches_frozen'] and not graph['new_package_tuples'] and not graph['edge_errors'] and graph['lock_sha256']==LOCK,'frozen graph')
   require(lock==dict(before=LOCK,after=LOCK,unchanged=True) and not src['errors'],'lock/source fidelity')
   require(r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3' and '-Copt-level=3' in r['env']['RUSTFLAGS'],'offline optimized')
   require(r['native_command'][r['native_command'].index('--features')+1]=='private-leaf-salts,optimized-terminal,program-build','deployed features')
   text=(E/a/'stdout.log').read_text();require('undetermined' not in text.lower() and 'timed out' not in text.lower(),'terminal native property')
   require(bool(re.search(r'\*\* '+('0' if a==p else '1')+r' of \d+ failed',text)),'precise native verdict '+a)
  require('VERIFICATION:- SUCCESSFUL' in (E/p/'stdout.log').read_text() and 'VERIFICATION:- FAILED' in (E/n/'stdout.log').read_text(),'positive/negative verdict')
 require('line 50,' in (E/'NHF_K026/stdout.log').read_text() and 'decoded reply identity' in s.splitlines()[49],'bad reply hits intended source assertion')
 require('v.round0.len() == 224' in (E/'NHF_K019/stdout.log').read_text(),'wrong returned slice control')
 require('bytes.len() == 32' in (E/'NHF_K023/stdout.log').read_text(),'wrong decoder argument control')
 for mod,slot in cert['lean_modules'].items():
  a=f'NHF_L{slot:03d}';x=checked(a);require(x['module']==mod,'focused target')
  require(sha((E/(mod+'.lean')).read_bytes())==x['source_hashes']['NHF_generated/'+mod+'.lean'],'current theorem pinned to checked source')
  N.standard_prints(x['print_axioms'])
  require('-M7000' in x['command'],'Lean cap')
 require(audit['status']=='PASS_AX2_CONDITION_3' and audit['walker_unchanged'] and audit['standard_axioms_only'] and audit['raw_equals_collect'] and audit['zero_unresolved_constants'],'ax2 obligations')
 require((E/'NHF_WALKER_SOURCE.lean.txt').read_bytes()==(R/'evidence/axaudit2-20261102/NEP_WALKER.lean').read_bytes(),'walker unchanged')
 expected=set(load('NHF_AUDIT_ROOTS.json')['all']);actual=load('NHF_audit/batch0/proof0.json');fixture=load('NHF_audit/fixtures/fixtures.json')
 N.fixtures(fixture['results'])
 require(audit['fixture_binary_unchanged'] and load('NHF_L040/NHF_ProofDriver_BINARY_PIN.json')==load('NHF_L048/NHF_ProofDriver_BINARY_PIN.json'),'same binary fixtures')
 rawpins=load('NHF_RAW_AUDIT_PINS.json');require(len(rawpins)==62,'all raw root and fixture transports')
 for pin in rawpins:
  encoded=(R/pin['path']).read_bytes();require(sha(encoded)==pin['sha256'] and sha(lzma.decompress(encoded))==pin['raw_sha256'],'raw axiom transport')
 for pin in load('NHF_REUSED_SOURCES.json'):
  require(sha((E/pin['local']).read_bytes())==pin['sha256'],'reused source pin')
  old=subprocess.check_output(['git','show',pin['revision']+':'+pin['path']],cwd=R)
  require(sha(old)==pin['sha256'],'reused committed provenance')
 require(len(expected)==54 and {r['root'] for r in actual['results']}==expected,'all theorem and headline audit roots')
 require(all(r['equal'] and r['collect_axioms']==r['walked_axioms'] and set(r['walked_axioms'])<=STANDARD for r in actual['results']),'raw standard axioms')
 for a in ['NHF_L047','NHF_L040','NHF_L048','NHF_L049']:checked(a)
 scan=(E/'NHF_audit/scan/scan.log').read_text();require(scan.strip()=='NFN_SCAN_ZERO_DANGLING','NFX scan exit marker')
 require(audit['loaded_modules']==13479 and len((E/'NHF_LOADED_scan.jsonl').read_text().splitlines())==13479,'loaded module inventory')
 require('import NGK_COMBINED_IMPORT' in (E/'NHF_COMBINED_IMPORT.lean').read_text(),'coherent headline composition')
 raw=lzma.decompress((E/'NHF_CLOSURE_PINS.json.xz').read_bytes());require(sha(raw)==(E/'NHF_CLOSURE_PINS.json.sha256').read_text().strip(),'resolved closure pins')
 N.BASE_CREDITS=base['NEZ_credits'];row=N.materialize_recipe(b,cert,'NHF',edges)
 edge=edges['edges'];require(len(edge)==1 and edge[0]['selected_claims']==by['TX1:048']['selected_claims'],'exact closed callee packet')
 for ob in row['caller_domain_obligations']:
  if 'callee' in ob:
   ob['callee_claims']=edge[0]['selected_claims'];ob['owner_packets']=['NHF','NET']
 row['active_support_receipts']=['evidence/candidate-prepare-20261106/'+f'NHF_K{n:03d}/receipt.json' for n in [18,19,20,21,22,23,25,26,88,89]]
 row['NHF_historical_inventory_domain_obligations']=row['inventory_domain_obligations']
 row['inventory_domain_obligations']=[dict(domain=cert['domain'],status='CLOSED',discharged_by=cert['id'])]
 row.update(NHF_provider='NHF',NHF_certificate=cert,NHF_route='(y) plain / (ai) local callee cut; retained P6/D188 option A',NHF_trust_used=['NativeContractSemanticTransport'])
 require(N.row_checks(row,b,cert)==[],'unchanged NFK row predicates')
 compat=copy.deepcopy(base);barriers={}
 for old in compat['rows']:
  if 'caller_domain_obligations' not in old:
   require(old['composed_status']=='OPEN' and old['bridge_status']=='OPEN','new-schema row cannot bypass admission')
   barriers[old['row']]=copy.deepcopy(old)
   old['caller_domain_obligations']=[dict(id='NHF-unknown-schema:'+old['row'],status='OPEN',discharged_by=None)]
 out=N.admit(compat,{'TX1:095':('NHF',row)},{'TX1:095':cert},{'NHF':['TX1:095']},audit_ok=True)
 for i,old in enumerate(out['rows']):
  if old['row'] in barriers:
   require(old['composed_status']=='OPEN' and old['bridge_status']=='OPEN','new-schema barrier stayed open')
   out['rows'][i]=barriers[old['row']]
 changed=[r['row'] for r in out['rows'] if (r['bridge_status'],r['composed_status'])!=(by[r['row']]['bridge_status'],by[r['row']]['composed_status'])]
 require(changed==['TX1:095'] and next(r for r in out['rows'] if r['row']=='TX1:095')['composed_status']=='CLOSED','additive NFK fixed point')
 require(out['trust_rows']==base['trust_rows'],'retained trust inventory')
 out['NHF_delta']=delta;return out

def main():
 started=time.monotonic()
 cert=load('NHF_CERTIFICATES.json')[0];delta=load('NHF_LEDGER_DELTA.json');audit=load('NHF_AUDIT.json');closed=load('NHF_CLOSED.json');edges=load('NHF_EDGES.json')
 out=validate(cert,delta,audit,closed,edges)
 # Mutation controls prove these added gates deny absent support, open premises,
 # missing controls, wrong source/row/model/scope, trust changes and audit removal.
 mutations=[]
 for name,group,fn in [
  ('parent promotion','delta',lambda x:x.update(newly_closed=['TX1:087'])),
  ('dropped control','cert',lambda x:x['native_corruption'].pop()),
  ('wrong frozen body','cert',lambda x:x.update(frozen_body_sha256='0'*64)),
  ('open inner hypothesis','cert',lambda x:x.update(inner_hypotheses_remaining=['missing callee'])),
  ('desired output premise','cert',lambda x:x['source_association'].update(source_body_equality_premise=True)),
  ('wrong model root','cert',lambda x:x.update(theorems=['parallel_model.result'])),
  ('added trust','cert',lambda x:x.update(trust_additions=['AssumePrepareCorrect'])),
  ('missing ax2','audit',lambda x:x.update(standard_axioms_only=False)),
  ('missing callee edge','edges',lambda x:x.update(edges=[])),
  ('missing closed occurrence','closed',lambda x:x.update(rows=[]))]:
  args=copy.deepcopy(dict(cert=cert,delta=delta,audit=audit,closed=closed,edges=edges));fn(args[group])
  # Recompute review digest, so these exercise gates beyond digest identity.
  if group=='cert':
   c=args['cert'];c['semantic_review_sha256']=sha(json.dumps({k:v for k,v in c.items() if k!='semantic_review_sha256'},sort_keys=True).encode())
  try:validate(**args)
  except (ValueError,KeyError,IndexError) as e:mutations.append(dict(name=name,rejected=True,reason=str(e)))
  else:raise ValueError('mutation accepted: '+name)
 raw=json.dumps(out,sort_keys=True).encode();(E/'NHF_COMPOSED_LEDGER.json.xz').write_bytes(lzma.compress(raw,preset=6));(E/'NHF_COMPOSED_LEDGER.json.sha256').write_text(sha(raw)+'\n')
 result=dict(exit_status=0,newly_closed=['TX1:095'],prepare_status='OPEN',checks_added_only=True,mutations=mutations,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),validator_sha256=sha(Path(__file__).read_bytes()),ledger_sha256=sha(raw),trust_changes=[])
 result.update(target='NHF_validate.py additive row admission plus ten denial controls',wall_seconds=time.monotonic()-started,peak_rss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,swaps=resource.getrusage(resource.RUSAGE_SELF).ru_nswap,source_tree_dirty=True,print_axioms='N/A: receipt validation; formal roots in NHF_AUDIT.json')
 (E/'NHF_VALIDATION.json').write_text(json.dumps(result,indent=1)+'\n');print(json.dumps(result))
if __name__=='__main__':main()
