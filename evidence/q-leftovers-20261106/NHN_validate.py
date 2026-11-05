"""Read-only inherited gates plus additive NHN closure checks; no inherited writes."""
from pathlib import Path
import json,lzma,hashlib,runpy,copy,re,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1];P=E.parent/'q-field-rows-20261106'
def J(p):
 p=Path(p);return json.loads(p.read_bytes()if p.exists()else lzma.decompress(Path(str(p)+'.xz').read_bytes()))
H=lambda b:hashlib.sha256(b).hexdigest()
def inherited():
 old=runpy.run_path(str(R/'evidence/ledger9-20261105/NGZ_validate.py'))
 base=R/'evidence/ledger9-20261105'
 old['gate'](*[J(base/n)for n in ['NGZ_LEDGER.json','NGZ_AUDIT.json','NGZ_SCAN.json','NGZ_TRUST_USED.json','NGZ_L003-admission.json']])
 n=runpy.run_path(str(P/'NHH_validate.py'))
 n['gate'](*[J(P/name)for name in ['NHH_CLOSED.json','NHH_LEDGER_DELTA.json','NHH_EDGES.json','NHH_AUDIT.json','NHH_NATIVE_VALIDATION.json','NHH_SOURCE_VALIDATION.json']])
def gate(closed,delta,edges,audit,native):
 final=delta['stage']=='final';expected={'TX1:006','TX1:031'}if final else{'TX1:006'}
 fs=closed['functions'];rows=[r for f in fs for r in f['rows']]
 assert set(rows)==set(delta['new_closed_rows'])==expected and len(rows)==len(set(rows))
 assert len(fs)==closed['new_composed_rows']==closed['new_composed_functions']==delta['new_functions']==len(expected)
 assert not closed['headline_target_established']and not closed['trust_removed']and not closed['trust_added']and not closed['generic_pointer_credit']
 assert delta['validator_checks_added_only']and delta['checks_removed']==0 and delta['no_other_status_change']and delta['no_authoritative_graph_or_membership_edit']and delta['retained_trust']
 assert delta['Q_after']=={'total':161,'CLOSED':159+len(expected),'OPEN':2-len(expected)}
 assert delta['global_after']=={'total':599,'CLOSED':315+len(expected),'OPEN':284-len(expected)}
 assert delta['pending']==([]if final else['TX1:031'])
 cm=next(f for f in fs if f['rows']==['TX1:006'])
 assert cm['ruling']=='al'and cm['instantiations']==['M31::inv']and delta['ruling_al_instantiations']=={'TX1:006':['M31::inv']}
 assert cm['model_root']=='NHN_CMInstantiation.packet'and cm['full_partial_result']=='NHN_CMInstantiation.association'and cm['outcome_root']=='NHN_CMInstantiation.outcomes'
 assert cm['native_positive']=='NHN_K001'and cm['matched_control']=='NHN_K002'and cm['rename_pair']==['NHN_K003','NHN_K004']and cm['copy_pair']==['NHN_K005','NHN_K006']
 assert 'batch'in cm['excluded_instantiations']
 if final:
  q=next(f for f in fs if f['rows']==['TX1:031'])
  assert q['native_positive']=='NHH_K055'and q['matched_control']=='NHH_K056'
  assert q['model_root']=='NHN_QNegAssociation.packet'and q['enclosing']=='NHN_QNegAssociation.enclosing'and q['child_domains']=='NHN_QNegAssociation.child_domains'
  assert q['adopted_endpoint']=='AspisR1CurrentWide.field.QM31.sub zero (receiver x)'and q['adopted_consumer'].startswith('NFT_WideNeg.source:')
 assert edges['no_authoritative_graph_edit']and edges['new_closed_edges']==(5 if final else 4)
 assert len(edges['edges'])==(6 if final else 4)
 assert audit['status']=='PASS'and audit['raw_authoritative']and not audit['cold_release_replay']and audit['headline']=='AspisR1.RPx_Deployed.deployed'
 roots={'NHN_CMInstantiation.association','NHN_CMInstantiation.packet','NHN_CMInstantiation.outcomes','AspisR1.RPx_Deployed.deployed'}
 if final:roots|={'NHN_QNegAssociation.scalar','NHN_QNegAssociation.association','NHN_QNegAssociation.enclosing','NHN_QNegAssociation.child_domains','NHN_QNegAssociation.packet'}
 assert {r['root']for r in audit['results']}==roots and len(audit['results'])==len(roots)
 assert all(r['equal']and set(r['walked_axioms'])==set(r['collect_axioms'])<={'propext','Classical.choice','Quot.sound'}for r in audit['results'])
 assert len(audit['fixtures'])==8 and all(r['equal']for r in audit['fixtures'])
 assert all(len(r['walked_axioms'])==1 for r in audit['fixtures'][:4])and all(not r['walked_axioms']for r in audit['fixtures'][4:])
 assert audit['scan']['modules']>=13452 and all(audit['scan'][k]==0 for k in ['dangling','incompatible_owners','import_mismatches'])
 assert native['status']=='PASS'and native['constant']=='M31::inv'and native['callback_invoked']and not native['pointer_assertion']and not native['writable_static']and native['no_native_multiplication']
 assert native['rename_verdicts']==[0,1,0,1]and native['copy_verdicts']==[0,1]and native['frozen_source_files']==735 and native['offline_graph_equal']and native['lock_unchanged']and native['deployed_features']
 assert native['erasure_equal']and native['kmx_patch_sha256']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
 return True
if __name__=='__main__':
 inherited()
 vals=[J(E/n)for n in ['NHN_CLOSED.json','NHN_LEDGER_DELTA.json','NHN_EDGES.json','NHN_AUDIT.json','NHN_NATIVE_VALIDATION.json']];gate(*vals)
 mutations=[('extra row',0,lambda x:x['functions'][0]['rows'].append('TX2:006')),('false headline',0,lambda x:x.update(headline_target_established=True)),('generic callback credit',0,lambda x:x.update(generic_pointer_credit=True)),('wrong instantiation',0,lambda x:x['functions'][0].update(instantiations=['arbitrary'])),('missing zero law',0,lambda x:x['functions'][0].update(outcome_root='')),('missing rename pair',0,lambda x:x['functions'][0].update(rename_pair=[])),('weakened validator',1,lambda x:x.update(checks_removed=1)),('membership edit',1,lambda x:x.update(no_authoritative_graph_or_membership_edit=False)),('wrong Q count',1,lambda x:x['Q_after'].update(CLOSED=162)),('missing edge',2,lambda x:x['edges'].pop()),('missing root',3,lambda x:x['results'].pop()),('nonstandard axiom',3,lambda x:x['results'][0]['walked_axioms'].append('sorryAx')),('raw disagreement',3,lambda x:x['results'][0].update(equal=False)),('missing fixture',3,lambda x:x['fixtures'].pop()),('scan dangling',3,lambda x:x['scan'].update(dangling=1)),('owner mismatch',3,lambda x:x['scan'].update(incompatible_owners=1)),('import mismatch',3,lambda x:x['scan'].update(import_mismatches=1)),('rename unstable',4,lambda x:x.update(rename_verdicts=[0,1,1,0])),('copy control passes',4,lambda x:x.update(copy_verdicts=[0,0])),('wrong KMX',4,lambda x:x.update(kmx_patch_sha256='')),('lock drift',4,lambda x:x.update(lock_unchanged=False)),('feature drift',4,lambda x:x.update(deployed_features=False)),('native multiplication',4,lambda x:x.update(no_native_multiplication=False)),('writable static',4,lambda x:x.update(writable_static=True)),('pointer assertion',4,lambda x:x.update(pointer_assertion=True)),('erasure mismatch',4,lambda x:x.update(erasure_equal=False))]
 if vals[1]['stage']=='final':mutations += [('stand-in endpoint',0,lambda x:x['functions'][1].update(adopted_endpoint='NHN_standin.neg')),('missing enclosing receiver',0,lambda x:x['functions'][1].update(enclosing=''))]
 tests=[]
 for label,i,f in mutations:
  bad=copy.deepcopy(vals);f(bad[i])
  try:gate(*bad)
  except AssertionError:tests.append(label)
  else:raise AssertionError('Accepted mutation '+label)
 # Static reuse and scan/runtime fidelity, with no imported evidence writes.
 for n,pin in J(E/'NHN_REUSE.json').items():
  raw=(R/n).read_bytes()if(R/n).is_file()else subprocess.check_output(['git','show','HEAD:'+n],cwd=R)
  assert H(raw)==pin['sha256'],n
 old=(P/'NHH_Driver.lean').read_text();new=(E/'NHN_Driver.lean').read_text();marker='/-- Standalone runtime avoids';action='  let action : CommandElabM Bool := do'
 assert old.split(marker)[0]==new.split(marker)[0]and old[old.index(action):]==new[new.index(action):]
 walker=R/'evidence/axaudit2-20261102/NEP_WALKER.lean';assert H(walker.read_bytes())==J(E/'NHN_WALKER_PIN.json')['sha256']
 coverage=J(E/'NHN_INSTANTIATION_COVERAGE.json')
 assert coverage['instantiations']==['M31::inv']and not coverage['generic_forwarded_backends_certified']
 assert coverage['incoming']==[{'row':'TX1:005','function':'crates/aspis-core/src/field.rs::CM31::inv'}]
 assert coverage['occurrences']==[{'row':'TX1:006','function':'crates/aspis-core/src/field.rs::CM31::inv_with','transaction':'TX1'}]
 assert set(coverage['absent_functions'])=={'cm31_batch_inverse','cm31_batch_inverse_with','verify_inner'}
 census=J(E/'NHN_CENSUS.json')
 assert [r['input']for r in census]==J(R/'evidence/inv-repair-20261104/NGB_MIR_EDGES.json')['inputs']
 for row in census:
  raw=(R/row['input']['path']).read_bytes();assert H(raw)==row['input']['sha256']
  raw=lzma.decompress(raw);assert H(raw)==row['input']['uncompressed_sha256']
  lines=raw.decode().splitlines();hits=[];fn=''
  for i,line in enumerate(lines):
   if line.startswith('fn '):fn=line
   if any(k in line for k in ['CM31::inv_with(', 'cm31_batch_inverse_with(', 'cm31_batch_inverse(']):hits.append(dict(line=i+1,function=fn,context='\n'.join(lines[max(0,i-4):i+3])))
  assert hits==row['hits']
 core=census[2]['hits'];direct=[h for h in core if '>::inv('in h['function']and 'CM31::inv_with('in h['context']]
 assert len(direct)==1 and 'field::M31::inv as fn(field::M31) -> field::M31'in direct[0]['context']
 assert not census[0]['hits']and not census[1]['hits']
 er=J(E/'NHN_ERASURE.json');assert er['erasure_equal']and er['constant']=='M31::inv'
 for m in ['NHN_CMInstantiation','NHN_QNegAssociation']:
  s=(E/(m+'.lean')).read_text();assert not re.search(r'\b(?:sorry|admit|axiom|native_decide)\b|set_option\s+(?:maxRecDepth|maxHeartbeats)',s)
  assert all('#print axioms '+n in s for n in re.findall(r'^theorem (\w+)',s,re.M))
 for n in range(1,7):
  a=f'NHN_K{n:03}';c=J(E/(a+'.json'));r=J(E/a/'receipt.json');ad=J(E/(a+'-admission.json'));g=J(E/(a+'-graph-check.json'));l=J(E/(a+'-lock-check.json'));sc=J(E/(a+'-source-check.json'))
  assert r['exit_status']==(0 if n%2 else 1)and int(r['swaps'])==0
  assert ad['exit']==0 and ad['reservation']['allowed']is True and g['graph_matches_frozen']and l['unchanged']and sc['frozen_files']==735 and not sc['errors']
  fs=next(x['features']for x in g['selected_closure']if x['name']=='aspis-r1-cost-probe');assert fs==['default','optimized-terminal','private-leaf-salts','program-build']
  assert 'CARGO_NET_OFFLINE'in c['env']and c['env']['CARGO_NET_OFFLINE']=='true'
  log=(E/a/'stdout.log').read_text();assert ('VERIFICATION:- SUCCESSFUL'in log)if n%2 else('VERIFICATION:- FAILED'in log)
 for n in [1,3,5]:
  a=J(E/f'NHN_K{n:03}.json');b=J(E/f'NHN_K{n+1:03}.json');be=dict(b['env']);be['RUSTFLAGS']=be['RUSTFLAGS'].replace(' --cfg NHN_bad_argument','');assert be==a['env']and b['native_command']==a['native_command']
 for p in E.rglob('*'):
  assert p.name!='__pycache__'
  if p.is_file():assert p.stat().st_size<=20_000_000,p
 result=dict(status='PASS',stage=vals[1]['stage'],mutations_rejected=tests,inherited_NGZ_and_NHH_gates=True,checks_removed=0,new_closed_rows=vals[1]['new_closed_rows'],roots=len(vals[3]['results']),scan_modules=vals[3]['scan']['modules'],deployed_target_established=False)
 (E/'NHN_VALIDATION.json').write_text(json.dumps(result,indent=1)+'\n');print(json.dumps(result))
