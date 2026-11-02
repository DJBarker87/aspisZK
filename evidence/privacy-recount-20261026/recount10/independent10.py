from audit10 import *
manifest.update({x['ref']+':'+x['path']:x for x in json.loads((P/'manifest.json').read_text())})
def get(k,p):
 s=txt(k,p);assert s is not None,(k,p);return s
out={}
for id,th in [('V201','source_reference'),('V220','source_reference'),('V237','complete')]:
 p='docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RDCD4_'+id+'.lean';s=get('rw',p)
 assert 'theorem '+th in s and '#print axioms '+th in s
 out[id]={'disposition':'CONFIRM qualified restoration','statement_source':manifest['rw:'+p],'full_statement':s[s.index('theorem '+th):].split(' := by')[0],'not_claimed':'native RunJoin, physical observations, compiler/executable or endpoint privacy'}
# Check admissions and section6 fields of ALL rdcd4 launched receipt directories.
receipts=[];bad=[];summary_axioms=[]
for p in tree('rw'):
 if not re.fullmatch(r'evidence/pv-rdcd4-20261029/lean-\d+/receipt.json',p):continue
 r=json.loads(read('rw',p));prefix=p.rsplit('/',1)[0];a=[]
 for n in ['admission-before.json','admission-launch.json','admission-barrier.json']:
  b=read('rw',prefix+'/'+n)
  if b:
   v=json.loads(b);assert v.get('allowed') is True,(p,n);a.append(n)
 assert a,(p,'no admission')
 for key in ['target','exit','wall','peak_rss_kib','swap','source_revision','axioms']:assert key in r,(p,key)
 receipt={'path':p,'receipt':r,'admission_inputs':a,'axioms_kind':'SUMMARY-BASED'};receipts.append(receipt)
 if r['exit']==0:
  lines=r['axioms'] if isinstance(r['axioms'],list) else [r['axioms']]
  assert not any('sorryAx' in x for x in lines),p
  summary_axioms.extend(lines)
 else:bad.append(p)
(P/'receipt-audit10.json').write_text(json.dumps({'rdcd4_receipts':receipts,'failed_uncredited':bad,'raw_walk_claimed':False},indent=1)+'\n')
# Old/new consumer conclusions compared verbatim, not only theorem names.
def source(k,n):return get(k,'docs/research/v8-r0-zk-20261009/lean/R1Z/'+n+'.lean')
a=source('runjoin','PV_RunJoin_NativeQueryDischarge66');b=source('runjoin','PV_RunJoin_NativeFinishDischarge69')
def conclusion(s):return s.split('store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T) :',1)[1].split(' :=',1)[0]
assert conclusion(a)==conclusion(b)
def links(s):return re.findall(r'PV_RunJoin_Link_\w+',s.split('def Remaining',1)[1].split('theorem links',1)[0])
la,lb=links(a),links(b);assert set(la)-set(lb)=={'PV_RunJoin_Link_FinishContext'} and len(la)==8 and len(lb)==7
assert 'PV_RunJoin_NativeQueryAppend66.complete' in a and 'PV_RunJoin_NativeFinishContext69.complete' in b
out['consumers']={'QueryAppend':'CONFIRM nine to eight; construction in links/publication, unchanged actual-native conclusion','FinishContext':'CONFIRM eight to seven; conclusion bytes equal QueryAppend consumer','remaining':lb,'publication_conclusion_sha256':hashlib.sha256(conclusion(b).encode()).hexdigest(),'nonemptiness':'unproved; v-prime reduced to actual domain non-emptiness','counted_rows_removed':0}
# Mechanical statement-level strengthening checks; no kernel execution.
core=get('rw','lean/PV_EVH_Core.lean');mc=get('rw','lean/PV_MEAS_Core.lean');md=get('rw','lean/PV_MEAS_Deployed.lean');legacy=get('rw','lean/PV_MEAS_Legacy.lean')
assert 'abbrev Observer := PV_EVH_Core.Observer' in mc
assert '(simE (h).transport B outputs x)' in core and '(simE (h).transport B outputs x)' in mc
assert 'PV_EVH_Core.real' in md and 'PV_EVH_Core.ideal' in md
assert '(PV_EVH_Core.bound template outputs x : ℝ)' in md and '< 1 / 2^100' in md
assert 'Measurable adv.decide' in md and 'structure Links : Prop' in md
adapter=legacy.split('def ofLegacy',1)[1].split('/-- Every old',1)[0]
forwarded=re.findall(r'^  (\w+) := rt\.(\w+)$',adapter,re.M);assert len(forwarded)==22 and all(x==y for x,y in forwarded)
assert 'theorem links_of_legacy' in legacy and 'theorem finite_uniform_corollary' in legacy
trustpath='docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_TrustItems.lean';trust=get('rw',trustpath)
fields=re.findall(r'^  (entropy_law|entropy_kernel|observation)\s*:',trust,re.M);assert fields==['entropy_law','entropy_kernel','observation']
# Compare the event carrier/simulator to the adopted original; full Core unchanged.
original=txt('b51b1040f2','lean/PV_EVH_Core.lean');assert original==core
out['measured']={'disposition':'CONFIRM statement-level strengthening','observer':'same PV_EVH_Core.Observer, Signal × Observation A; measurable Boolean decisions','simulator':'same simE, completion/public input; no witness argument in ideal','bound':'same PV_EVH_Core.bound, real cast, strict < 1/2^100','T':fields,'Core_byte_identical_to_adoption':True,'forwarded_runtime_fields':forwarded,'finite_corollary':'PV_MEAS_Legacy.finite_uniform_corollary recovers full rational finite statement without calling old headline','ordinary_new_obligations':['measurability','joint pushforward/ConditionalLaw','exact common coupling'],'native_links_discharged':0,'raw_release_audit':False}
# Record exact final focused outputs, including the failed superseded adapter.
for n in [73126,73130,73197,73198,73199]:
 for suffix in ['receipt-'+str(n)+'.json','out-'+str(n)+'.log','admission-'+str(n)+'.json']:
  read('rw','evidence/pv-meas2-20261029/'+suffix)
# V242 sole whole-row class A, explicit owner adoption and unchanged restoring law.
fs=get('19e3328e8eeac847fc1895cc813cdf262076840e','evidence/pv-fscan-20261028/CLASSIFY.md')
owner=get('research','design/PV-OWNER-PACKET-20261027.md')
assert '| V242 | A |' in fs and '**D381/D386 (compiler cohort, V242): ADOPTED.**' in owner
out['V242']={'disposition':'CONFIRM scoped restoration under D502/V370','source_class':'A at whole retained boundary; four pure byte-identical project bodies','owner_adoption':True,'theorem':'R1Z.PV_CB3_Op225Source.op225_source','evidence_class':'RECLASSIFICATION within tool/compiler trust; compiler preservation remains'}
res=get('b3p6','evidence/pv-b3p6-20261028/lean/PV_B3P_BridgeResidual557227.lean')
assert '(wrapper : DeployedWrapper557 base ops)' in res
out['V244']={'status':'OPEN','local_associations':36,'total_local_functions':36,'residual':'PV_B3P_Closure557227.DeployedWrapper557 base ops','unconditional_bridge':False,'source':manifest['b3p6:evidence/pv-b3p6-20261028/lean/PV_B3P_BridgeResidual557227.lean']}
find=get('research','evidence/axaudit2-20261102/NEP_FINDINGS.md');driver=get('research','evidence/axaudit2-20261102/NEP_Driver.lean')
assert 'importAll := true' in driver and 'level := .private' in driver
assert 'hard error' in find and '11,379,716' in find
out['D565']={'disposition':'CONFIRM correction; non-vacuity witness NOT established on coherent build','source':'research:evidence/axaudit2-20261102/NEP_FINDINGS.md','witness_root':'AspisR1.NDR_CombinedAudit.sourceOnHeadline','missing':'AdapterRw.r1_pool_adapter.owned.stage2_owned.match_3','NDR_authority':'INCOHERENT, excluded','90000':'successful elaboration only, superseded as joint-coherence evidence','90001':'INCOMPLETE; summary-based standard axioms do not cure missing constant','NEP_R900':{'exit':1,'wall_seconds':40.06736564391758,'peak_rss_kib':11379716,'swap':0,'revision':'d3602156d620dbb8878a671b33b561919a9e2f75'},'no_new_audit':True}
out['client']={'combined_bundle':'D537 ADOPTED da36d6aa36f8566ffa2ce7276546941c745bcd6325613c5a98c5517328b7def0; unchanged release ELFs','bundle_timing':'D359(A) paired, throttled; transfer14.834947s +3.3167%, withdrawal14.310064s -1.3159%; no universal latency claim','user_client':'owner adopts scope U, not an all-gates-pass executable','user_candidate':'9310ca5e3dcb3b2e8d7ac51312d6737aa465d2f8321fdaef6928114ffa38538e','differential':'N75145 1000/1000 pairs,2000 real calls, finite evidence','timing':'N75149 invalid,0 accepted pairs','full_entry':'emission passes; faithful external25 types/119 ops and decoder shift block compilation; formatting loses required operands','checksum':'31/31, not full release closure','audit':'three compiled roots only; no raw full-entry audit or new NEP invocation'}
(P/'independent-audit10.json').write_text(json.dumps(out,indent=2)+'\n');save();print('Independent statement/receipt checks PASS; historical Lean receipts',len(receipts),'failed excluded',len(bad))
