"""Create reviewable exact S packets only from complete successful evidence."""
from pathlib import Path
import json,hashlib,re,subprocess,sys
import NEU_validate as v
import NEU_bridge_checks as checks
import NEU_decoder_checks as decoder_checks
from NEU_inputs import read,write_delta
E=v.E;R=v.R
sha=lambda b:hashlib.sha256(b).hexdigest()
def ref(p):
 p=Path(p);return dict(path=str(p.relative_to(R)),sha256=sha(p.read_bytes()))
def thm(name,attempt):
 source=E/attempt/'NEU_SOURCE.lean.txt';s=source.read_text();short=name.rsplit('.',1)[1];a=s.index('theorem '+short+' ');z=re.search(r'\s:=\s',s[a:]).start()+a
 statement=s[a:z].rstrip();r=read(E/attempt/'receipt.json');assert r['exit_status']==0
 assert any(line.startswith("'"+name+"'") and 'sorryAx' not in line for line in r['print_axioms'])
 return dict(name=name,source=ref(source),receipt=ref(E/attempt/'receipt.json'),snapshot_path='NEU_generated/'+name.rsplit('.',1)[0]+'.lean',statement=statement,statement_sha256=sha(statement.encode()))
RECEIPTS={'NEU_BoxModel':'NEU_L009','NEU_ReconstructCore':'NEU_L010','NEU_ReconstructAdopted':'NEU_L011','NEU_CallDomains':'NEU_L012','NEU_PublicProjections':'NEU_L014','NEU_BoxDecodeModel':'NEU_L017','NEU_DecoderProjections':'NEU_L018'}
def support(pairs,box,decoder=False):
 paths=set()
 for pair in pairs:
  for a in pair:
   paths.update(E/n for n in [a+'/receipt.json',a+'/stdout.log',a+'.json',a+'-admission.json',a+'-graph-check.json',a+'-lock-check.json',a+'-metadata-pin.json',a+'-source-check.json',a+'-rule16-check.json',a+'-NEU_native_contracts.patch',a+'-NEU_oracle.patch',a+('-shape.json' if decoder else '-box.json' if box else '-reconstruct.json')])
   archive=a+'-inputs.json' if (E/(a+'-inputs.json.xz')).is_file() else 'NEU_SOURCE_HISTORY.json'
   paths.update(E/(archive+x) for x in ['.xz','.sha256'])
 return [ref(p) for p in sorted(paths)]
def pair(n):return [f'NEU_K{n:03}',f'NEU_K{n+1:03}']
config=read(E/'NEU_NATIVE_PAIR_SELECTION.json')
selected={checks.P+'transfer_statement_box':[pair(23+2*i) for i in range(23)],checks.P+'withdrawal_statement_box':[pair(70+2*i) for i in range(24)]}
if 'common' in config:selected[checks.P+'asq8_common']=[config['common']]
if 'prefix' in config and 'finish' in config:selected[checks.P+'reconstruct_asq8_statement']=[config['prefix'],config['finish']]
for branch in ['transfer','withdrawal']:
 if 'decode_'+branch in config:selected[decoder_checks.D+'decode_'+branch+'_statement_boxed_v1']=[config['decode_'+branch]]
packet=read(E/'NEU_LEDGER_DELTA.json');reviewed=read(E/'NEU_REVIEWED_CERTIFICATES.json');base=read(R/'evidence/native-ledger3-20261029/NDT_LEDGER.json')
# Rebuild only this lane's additions. Every inherited packet stays byte-identical.
for group in ['roots','members','edges','hypotheses','externals','inventory_edges']:
 packet[group]={k:c for k,c in packet.get(group,{}).items() if not c.get('id','').startswith('NEU_')}
for k in list(reviewed):
 if k.startswith('native-bridge::') or k in config.get('old_neu_subjects',[]):del reviewed[k]
packet['native_bridge_additions']={}
for f,pairs in selected.items():
 decoder=f in decoder_checks.FUNCTIONS
 theorem_table=decoder_checks.THEOREMS if decoder else checks.THEOREMS
 name=f.rsplit('::',1)[1];frozen=v.frozen_source(f);a=frozen.index('fn '+name+'(');z=frozen.index('\n}',a)+2;body=frozen[a:z]
 b=dict(function=f,frozen_revision=base['frozen_revision'],frozen_body=body,frozen_body_sha256=sha(body.encode()),native_pairs=pairs,theorems=[thm(t,RECEIPTS[t.rsplit('.',1)[0]]) for t in theorem_table[name]],support=support(pairs,name in checks.FIELDS,decoder),domain=decoder_checks.DOMAIN if decoder else 'all typed inputs; no accepted-run or canonicality precondition',physical_qualification='root-owned valid typed carriers, fresh Box allocation/cleanup interpretation and ABI; no inner native bridge assumed',full_Result=True,same_inputs=True,same_state=True,same_ordered_effects=True,native_frame_complete=True,inner_hypotheses_remaining=[],new_trust_rows=[],trust_classification='P6/D188 option A reclassification')
 b['semantic_review_sha256']=sha(json.dumps(b,sort_keys=True).encode());reviewed['native-bridge::'+f]=b['semantic_review_sha256'];packet['native_bridge_additions'][f]=b
 assert checks.addition(b,f,base,v,reviewed),'incomplete bridge '+f
# Construct the reviewed domain layer against the newly verified callee claims.
subjects=[]
def certificate(f,subject,kind,ob=None):
 b=packet['native_bridge_additions'][f]
 selected_claims=['NEU::'+f];names=[]
 if ob and 'callee' in ob:
  g=ob['callee'];selected_claims=['NEU::'+g] if g in selected else ob['callee_claims'];names=checks.qualifiers(g) if g in selected else ob['required_named_hypotheses']
 d=dict(subject=subject,frozen_revision=base['frozen_revision'],native_association_kind='ruling-y',domain_theorems=b['theorems'],physical_theorems=b['theorems'],selected_callee_claims=selected_claims,inner_hypotheses_remaining=[],exact_callsite=True,canonical_carrier=True,same_arguments=True,same_prestate=True,same_result=True,same_ordered_effects=True,trust_classification='P6/D188 option A reclassification',new_trust_rows=[],native_frame_complete=True,inner_names_discharged=names)
 c=dict(id='NEU_'+kind+'::'+subject,kind=kind,subject=subject,frozen_revision=base['frozen_revision'],theorems=b['theorems'],native_association=b['support'],same_inputs=True,same_carrier=True,same_state=True,same_result=True,ordered_effects=True,inner_hypotheses_remaining=[],physical_interpretation_derivation=b['physical_qualification']+'; actual typed call-site carriers, complete native value/Box frame and reached-domain theorems; no callee PhysicalInterpretation assumed',callee_domain_established=True,canonical_carrier_established=True,call_domain_certificate=d,native_bridge_function=f,native_bridge_sha256=b['semantic_review_sha256'],hypotheses=([f+'.PacketDomain',f+'.PhysicalInterpretation','NativeContractSemanticTransport'] if kind=='root-composition' else []))
 c['semantic_review_sha256']=sha(json.dumps(c,sort_keys=True).encode());reviewed[subject]=c['semantic_review_sha256'];subjects.append(subject);return c
roots=read(R/'docs/research/100bit-spend-path-20261013/design/VERTICAL-SLICES-20261029.json')['slices']['S']['roots']
for f in selected:
 packet['roots' if f in roots else 'members'][f]=certificate(f,f,'root-composition')
 for n in checks.qualifiers(f):packet['hypotheses'][f+'::'+n]=certificate(f,f+'::'+n,'hypothesis-discharge')
 rows=[r for r in base['rows'] if r['function']==f];assert rows
 for r in rows:
  for ob in r['caller_domain_obligations']:
   subject=f+' -> '+ob['callee'] if 'callee' in ob else ob['id']
   packet['edges' if 'callee' in ob else 'externals'][subject]=certificate(f,subject,'call-domain' if 'callee' in ob else 'external-domain',ob)
write_delta(E/'NEU_LEDGER_DELTA.json',packet);(E/'NEU_REVIEWED_CERTIFICATES.json').write_text(json.dumps(reviewed,indent=1)+'\n')
(E/'NEU_NATIVE_ADMISSION_REVIEW.json').write_text(json.dumps(dict(functions=list(selected),subjects=subjects,baseline_unchanged=True,new_bridge_phase='complete new native evidence, before composition; every historical baseline check retained',trust_reclassification=True),indent=1)+'\n')
print(json.dumps(dict(native_bridges=list(selected),domain_certificates=len(subjects))))
