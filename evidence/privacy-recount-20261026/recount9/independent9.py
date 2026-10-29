from auditlib9 import *
import struct,difflib,datetime
out={}; checks=[]
def J(path,k='rw'):return json.loads(read(k,path))
def check(name,value):
 checks.append(dict(check=name,pass_=bool(value)))
 if not value:raise AssertionError(name)
# Exact native bytes are re-constructed from literal source, not a fingerprint equality.
bc=J('evidence/pv-ownh-20261029/byte-comparison.json');nat=J('evidence/pv-ownh-20261029/native-result.json')
s,_=module('rw','R1Z.PV_RDB2D_PV_B3P_Sorted133');lit=re.search(r'^def expected\s*:\s*List Nat\s*:=([^\n]+)',s,re.M).group(1);words=[int(v) for v in re.findall(r'\d+',lit)]
s,_=module('rw','R1Z.PV_RDB2D_MaskChunk13');mask=[int(v) for v in re.findall(r'(\d+)#16',re.search(r'def after\s*:.*?:=\s*\[([^]]+)\]',s).group(1))]
for id,ws,run,b in zip(['V229','V230'],[words,mask],nat['runs'],bc['runs']):
 raw=b'\0'+struct.pack('<Q',len(ws))+b''.join(struct.pack('<H',w) for w in ws);actual=bytes.fromhex(re.search(r'result=([0-9a-f]+)',run['stdout']).group(1))
 check(id+' literal/native every-byte equality',run['exit']==0 and raw==actual==bytes.fromhex(b['result_hex']) and hashlib.sha256(raw).hexdigest()==b['result_sha256'])
 out[id]=dict(verdict='CONFIRM qualified singleton-value restoration',canonical_result_bytes=len(raw),word_count=len(ws),result_sha256=hashlib.sha256(raw).hexdigest(),evidence_class=bc['evidence_class'],scope='Successful returned value only. Source influence/address/channel(iii) argument reviewed in STATIC-CHECK; runtime/allocator and V370 remain. Not exhaustive allocator/timing/observation validation.')
check('mask expansion exactly equals rows',[16*i+j for i,m in enumerate(mask) for j in range(16) if m&(1<<j)]==words)
cp=J('evidence/pv-ownh-20261029/crate-source-pins.json')
for x in cp['files']:check('ownh crate '+x['path'],hashlib.sha256(read('rw',x['path']).encode()).hexdigest()==x['sha256'])
check('85 identical crate sources',len(cp['files'])==85)
# Proof-only authority exception: check the whole source, not just signature hashes.
hist='e030a78a739b65afe67a6e2641be1c8b3e25cb70'
a=subprocess.check_output(['git','show',hist+'^:'+R+'R1Z/PrivacyR1HeadlineV2.lean'],text=True);b=read('rw',R+'R1Z/PrivacyR1HeadlineV2.lean');c=read('research',R+'R1Z/PrivacyR1HeadlineV2.lean')
diff=list(difflib.ndiff(a.splitlines(keepends=True),b.splitlines(keepends=True)));delta=[x for x in diff if x.startswith(('- ','+ '))];check('V2 whole delta exactly one redundant rfl removed',a.replace('      rfl)','      )',1)==b and len(delta)==2);check('research/candidate identical V2',b==c)
identity=J('evidence/pv-diag5-20261029/statement-identity.json');check('V2 recorded hashes',hashlib.sha256(a.encode()).hexdigest()==identity['ejr_sha256'] and hashlib.sha256(b.encode()).hexdigest()==identity['tracked_sha256']);out['h5_double_prime']=dict(verdict='CONFIRM proof-only authority supersession, not native closure',old_sha256=identity['ejr_sha256'],new_sha256=identity['tracked_sha256'],source_delta=delta,statement_identity=identity['declarations'])
# Body identities are after expansion; no fuzzy similarity value earns credit.
x=J('evidence/pv-b3p6-20261028/resume12/identity-audit.json','b3p6');check('43 body records',len(x['bodies'])==43)
for v in x['bodies']:check('postmacro identity '+v['family']+v['key'],v['post_macro_identity'] and v['source']['token_sha256']==v['owned']['token_sha256'] and v['source']['expanded_body_sha256']==v['owned']['expanded_body_sha256'])
bound=[v for v in x['bodies'] if v['bound']];reject=[v for v in x['bodies'] if not v['bound']];check('36 bound / 7 provenance failures',len(bound)==36 and len(reject)==7 and all(v['exact_extraction'] and v['model_declarations'] for v in bound))
outputs=J('evidence/pv-b3p6-20261028/resume12/aeneas-outputs.json','b3p6');check('fresh exact 3 downstream extractor outputs',len(outputs)==3 and all(v['byte_identical'] and v['sha256']==v['old_sha256'] for v in outputs))
out['b3p6-1']=dict(verdict='CONFIRM reclassification to raw extracted bodies only',count=36,failed_provenance=[v['key'] for v in reject],outputs=outputs,qualification='Token identity alone is insufficient: name resolution, dependency semantics, mutable restorations and compiled API ports stay separate. Fresh exact extraction plus postmacro identity justifies existing tool-trust label, not Rust proof or complete cone certificate. 79 is conservative.')
# Re-audit raw section6 receipts and source hashes at fixed pins.
receipts=[]
def receipt(path,k='rw'):
 z=J(path,k);ex=z.get('exit',z.get('exit_code',z.get('exit_status')));check(path+' exit0',str(ex)=='0')
 ax=z.get('axioms',z.get('print_axioms',[]));ax='\n'.join(ax) if isinstance(ax,list) else ax
 for names in re.findall(r'depends on axioms:\s*\[([^]]*)\]',ax):
  names=re.sub(r'\.\{[^}]*\}','',names);check(path+' standard axioms',all(v.strip() in ['propext','Classical.choice','Quot.sound'] for v in names.split(',') if v.strip()))
 check(path+' no sorryAx','sorryAx' not in ax)
 src=z.get('source',{});sp=z.get('source_path',src.get('path'));sh=z.get('source_sha256',src.get('sha256'))
 if sp and sh:check(path+' current pinned source hash',hashlib.sha256(read(k,sp).encode()).hexdigest()==sh)
 receipts.append(dict(evidence=path,**z));return z
for w,ids in [('ownh',[63853,63897,63898,63899]),('rdb2h',[64397,64398,64399]),('rdcd3',[60637,60653,60655,60691,60697,60698,60699])]:
 date='20261028' if w=='rdcd3' else '20261029'
 for id in ids:receipt(f'evidence/pv-{w}-{date}/lean-{id}/receipt.json')
for id in [62012,62013,62014,62112,62113]:receipt(f'evidence/pv-fix-20261028/receipt-{id}.json')
for id in [65397,65398,65399]:receipt(f'evidence/pv-b3p6-20261028/resume12/receipts/lean-{id}/receipt/receipt.json','b3p6')
for id in range(65000,65011):
 # diag has flat receipts
 receipt(f'evidence/pv-diag5-20261029/lean{id}-receipt.json')
receipt('evidence/pv-fib-20261029/receipt-67504.json');receipt('evidence/pv-fib-20261029/receipt-67502.json')
# Exact-path gate and full unchanged output comparison.
comp=J('evidence/pv-rdb2h-20261029/comparison.json');check('88 rebuilt/no differences',comp['rebuilt']==88 and all(not comp[k] for k in ['object_differences','missing_rebuilds','rebuilt_dependency_mismatches']))
for id in ['V256','V257']:out[id]=dict(verdict='CONFIRM scoped structural restoration',exact_environment=comp,retained='V370/D381/D386, original API and source continuation, complete Result and library/native world boundary')
# Admissions are reviewed separately from successful elaboration.
admissions=[]
for w,date,ids in [('ownh','20261029',[63853,63897,63898,63899]),('rdb2h','20261029',[64397,64398,64399]),('rdcd3','20261028',[60637,60653,60655,60691,60697,60698,60699])]:
 for id in ids:
  for name in (['admission-before.json','admission-barrier.json'] if w=='rdcd3' else ['admission-launch.json','admission-barrier.json']):
   path=f'evidence/pv-{w}-{date}/lean-{id}/{name}';v=J(path);check(path+' allowed',v.get('allowed') is True);admissions.append(dict(path=path,allowed=v['allowed'],utc=v.get('utc')))
for id in [62012,62013,62014,62112,62113]:
 p=f'evidence/pv-fix-20261028/admission-{id}.json';v=J(p);check(p+' allowed',v['allowed'] is True);admissions.append(dict(path=p,allowed=True,utc=v.get('utc')))
for id in [60630,60643]:
 path=f'evidence/pv-rdcd3-20261028/lean-{id}/admission-history.jsonl';hist=[json.loads(v) for v in read('rw',path).splitlines()];admissions.append(dict(path=path,history=[{k:v.get(k) for k in ['utc','allowed','exit','admission']} for v in hist]))
cd=J('evidence/pv-rdcd3-20261028/cooldown-audit.json');check('rdcd3 >=180s no cooldown violations',not cd['violations'] and cd['minimum_gap_seconds']>=180)
# Failed logs never count as support; independently census success/failure sorryAx.
failed_sorry=[];successful_sorry=[]
for v in list(manifest):
 if v['ref']!='rw' or not re.match(r'evidence/pv-rdcd3-20261028/lean-\d+/receipt.json$',v['path']):continue
 z=J(v['path']);ax=str(z.get('axioms',z.get('print_axioms','')))
 if 'sorryAx' in ax:(failed_sorry if z.get('exit')!=0 else successful_sorry).append(v['path'])
check('no credited rdcd3 sorryAx',not successful_sorry)
out['V213']=dict(verdict='RESTORE scoped row despite worker OPEN',binding_attempt=62012,source_attempt=62112,audit_attempt=62113,qualification='17 aggregate consumers unfinished; old41466 stays void; source62112 and audited exact/reference laws use compliant rebuilt closure. Final release replay still open.')
for id in ['V217','V260','V265']:out[id]=dict(verdict='CONFIRM scoped structural restoration',complete_statement='closing-source-index9.json#'+id,quarantine='V265 pointer Kani not recredited',retained='No observer/world/panic diagnostic or binary theorem; standard axioms and source mapping only')
out['admissions']=admissions;out['rdcd3_cooldown']=cd;out['rdcd3_failed_sorryAx_receipts']=failed_sorry;out['checks']=checks
(P/'independent-audit9.json').write_text(json.dumps(out,indent=1)+'\n');(P/'receipt-audit9.json').write_text(json.dumps(receipts,indent=1)+'\n');(P/'independent-manifest9.json').write_text(json.dumps(manifest,indent=1)+'\n');print('Independent checks',len(checks),'PASS; receipts',len(receipts))
