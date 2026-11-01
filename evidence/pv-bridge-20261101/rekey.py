"""Re-key the committed census without conflating generated Lean proofs with Rust items."""
from pathlib import Path
import json, hashlib, itertools, subprocess, re
B=Path(__file__).resolve().parent; R=B.parent.parent; D=R/'evidence/pv-dup-20261029'
def load(n): return json.loads((D/n).read_text())
def sha(b): return hashlib.sha256(b).hexdigest()
def git(p,rev='HEAD'): return subprocess.check_output(['git','show',f'{rev}:{p}'],cwd=R)
names=load('nonidentical.json'); sources=load('SOURCES-COMPLETED.json')
rows=[]; pair_counts={}; name_counts={}
for r in names:
 n=r['name']; kind='LEAN_GENERATED'
 if n=='instDiscriminantPoolV1TreeErrorIsize': kind='A'
 if n=='instDiscriminantPoolV1PaymentStatementFormatErrorIsize': kind='A'
 if n=='instDiscriminantErrorIsize': kind="A'"
 pairs=[]
 groups={m:g for g in r['groups'] for m in g['modules']}
 for a,b in itertools.combinations(r['provider_modules'],2):
  ga,gb=groups[a],groups[b]
  if ga['variant_index']==gb['variant_index']: continue
  pairs.append({'left':a,'right':b,'type_equal':ga['type_sha256']==gb['type_sha256'],'value_equal':ga['value_sha256']==gb['value_sha256']})
 pair_counts[kind]=pair_counts.get(kind,0)+len(pairs); name_counts[kind]=name_counts.get(kind,0)+1
 rows.append({'name':n,'origin_class':kind,'providers':{m:sources[m] for m in r['provider_modules']},'nonidentical_provider_pairs':pairs,'rust_key':None if kind=='LEAN_GENERATED' else n,'note':'Generated Lean proof/equation auxiliary; Rust crate/path/features are not applicable.' if kind=='LEAN_GENERATED' else 'See RUST-ORIGINS.json; source-origin classification records extraction wrapper separately.'})
assert len(rows)==112
(B/'REKEYED.json').write_text(json.dumps({'inputs':{n:sha((D/n).read_bytes()) for n in ['nonidentical.json','SOURCES-COMPLETED.json']},'name_counts':name_counts,'nonidentical_provider_pair_counts':pair_counts,'rows':rows},indent=2)+'\n')
# The historical builder crate has NO default feature definition. Default and
# --no-default-features therefore both select the empty aspis-statement set.
manifest=git('crates/aspis-statement/Cargo.toml','0b0e77f5f').decode()
assert not re.search(r'^default\s*=',manifest,re.M)
manifest2=git('crates/aspis-statement/Cargo.toml','0626294e').decode()
assert not re.search(r'^default\s*=',manifest2,re.M)
origins=[
 {'name':'instDiscriminantPoolV1TreeErrorIsize','class':'A','origin_key':['aspis-statement','crates/aspis-statement/src/pool_v1/incremental_merkle.rs',[]],'privacy_span':'32:0-46:1','ndr_span':'32:0-46:1','privacy_extraction_crate':'aspis-statement','ndr_extraction_crate':'aspis-statement','feature_evidence':'builder command has no feature arguments; no default feature in 0b0e77f5f manifest; decoder --no-default-features at 0626294e'},
 {'name':'instDiscriminantPoolV1PaymentStatementFormatErrorIsize','class':'A','origin_key':['aspis-statement','crates/aspis-statement/src/pool_v1/payment_relation.rs',[]],'privacy_span':'128:0-143:1','ndr_span':'lib.rs 39:0-54:1; copied fragment source lines 127-143, bytes 4444-4854','privacy_extraction_crate':'aspis-statement','ndr_extraction_crate':'aspis-withdrawal-validation-extract','ndr_copy':True,'literal_extraction_crate_class':'B','feature_evidence':'builder empty default; wrapper Cargo.toml declares no features; withdrawal --no-default-features','qualification':'A by recorded original Rust item; B if the crate key means the extraction wrapper itself. This copy risk is explicit; no executable-source identity inferred.'},
 {'name':'instDiscriminantErrorIsize','class':"A'",'privacy_origin_key':['aspis-r1-cost-probe','crates/aspis-r1-cost-probe/src/verifier.rs',['private-leaf-salts','prover']],'ndr_origin_key':['aspis-r1-cost-probe','crates/aspis-r1-cost-probe/src/verifier.rs',['r0','private-leaf-salts']],'privacy_span':'20:0-27:38','ndr_span':'lib.rs 846:0-846:88','privacy_extraction_crate':'aspis-r1-cost-probe','ndr_extraction_crate':'aspis-r1-finish-relation-current','ndr_copy':True,'literal_extraction_crate_class':'B','qualification':'A-prime by original verifier item, as D536 explicitly directs; literal wrapper keys differ too. Feature lists are extraction selections, not a recovered complete Cargo dependency feature graph. Three prover-only variants are retained.'}
]
(B/'RUST-ORIGINS.json').write_text(json.dumps({'convention':'Origin crate/path keyed separately from actual extraction/copy crate. No wrapper is silently treated as deployed source. Complete dependency feature metadata has not been recovered.','items':origins,'manifest_hashes':{'builder':sha(manifest.encode()),'decoder':sha(manifest2.encode())}},indent=2)+'\n')
print(json.dumps({'name_counts':name_counts,'nonidentical_provider_pair_counts':pair_counts}))

# Preserve literal extraction-crate keys as the primary pair key.
lookup={v['name']:v for v in origins}
obj=json.loads((B/'REKEYED.json').read_text())
for r in obj['rows']:
 if r['name'] not in lookup:continue
 o=lookup[r['name']]
 if o['name']=='instDiscriminantPoolV1TreeErrorIsize':
  keys={'R1Z.BuilderAdmissionExtracted':o['origin_key'],'AspisR1TerminalDecoder.Types':o['origin_key']}
 elif o['name']=='instDiscriminantPoolV1PaymentStatementFormatErrorIsize':
  keys={'R1Z.BuilderAdmissionExtracted':o['origin_key'],'AspisR1WithdrawalValidation.Types':['aspis-withdrawal-validation-extract','lib.rs',[]]}
 else:
  keys={'AspisR1ProverCommit.Types':o['privacy_origin_key'],'AspisR1FinishRelationCurrent.Types':['aspis-r1-finish-relation-current','lib.rs',['private-leaf-salts','r0']]}
 r['rust_key']=keys
 r['literal_extraction_class']=o.get('literal_extraction_crate_class',o['class'])
obj['literal_extraction_crate_name_counts']={'A':1,"A'":0,'B':2,'LEAN_GENERATED':109}
(B/'REKEYED.json').write_text(json.dumps(obj,indent=2)+'\n')
