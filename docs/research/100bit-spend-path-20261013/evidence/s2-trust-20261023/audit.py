import json,pathlib,re,hashlib,subprocess
p=pathlib.Path(__file__).resolve().parent
lean=p.parents[1]/'lean'
s=(lean/'S2TrustedSdkBorrow.lean').read_text()
body=s.split('structure S2TrustedSdkBorrow ',1)[1].split('/-- Identity interpretation:',1)[0]
fields=re.findall(r'^  (\w+) :',body,re.M)
expected='account_data_cell cell_payload cell_counter shared_ok shared_err exclusive_ok exclusive_err shared_deref exclusive_deref guard_move shared_drop exclusive_drop error_move_drop borrow_frame guard_liveness'.split()
assert fields==expected,(fields,expected)
for forbidden in ['S2CallerFacts','dV_frozen2','accepted','proofBytes','publicBytes','checkpointBytes','savedBytes','stage1','stage2','log']:
 assert forbidden not in body, forbidden
assert re.findall(r'^import (.*)$',s,re.M)==['Std']
for f in ['S2TrustedSdkBorrow.lean','S2TrustConsistency.lean']:
 t=(lean/f).read_text()
 assert not re.search(r'\b(sorry|admit|native_decide|axiom|decide)\b',t)
 assert not re.search(r'set_option\s+(maxRecDepth|maxHeartbeats)',t)
 theorems=re.findall(r'^(?:private )?theorem (\w+)',t,re.M)
 assert set(theorems)<=set(re.findall(r'^#print axioms (\w+)',t,re.M))
rust=(p/'kani-spec/src/lib.rs').read_text()
for field in expected: assert re.search(r'fn '+field+r'\(',rust),field
assert rust.startswith('#![cfg(kani)]')
root=p.parents[4]
changed=subprocess.check_output(['git','diff','--name-only','0998f05ffa0256157a35b270d4097a096fa17748'],cwd=root,text=True).splitlines()
changed+=subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=root,text=True).splitlines()
allowed='docs/research/100bit-spend-path-20261013/'
assert all(f.startswith(allowed+'evidence/s2-trust-20261023/') or f in [allowed+'lean/S2TrustedSdkBorrow.lean',allowed+'lean/S2TrustConsistency.lean'] for f in changed)
result={'exact_fields':fields,'field_count':len(fields),'caller_conclusion_terms_absent':True,'new_module_only':True,'axioms_audit_commands_cover_all_theorems':True,'kani_properties_cover_all_fields':True,'trust_discharged':False,'scope':'mathematical consistency + bounded Rust spec, not SDK certification','sha256':{f:hashlib.sha256((lean/f).read_bytes()).hexdigest() for f in ['S2TrustedSdkBorrow.lean','S2TrustConsistency.lean']}}
(p/'audit.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
