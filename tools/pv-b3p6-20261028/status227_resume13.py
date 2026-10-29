"""Conservative body credit and exact callback-hypothesis comparison."""
from pathlib import Path
import json,hashlib,re,subprocess
D=Path('evidence/pv-b3p6-20261028');O=D/'resume13';sha=lambda b:hashlib.sha256(b).hexdigest()
prev=json.loads((D/'resume12/identity-audit.json').read_text());cov=json.loads((D/'resume12/coverage.json').read_text())
raw=O/'missing-semantic';emitted=json.loads((raw/'translation.json').read_text())['functions'];out=json.loads((O/'extraction/semantic/aeneas-outputs.json').read_text())
for name in ['Funs.lean','Types.lean','translation.json']:
 r=next(x for x in out if x['path'].endswith('/'+name));assert sha((raw/name).read_bytes())==r['sha256']
new=[]
for f in emitted:
 if f['is_opaque']:continue
 simple=f['rust_name'].split('::')[-1]
 if simple not in ['private_public','withdrawal_public']:continue
 old=next(r for r in prev['bodies']if r['key']==simple+'#0');assert old['post_macro_identity']and not old['bound']
 row=next(r for r in cov['rows']if r['key']==simple+'#0'and r['family']=='terminal')
 # This fresh generation is the model's direct exact-owned-text chain.
 inputs=json.loads((O/'extraction/semantic/charon-inputs.json').read_text());owned=Path('tools/pv-b3p6-20261028/v244/reference_terminal.rs')
 assert sha(owned.read_bytes())==inputs['source_freeze'][str(owned)]
 inventory=json.loads((D/'resume9/body-inventory.json').read_text())['bodies'][row['inventory_index']]
 assert f['source']['begin_line']==inventory['owned']['line']
 row.update(bound=True,binding_class='reclassification within existing Charon/Aeneas tool trust (owner fifth amendment)',identity_audit='identity-audit.json',identity_failures=[],remaining=[],note='New exact-span raw model; compiled conversion laws in SemanticBinding13227. Full dependency/callback composition remains open.')
 new.append(dict(key=row['key'],inventory_index=row['inventory_index'],post_macro_authority='../resume12/identity-audit.json',post_macro_source_sha256=old['source']['expanded_body_sha256'],post_macro_owned_sha256=old['owned']['expanded_body_sha256'],token_sha256=old['source']['token_sha256'],owned_file_sha256=sha(owned.read_bytes()),model=f,raw_outputs=out,generation='extraction/semantic',bound=True,evidence_class=row['binding_class']))
assert len(new)==2
cov.update(bound=38,reclassification_bound=38,own_1_proved_fully_composed=0,unbound=41,lexical_identities_without_model_chain=5,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),new_bound=[r['key']for r in new],credit_policy='Only two new exact-span b3p6-1 chains earn credit. Model laws and parameterized predicates do not establish native source association.')
(O/'coverage.json').write_text(json.dumps(cov,indent=2)+'\n');(O/'identity-audit.json').write_text(json.dumps(dict(reused=prev['ruling'],previous='../resume12/identity-audit.json',new_bound=new,total_bound=38,all_43_post_macro_identities_reused_with_unchanged_inputs=True),indent=2)+'\n')
# Byte comparison of conclusion text, with the scope/arguments recorded explicitly.
path='docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_OracleBridge38.lean';ref='origin/codex/pv-runjoin-20261026';b=subprocess.check_output(['git','show',ref+':'+path]).decode();hyp=re.search(r'\(op227 : (∀ claims,[\s\S]*?)\) :',b)[1]
source=(D/'lean/PV_B3P_PartsBinding13227.lean').read_text();target=re.search(r'    (∀ claims,[\s\S]*?) := by',source)[1];assert hyp==target
(O/'runjoin-hypothesis.txt').write_text('(op227 : '+hyp+')\n')
status=dict(branch='codex/pv-runjoin-20261026',revision=subprocess.check_output(['git','rev-parse',ref],text=True).strip(),path=path,source_sha256=sha(b.encode()),hypothesis='(op227 : '+hyp+')',hypothesis_sha256=sha(('(op227 : '+hyp+')').encode()),conclusion_text_byte_identical=True,conclusion_sha256=sha(hyp.encode()),core_skeleton='PV_B3P_Binding13227.selected_callback13',core_skeleton_attempt=66613,core_skeleton_charged_ordinal=14,core_skeleton_hypotheses=['PV_B3P_Link_terminal_qm31 base ops (source_ports13 base composition equality)','PV_B3P_Link_terminal_composition_parts composition','PV_B3P_Link_terminal_equality_value equality'],terminal_specialization='transported_reference base',carrier='PV_B3P_Install227.Types base',discharged=False,replacement_theorem=None,full_requested_skeleton_complete=False,missing_from_full_skeleton=['exact seven-body link group with source associations; only private_public and withdrawal_public now extraction-bound','36 function links are typed predicates with source arguments uninstantiated; prepared_link13 instantiates only an explicit source model','standalone D188/matrix gate and slice/std coverage links connected to the native interpretation'],installed_fit='PV_B3P_InstalledFit13227.selected_callback',installed_fit_scope='newly selected reference ops only; not a native source theorem',compiler_boundary='V370 / pending owner D381,D386 retained',coverage=dict(candidates=79,bound=38,reclassification_bound=38,own_1_proved_fully_composed=0))
(O/'runjoin-status.json').write_text(json.dumps(status,indent=2)+'\n')
links=json.loads((O/'link-status.json').read_text())
for r in links:
 if r['function']=='qm31_sum_products3_prepared':r.update(model_instance='PV_B3P_Binding13227.source_prepared13',model_theorem='PV_B3P_Binding13227.prepared_link13',status='DISCHARGED for explicit interpreted source model; native/stdlib association remains open; no BOUND credit')
(O/'link-status.json').write_text(json.dumps(links,indent=2)+'\n')
print(json.dumps(dict(coverage=38,core_conclusion_byte_identical=True,full_requested_skeleton_complete=False,op227_discharged=False)))
