from audit10 import *
manifest.update({x['ref']+':'+x['path']:x for x in json.loads((P/'manifest.json').read_text())})
# Read D566 at its later immutable LOG revision, keeping the original evidence pins.
pins['supplemental_LOG_revision']='5128519ff805330d2dcdde8ebaa2298615588b65'
s=txt(pins['supplemental_LOG_revision'],'docs/research/v8-r0-zk-20261009/LOG.md')
d566=s.split('## D566',1)[1].split('## D567',1)[0];(P/'D566.txt').write_text(('## D566'+d566).rstrip()+'\n')
# Direct source witnesses for the supplementary rows, preserving measurement identity.
items={
'V380-inversion':[('rw','docs/research/v8-r0-zk-20261009/lean/R1Z/PV_L2_Premises.lean')],
'V400':[('rw','lean/PV_MEAS_Deployed.lean')],
'V401':[('research','evidence/privacy-recount-20261026/recount2/rebase/docs/research/100bit-spend-path-20261013/evidence/pv-rebase-20261026/fixture-comparison.json')],
'V402':[('research','evidence/privacy-recount-20261026/recount2/rebase/docs/research/100bit-spend-path-20261013/evidence/pv-rebase-20261026/corpus-v3/pipeline-final.json')],
'V403':[('rw','docs/research/v8-r0-zk-20261009/lean/R1Z/PV_Canon_Prefix.lean'),('rw','docs/research/v8-r0-zk-20261009/lean/R1Z/PV_Canon_ReachedPolynomial.lean')],
'V404':[('research','design/PRIVACY-LEDGER-20261026.md')],
'V405':[('research','design/PRIVACY-LEDGER-20261026.md')],
'V406':[('rw','docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_TrustItems.lean')]}
result=[]
for id,ls in items.items():
 for k,p in ls:
  assert read(k,p) is not None,(id,p)
 result.append({'id':id,'sources':[manifest[k+':'+p] for k,p in ls],'prior_derivation':'../recount9/rows9.json#'+id,'scope':'Historical scoped statement/measurement retained; no new closure'})
(P/'supplemental10.json').write_text(json.dumps(result,indent=1)+'\n')
# Save the instructed external method/rulings as auditable text inputs in this worktree.
root=Path('/private/tmp/claude-501/-Users-dominic-ZK/4dec4925-8c43-447e-9333-6147c1c7863b/scratchpad')
for name in ['prompt-pv-recount9.txt','pv-common.txt','r1p-common.txt','local-lean.txt']:
 (P/('instructions-'+name)).write_bytes((root/name).read_bytes())
(P/'instructions-note.txt').write_text('Referenced prompt-pv-recount8.txt is absent from the supplied scratchpad. The committed recount8/METHOD8.md and recount9/METHOD9.md were read and applied. No missing instruction text was invented. Root AGENTS.md security/proof discipline was read in full. Latest supplied pv-common contains ax1-prime and k3. No later ruling changes the frozen audit pins.\n')
(P/'pins.json').write_text(json.dumps(pins,indent=2)+'\n');save();print('Supplementary8 rows and LOG D566 captured')
