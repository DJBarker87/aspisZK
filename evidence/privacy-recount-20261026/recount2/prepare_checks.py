from pathlib import Path
import re,json,subprocess,hashlib
P=Path(__file__).resolve().parent; R='docs/research/v8-r0-zk-20261009/lean/R1Z/'
checks=[]; items=[]
for p in sorted((P/'cb'/R).glob('*Source.lean.txt')):
 s=p.read_text();ns=re.findall(r'namespace (R1Z\.PV_CB_\w+)',s)
 for op in re.findall(r'theorem (op\d+_source)\b',s):
  if ns:items.append((p.name.removesuffix('.lean.txt'),ns[-1]+'.'+op))
for i in range(0,len(items),3): checks.append(('Callbacks'+str(i//3+1),items[i:i+3],[]))
assert len(checks)==8,len(checks)
checks += [
 ('Dictionary', [('PDict_RemainingDictionary231','R1Z.PDict_RemainingDictionary231.op'+str(op)+'_installed') for op in [78,231,247]],[]),
 ('Endpoint',[('PV_RunJoin_Endpoint','R1Z.PV_RunJoin_Endpoint.'+n) for n in ['uniform_V037','privacy_headline_from_premises']],['R1Z.PV_RunJoin_Endpoint.PV_RunJoin_Premises']),
 ('OsFailure',[(m,'R1Z.'+m+'.'+n) for m,n in [('PV_RunJoin_OsFailure','conditional_disagreement'),('PV_RunJoin_SourceFailureIndependence','source_witness_independent'),('PV_RunJoin_PublicFailureEndpoint','privacy_headline_public_failure'),('PV_RunJoin_OsFailureEndpoint','PV_RunJoin_OsFailure')]],['R1Z.PV_RunJoin_OsFailure.FirstDrawFailure']),
 ('SourceIdentification',[('PV_Src_Identification','R1Z.PV_Src_Identification.'+n) for n in ['public_eq','build_eq','transport_eq']],['R1Z.PV_Src_Identification.PV_Src_Premises']),
 ('Rw',[('PV_ProverRwP7CoefficientsInstall','R1Z.PV_ProverRwP7CoefficientsInstall.source'),('PV_TraceValueInstall','R1Z.PV_TraceValueInstall.source')],[]),
 ('Model',[('PrivacyR1HeadlineOwnedClosed','R1Z.PrivacyR1HeadlineOwnedClosed.Admitted.builder_premises'),('ProverCommitOwnedEndpoint','R1Z.ProverCommitOwnedEndpoint.caller_law'),('PrivacyR1HeadlineDeployedReal','R1Z.PrivacyR1HeadlineDeployedReal.privacy_headline_deployed')],[]),
 ('Trust',[('ProverCommitPublicNonce40','R1Z.ProverCommitPublicNonce40.E1'),('ProverCommitLedger36','R1Z.ProverCommitLedger36.E2')],['R1Z.ProverCommitPublicNonce40.E1','R1Z.ProverCommitLedger36.E2'])]
assert len(checks)==15
plan=[]
for label,items,prints in checks:
 name='PV_Ledger_Recount2_'+label
 s='\n'.join('import R1Z.'+m for m in dict.fromkeys(m for m,n in items))+'\nset_option pp.explicit true\n'
 for m,n in items:s+='#check @'+n+'\n#print axioms '+n+'\n'
 for n in prints:s+='#print '+n+'\n'
 file=P/'helpers'/(name+'.lean');file.parent.mkdir(exist_ok=True);file.write_text(s)
 plan.append(dict(module=name,source=str(file.relative_to(P)),sha256=hashlib.sha256(s.encode()).hexdigest(),items=items))
(P/'checks.json').write_text(json.dumps(plan,indent=2)+'\n')
print(len(plan),'print/check-only helpers; no declarations')
