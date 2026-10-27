from pathlib import Path
import re,json
P=Path(__file__).resolve().parent;R=P.parents[1]
groups=[
 ('Authentication',['JHj_Authentication']),
 ('Master',['JHj_MasterPrefix','JHj_DecodedMaster','JHj_MasterPdaStep','JHj_MasterRegistryStep']),
 ('Checkpoint',['JHj_CheckpointReadStep','JHj_CheckpointPrefix','JHj_CheckpointPdaStep']),
 ('Lane',['JHj_LaneReadStep','JHj_LanePrefix','JHj_LanePdaStep']),
 ('Registry',['JHj_RegistryPrefix','JHj_RegistryReadonly','JHj_RegistryReadStep','JHj_RegistryPolicyStep']),
 ('Entry',['JHj_EntryReadStep']),
 ('RegistryTails',['JHj_RegistryPolicy','JHj_RegistryRead','JHj_RegistryDecoded','JHj_RegistryPda','JHj_RegistryProgramdata','JHj_RegistryChecks','JHj_RegistryStatus']),
 ('EntryTails',['JHj_EntryRead','JHj_EntryDecoded','JHj_EntryPda','JHj_EntryProgramdata','JHj_EntryChecks']),
 ('MasterErrors',['JHj_MasterPdaError','JHj_MasterPdaFailure','JHj_MasterPdaDivergence']),
 ('CheckpointErrors',['JHj_CheckpointPdaError','JHj_CheckpointPdaFailure','JHj_CheckpointPdaDivergence']),
 ('LaneErrors',['JHj_LanePdaError','JHj_LanePdaFailure','JHj_LanePdaDivergence']),
 ('Fields',['JHj_RegistryValue','JHj_RegistryFields','JHj_EntryFields','JHj_RegistrySeeds','JHj_GuardNonVacuity']),
 ('Pair',['JHj_JointPair','JHj_TX2']),
]
for short in ['Reconstruction','AuthenticationPrefix','SHAProof','SHAPublic','SHAChecksum','Validation','TX2','JointPair','AuthenticationRefusal','EmissionAssociation','PaymentBody']:
 groups.append(('Inherited'+short,['JHi_'+short]))
manifest=[]
for label,mods in groups:
 name='JHj_Audit'+label
 s=''.join('import '+m+'\n' for m in mods)+'set_option autoImplicit false\nset_option pp.proofs false\n'
 for mod in mods:
  text=(R/'lean'/(mod+'.lean')).read_text()
  ns=re.search(r'^namespace (\S+)',text,re.M)[1]
  for decl in re.findall(r'^#print axioms (\S+)',text,re.M):
   fq=decl if decl.startswith('AspisR1.') else ns+'.'+decl
   s+='#print '+fq+'\n#print axioms '+fq+'\n'
 (R/'lean'/(name+'.lean')).write_text(s)
 manifest.append(dict(module=name,imports=mods))
(P/'JHj_AUDIT_PLAN.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(len(groups),'small-group audits generated; headline remains separate')
