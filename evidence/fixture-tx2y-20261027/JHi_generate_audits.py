from pathlib import Path
R=Path(__file__).resolve().parents[2]
groups={
'Guards':['JHi_Guards','JHi_CheckpointGuard','JHi_AccountReads'],
'DistinctA':['JHi_DistinctAccounts','JHi_Distinct0','JHi_Distinct1','JHi_Distinct2','JHi_Distinct3'],
'DistinctB':['JHi_Distinct4','JHi_Distinct5','JHi_Distinct6','JHi_Distinct'],
'Digest':['JHi_DigestAssociation','JHi_ProfileDigestAssociation','JHi_RawForestDigest','JHi_RawLane'],
'Payment':['JHi_PaymentValidation','JHi_CommonEncoder','JHi_PaymentBody','JHi_PaymentRawAction','JHi_PaymentDecoderAction','JHi_PaymentAccepted','JHi_RetypeSuccess'],
'Snapshot':['JHi_RawFrontierCheck','JHi_RawSnapshotValidator','JHi_SnapshotLoopAssociation','JHi_SnapshotBody','JHi_SnapshotConstants','JHi_SnapshotDecoderAction','JHi_SnapshotAccepted','JHi_RetypePairSuccess'],
'Afterstate':['JHi_RawAfterstateFrontier','JHi_RawAfterstateValidator','JHi_AfterstateLoopAssociation','JHi_AfterstateBody','JHi_AfterstateConstants','JHi_AfterstateDecoderAction','JHi_AfterstateAccepted'],
'Late':['JHi_LateChildSpecs','JHi_LateAccepted'],
'Authentication':['JHi_Authentication','JHi_AuthenticationPrefix','JHi_AuthenticationRefusal'],
'Validation':['JHi_RawValuesValidated','JHi_RawComparisons','JHi_RawTerminalValidation','JHi_Reconstruction','JHi_Validation'],
'Emission':['JHi_Configuration','JHi_EmissionAssociation'],
'Wrapper':['JHi_TX2'],
'Pair':['JHi_JointPair']}
import re
for label,mods in groups.items():
 s='\n'.join('import '+m for m in mods)+'\nset_option autoImplicit false\nset_option pp.proofs false\n'
 for m in mods:
  raw=(R/'lean'/f'{m}.lean').read_text()
  for name in re.findall(r'^(?:@\[[^\n]*\] )?theorem (\w+)',raw,re.M):s+=f'#print axioms AspisR1.{m}.{name}\n'
 if label in ['Authentication','Validation','Wrapper','Pair']:
  m=mods[-1];name='after_validation' if label=='Wrapper' else 'source'
  s+=f'#print AspisR1.{m}.{name}\n'
 (R/'lean'/f'JHi_Audit{label}.lean').write_text(s)
