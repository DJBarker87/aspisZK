import re,sys
sys.path.insert(0,'.')
import ext
s=open('../prov-p2f-20261109/PRVEq_Port23PUSH_Source.lean').read()
s=s.replace("def verifier.update_residue_row\n  (row : Array Std.U64 4#usize) (power : aspis_core.field.QM31)","def verifier.update_residue_row\n  (ai : Port23PUSH.ArrayIntoIter)\n  (row : Array Std.U64 4#usize) (power : aspis_core.field.QM31)",1)
s=s.replace("MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter\n        row1","ai row1",1)
s=s.replace("def verifier.BatchedWeights.push\n  (self : verifier.BatchedWeights)","def verifier.BatchedWeights.push\n  (ai : Port23PUSH.ArrayIntoIter)\n  (self : verifier.BatchedWeights)",1)
s=s.replace("verifier.update_residue_row a power basis","verifier.update_residue_row ai a power basis",1)
assert 'ai row1' in s and 'update_residue_row ai a' in s
open('/tmp/p23_in.lean','w').write(s)
ext.build('/tmp/p23_in.lean','PRVEq_Port23PUSH_Source_P3d.lean',
  undrop=['verifier.update_residue_row','verifier.BatchedWeights.push'],
  steps=[('nonloop','verifier.update_residue_row'),('nonloop','verifier.BatchedWeights.push')])
