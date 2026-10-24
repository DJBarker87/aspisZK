from pathlib import Path
import re,sys
R=Path(__file__).resolve().parents[2];L=R/'docs/research/100bit-spend-path-20261013/lean'
ps=sorted(p for p in L.glob('Port9OR_*.lean') if p.stem!='Port9OR_Audit')
out='\n'.join('import '+p.stem for p in ps)+'\n\nset_option autoImplicit false\n'
keys=['CheckpointBytes5Inputs.Oracle','AspisR1.Port9OR_Code.native','AspisR1.Port9OR_Code.program','AspisR1.Port9OR_Bodies.native','AspisR1.Port9OR_Installed.implementation']
out+='\n'.join('#print '+x for x in keys)+'\n'
checks=['Port9OR_Code.correspondence','Port9OR_Bodies.reader_value','Port9OR_Bodies.reader_effects','Port9OR_Law.reader_lazy','Port9OR_Checksum.checksum_branches','Port9OR_Bridge.reader_inverse','Port9OR_Budget.reader_count','Port9OR_P6Verify.source','Port9OR_Batch.source','Port9OR_Installed.effects','Port9OR_FirstBatch.first_batch','Port9OR_BatchLaw.batch_lazy','Port9OR_Rejection.no_sampler']
out+='\n'.join('#check @AspisR1.'+x for x in checks)+'\n\n'
for p in ps:
 namespace=re.search(r'^namespace (\S+)',p.read_text(),re.M).group(1)
 for name in re.findall(r'^theorem\s+(\w+)',p.read_text(),re.M):out+='#print axioms '+namespace+'.'+name+'\n'
p=L/'Port9OR_Audit.lean'
if '--check' in sys.argv:assert p.read_text()==out
else:p.write_text(out)
print({'modules':len(ps),'axioms_reports':out.count('#print axioms')})
