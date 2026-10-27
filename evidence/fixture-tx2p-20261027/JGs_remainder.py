from pathlib import Path
import sys
R=Path(__file__).resolve().parents[2]
s='''import JGs_Regular
import JGq_SharedHigh
import JGq_Low
import JGs_Inactive
import JGs_LibraSource
'''
for i in range(3):
 q=R/f'lean/JGs_PairShared{i}.lean'
 t=(q if q.exists() else R/'evidence/fixture-tx2p-20261027/JGs_UNCHECKED'/(q.name+'.txt')).read_text()
 s+='\n'+'\n'.join(line for line in t.splitlines() if not line.startswith('import '))+'\n'
p=R/'lean/JGs_PairForwardRemainder.lean'
if '--check' in sys.argv:assert (p if p.exists() else R/'evidence/fixture-tx2p-20261027/JGs_UNCHECKED'/(p.name+'.txt')).read_text()==s
else:p.write_text(s)
print('Three small ordered continuation cuts in one focused source module')
