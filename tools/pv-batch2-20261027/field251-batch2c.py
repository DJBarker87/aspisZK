from pathlib import Path
import sys,hashlib,json
L=Path('docs/research/v8-r0-zk-20261009/lean/R1Z');s=(L/'PV_B2_C_ConstructorEnvironment.lean').read_text();s=s[s.index('-- Component: PV_B2_Total_P.lean'):s.index('-- Component: PV_B2_W_20_host_weights_double.lean')]
for a,b in [('PV_B2_C_Carrier','PV_B2_251c1'),('PV_B2_C_WeightsNative','PV_B2_251c1'),('PV_B2_C_FieldValue','PV_B2_C_251FieldValue'),('PV_B2_C_FieldTotal','PV_B2_C_251FieldTotal')]:s=s.replace(a,b)
s='import R1Z.PV_B2_C_RawWeights251Funs\nset_option autoImplicit false\n'+s
p=L/'PV_B2_C_251FieldTotal.lean'
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
print('251 field proof adaptation',hashlib.sha256(s.encode()).hexdigest())
