"""Version proof drafts explicitly; never relabel the old emission as v3."""
from pathlib import Path
D=Path('evidence/pv-b3p6-20261028/lean')
pairs={
 'PV_B3P_PublicCarrier226':'PV_B3P_PublicCarrier226V3',
 'PV_B3P_Install226':'PV_B3P_Install226V3',
 'PV_B3P_ByteScalar226':'PV_B3P_ByteScalar226V3',
 'PV_B3P_ByteLayout226':'PV_B3P_ByteLayout226V3',
 'PV_B3P_ByteEndian226':'PV_B3P_ByteEndian226V3',
 'PV_B3P_WordLaw226':'PV_B3P_WordLaw226V3',
 'PV_B3P_Fidelity226':'PV_B3P_Fidelity226V3',
 'PV_B3P_BytesTypes226':'PV_B3P_BytesV3Types226',
 'PV_B3P_BytesRoot226':'PV_B3P_BytesV3Emission226',
 'PV_B3P_ByteAt226':'PV_B3P_BytesV3Emission226',
}
for old,new in list(pairs.items())[:7]:
 s=(D/(old+'.lean')).read_text()
 for a,b in sorted(pairs.items(),key=lambda kv:len(kv[0]),reverse=True):s=s.replace(a,b)
 s=s.replace('PV_B3P_226','PV_B3P_226V3')
 (D/(new+'.lean')).write_text(s)
print('Seven explicitly versioned proof/finite-validation drafts; compilation pending')
