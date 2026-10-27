"""Copy only the unchanged arithmetic declarations required by RawNat.
This removes unrelated semantic parser imports; it does not alter any proof.
"""
from pathlib import Path
import re,json,hashlib
E=Path(__file__).resolve().parent
replacements={'JFr_TX2_DotLaneTotal':'LPn_Extend','JFs_TX2_FoldLane':'LPn_FoldLane','JFv_TX2_FoldValue':'LPn_FoldValue','JFs_TX2_RawMath':'LPn_RawMath','JFs_TX2_RawMap':'LPn_RawMap','FJf_RawReference':'LPn_RawReference','FJf_RawArithmetic':'LPn_RawArithmetic'}
parts=[];pins=[]
def add(path,select=None,namespace=None):
 raw=Path(path).read_text();s=select(raw) if select else re.sub(r'^import .*\n','',raw,flags=re.M)
 if namespace:s=f'namespace AspisR1.{namespace}\nopen Aeneas Aeneas.Std Result\n'+('open LPn_RawReference\n' if namespace=='LPn_RawArithmetic' else '')+s+f'\nend AspisR1.{namespace}\n'
 for a,b in replacements.items():s=s.replace(a,b)
 names=re.findall(r'^theorem (\w+)',s,re.M)
 # Existing full-module axiom prints retained; extracted declarations get prints.
 if namespace:s=s.replace(f'end AspisR1.{namespace}', '\n'.join('#print axioms '+n for n in names)+'\nend AspisR1.'+namespace)
 parts.append(s);pins.append({'path':path,'source_sha256':hashlib.sha256(raw.encode()).hexdigest(),'selected_transformed_sha256':hashlib.sha256(s.encode()).hexdigest(),'theorems':names})
add('lean/JFr_TX2_DotLaneTotal.lean',lambda s:s[s.index('theorem extend '):s.index('/-- One real native lane')], 'LPn_Extend')
add('lean/JFs_TX2_FoldLane.lean',lambda s:s[s.index('def R '):s.index('def lane ')]+s[s.index('theorem shift '):s.index('theorem source ')], 'LPn_FoldLane')
add('lean/JFv_TX2_FoldValue.lean')
add('lean/JFs_TX2_RawMath.lean')
add('lean/JFs_TX2_RawMap.lean')
add('lean/FJf_RawReference.lean')
add('lean/FJf_RawArithmetic.lean',lambda s:s[s.index('theorem product_value '):s.index('theorem product_bound ')], 'LPn_RawArithmetic')
(E/'LPn_RawSupport.lean').write_text('import FIo_NativeFuns\nimport FIo_ReduceBounds\nimport FIo_ScalarBridge\nset_option autoImplicit false\n'+ '\n'.join(parts))
(E/'LPn_RAW_SUPPORT.json').write_text(json.dumps({'method':'literal selected declarations; references/imports only renamed; no proof edit','declarations':pins},indent=2)+'\n')
p=E/'LPn_RawNat.lean';s=p.read_text().replace('import FJf_RawArithmetic','import LPn_RawSupport')
for a,b in replacements.items():s=s.replace(a,b)
p.write_text(s)
p=E/'LPn_DotJoin.lean';s=p.read_text().replace('AspisR1.FJf_RawReference','AspisR1.LPn_RawMap');p.write_text(s)
