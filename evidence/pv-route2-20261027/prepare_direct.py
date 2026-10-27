from pathlib import Path
import re,json
D=Path('evidence/pv-route2-20261027');O=D/'lean-direct';O.mkdir(exist_ok=True);rows=[]
for phase in ['Types','Funs']:
 for op in [223,230,254,258]:
  p=D/f'generated/generated-{op}/{phase}.lean';s=p.read_text();mod=f'PV_R2_Direct{op}_{phase}'
  s=re.sub(r'import PVR\d+\.Types',f'import PV_R2_Direct{op}_Types',s)
  names=re.findall(r'\b(?:def|structure) ([\w.]+)',s)
  s=s.replace('end PV_R2_'+str(op),'\n'.join('#print axioms '+n for n in names)+'\nend PV_R2_'+str(op))
  (O/(mod+'.lean')).write_text(s);rows.append(dict(module=mod,op=op,kind='direct emitted '+phase,file=str(O/(mod+'.lean'))))
# Independent full-file backend compatibility check for the previously isolated
# dynamic usize shift. This retains emitted namespace and all original bodies.
op=258;mod='PV_R2_Direct258_Funs_U32';s=(O/'PV_R2_Direct258_Funs.lean').read_text();s=s.replace('Std.Usize.wrapping_shr row 4#i32','Std.Usize.wrapping_shr row 4#u32');s=s.replace('  let i4 ← lift (Std.U16.wrapping_shl 1#u16 i3)','  let shift ← lift (UScalar.cast .U32 i3)\n    let i4 ← lift (Std.U16.wrapping_shl 1#u16 shift)')
# The insertion must preserve the existing two-space do-block indentation.
s=s.replace('    let shift ←','    let shift ←')
(O/(mod+'.lean')).write_text(s);rows.append(dict(module=mod,op=op,kind='direct emitted Funs with documented shift adapters',file=str(O/(mod+'.lean'))))
(D/'direct.json').write_text(json.dumps(rows,indent=2)+'\n')
