from pathlib import Path
import subprocess,re,hashlib,json
P=Path('docs/research/v8-r0-zk-20261009/lean/R1Z');E=Path('evidence/pv-extract-20261027');base='/home/dombarker/project-offloads/codex-pv-extract-20261027/index-compress-generated/'
raw={k:subprocess.check_output(['ssh','dombarker@100.108.41.90','cat '+base+k+'.lean'],text=True) for k in ['Types','Funs','FunsExternal_Template']}
(P/'PV_Ext_IndexCompressTypes.lean').write_text(raw['Types'])
template=raw['FunsExternal_Template'];names=re.findall(r'\baxiom\s+([\w.]+)',template);assert names==['aspis_core.field.CM31.from_m31','aspis_core.field.QM31.from_cm31','aspis_core.field.QM31.add','aspis_core.field.QM31.mul','aspis_core.field.QM31.mul_m31']
# Kernel check the extracted control on the existing structurally identical carrier.
s=raw['Funs'];s=s.replace('import PVExtIndexCompress.Types','import R1Z.ProverRwP6CompressSource').replace('import PVExtIndexCompress.FunsExternal','')
s=s.replace('namespace PV_Ext_IndexCompress','namespace R1Z.PV_Ext_IndexCompress\nopen ProverRwFull\nvariable [ExternalTypes] [ExternalFuns]')
s=s.replace('end PV_Ext_IndexCompress','end R1Z.PV_Ext_IndexCompress')
s=s.replace('core.num.Usize.wrapping_add','Std.Usize.wrapping_add')
(P/'PV_Ext_IndexCompressFuns.lean').write_text(s)
(E/'index-normalization.json').write_text(json.dumps(dict(raw_hashes={k:hashlib.sha256(v.encode()).hexdigest() for k,v in raw.items()},external_names=names,adaptations=['Types separately typechecked unchanged','Function carrier relocated to structurally identical ProverRwFull M31/CM31/QM31','Existing ExternalFuns universally quantified, no template installed','core.num.Usize.wrapping_add normalized to pinned backend Std.Usize.wrapping_add','namespace/import relocation only otherwise; generated body unchanged'],status='candidate index-loop extraction only; no shipped-iterator source association'),indent=2)+'\n')
