from pathlib import Path
import subprocess,json,hashlib,re
E=Path(__file__).resolve().parent
modules=['LPi_SerializationFold','LPm_WeightLoop','LPm_CheckpointBody','LPm_CheckpointProgram','KND_Schedule','KNE_Model','KNE_Schedule','KNE_Composition','KNE_Writer','KNE_Leaf','KNE_Final']
pins=[]
for m in modules:
 path=('evidence/kani-reverify4-20261028/'if m.startswith('KND_')else'evidence/kani-reverify5-20261028/'if m.startswith('KNE_')else'lean/')+m+'.lean'
 raw=subprocess.check_output(['git','show','HEAD:'+path],text=True);s=raw
 for n in sorted(modules+['KNE_Caller'],key=len,reverse=True):s=re.sub(r'(?<![A-Za-z0-9_])'+re.escape(n)+r'(?![A-Za-z0-9_])','NGC_'+n,s)
 if m=='KND_Schedule':s=s.replace('import KMY_CheckpointComposition','import NGC_Initialization')
 (E/('NGC_'+m+'.lean')).write_text(s)
 pins.append(dict(source_path=path,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_sha256=hashlib.sha256(raw.encode()).hexdigest(),target='NGC_'+m+'.lean',target_sha256=hashlib.sha256(s.encode()).hexdigest(),changes='module/name-only retarget; KND unused KMY import replaced with coherent initialization import',proof_text_changes=False))
(E/'NGC_CHECKPOINT_RETARGET.json').write_text(json.dumps(pins,indent=1)+'\n')
