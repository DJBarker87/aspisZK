from pathlib import Path
import re,json,hashlib
D=Path('evidence/pv-route2-20261027'); O=D/'lean';O.mkdir(exist_ok=True);rows=[];seen={};ns='PV_R2_Emitted';prev=None
# Relocate fresh emitted type declarations into one job-private carrier.
types=(D/'generated/generated-254/Types.lean').read_text().replace('PV_R2_254',ns)
types=types.replace('end '+ns,'\n'.join('#print axioms '+name for name in ['aspis_core.field.M31','aspis_core.field.CM31','aspis_core.field.QM31','aspis_core.field.wide_exact.WideExact'])+'\nend '+ns)
p=O/'PV_R2_Types.lean';p.write_text(types);prev='PV_R2_Types';rows.append(dict(module=prev,kind='emitted types',file=str(p)))
for op in [223,230,258,254]:
 raw=(D/f'generated/generated-{op}/Funs.lean').read_text();header=raw[:raw.index('namespace ')];header=re.sub(r'import PVR\d+\.Types','IMPORT',header);blocks=raw[raw.index('namespace '):].split('/-- ')[1:]
 for block in blocks:
  block='/-- '+block;block=re.sub(r'\nend PV_R2_\d+\s*$','',block)
  m=re.search(r'\bdef (\S+)',block,re.M)
  if not m:raise ValueError(block)
  name=m[1];adapt=[]
  # The pinned backend accepts U32 shift counts. Generated i32 positive literals
  # encode the identical nonnegative bit count; no arithmetic body is rewritten.
  def fix(m):
   before=m[0];after=before.replace('#i32','#u32');adapt.append([before,after]);return after
  block=re.sub(r'Std\.(?:U8|U16|U32|U64|Usize)\.wrapping_sh[lr] [^\n]+? \d+#i32',fix,block)
  semantic=block[block.index('@[') if '@[' in block else block.index('def '):].strip()
  if name in seen:
   if seen[name]!=semantic:raise ValueError('divergent emitted declaration '+name)
   continue
  seen[name]=semantic
  mod=f'PV_R2_D{len(rows):02d}_{re.sub("[^a-zA-Z0-9_]","_",name)[-65:]}'
  text=header.replace('IMPORT','import '+prev)+'namespace '+ns+'\n'+block+'\n#print axioms '+name+'\nend '+ns+'\n';p=O/(mod+'.lean');p.write_text(text)
  rows.append(dict(module=mod,op=op,declaration=name,file=str(p),raw_block_sha256=hashlib.sha256(('/-- '+blocks[blocks.index(block[4:])] if False else block).encode()).hexdigest(),shift_adaptations=adapt));prev=mod
(D/'split.json').write_text(json.dumps(rows,indent=2)+'\n');print('modules',len(rows))
