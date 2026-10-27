"""Generate small selector commutation statements; never launches jobs."""
from pathlib import Path
import re,sys
start=int(sys.argv[1]) if len(sys.argv)>1 else 1
root=Path(__file__).resolve().parents[2];p=root/'docs/research/v8-r0-zk-20261009/lean/R1Z'
mods=['ProverRwOuterTag','ProverRwOuterGuardLeaves','ProverRwOuterMapErr','ProverRwDictionaryDigest','ProverRwDictionaryBaseField','ProverRwDictionaryTower','ProverRwDictionaryScalar','ProverRwDictionaryLayout','ProverRwDictionaryDerived','ProverRwDictionaryMerkle','ProverRwDictionaryWideQM','ProverRwDictionaryDomain','PDict_WireError','PDict_Typenum','PDict_Numeric','PDict_Compare','PDict_Primitives','PDict_Ordering','PDict_Installed','PDict_UIntOps','PDict_MoreCarriers','PDict_ErrorCarrier','PDict_IOCarriers','PDict_Options','PDict_FinalDictionary','PDict_Publication','PDict_DigestDelegates','PDict_Array32','PDict_SaltClear','PDict_Fence','PDict_ResumeDictionary','PDict_OffpathBorrow','PDict_CtUpdate','PDict_CtConstructor','PDict_VolatileCell','PDict_FileFlush','PDict_FileCarrier','PDict_RejectionStd','PDict_PureDictionary','PDict_CodecDictionary']
for i,mod in enumerate(mods[1:],1):
 if i<start:continue
 prev='PDict_RemainingExt231' if i==1 else f'PDict_RemainingCommute231_{i-1:02}'
 extra=''
 if i>=6:
  src=(p/(mod+'.lean')).read_text()
  for names in re.findall(r'(?m)^open ([^\n]+)',src):
   if ' in' in names:continue
   if names.strip() not in ['Aeneas Aeneas.Std Result ProverRwFull','Aeneas Aeneas.Std Result','Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull']:
    extra+='open '+names+'\n'
 s=f'''import R1Z.{prev}
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_RemainingCommute231
open Aeneas Aeneas.Std Result ProverRwFull
open PDict_RemainingExt231 (replace stage0)
{extra}open {mod} in
'''
 if i<19:
  typ='types';cur=f'@{mod}.selected types';prefix=f'@{mods[i-1]}.selected types';previous=f'@stage{i-1} types'
  s+=f'''\ntheorem stage{i} [types : ExternalTypes] (ops other : ExternalFuns) :
    {cur} (@replace types ops other) =
    @replace types ({cur} ops) other := by
'''
 else:
  typ=('PDict_CarrierInstall.native base' if i==19 else 'PDict_IOCarriers.native base' if i==23 else f'{mod}.native base');cur=f'{mod}.selected base'
  arg='base'
  if i in [20,21,22]:arg=f'({mod}.native base)'
  if i==36:arg='({ base with op0 := PDict_FileCarrier.File })'
  if i==19:prefix=f'@{mods[i-1]}.selected ({typ})';previous=f'@stage{i-1} ({typ})'
  else:prefix=f'{mods[i-1]}.selected {arg}';previous=f'stage{i-1} {arg}'
  s+=f'''\ntheorem stage{i} (base : ExternalTypes)
    (ops other : @ExternalFuns ({typ})) :
    {cur} (@replace ({typ}) ops other) =
    @replace ({typ}) ({cur} ops) other := by
'''
 if i in [18,20,21,22,24,30,36]:s+=f'  exact {previous} ops other\n'
 else:
  raw=(p/(mod+'.lean')).read_text();a=raw.index('def selected');b=raw.find('\ntheorem',a);body=raw[a:b if b>=0 else None];a=body.index('{');depth=0
  for j in range(a,len(body)):
   depth+=(body[j]=='{')-(body[j]=='}')
   if depth==0:break
  rec=body[a:j+1];fields=rec.split(' with',1)[1]
  upd='{ d with'+fields
  s+=f'''  letI : ExternalTypes := {typ}
  let upd (d : @ExternalFuns ({typ})) : @ExternalFuns ({typ}) :=
    {upd}
  have hu (d : @ExternalFuns ({typ})) :
      upd (@replace ({typ}) d other) = @replace ({typ}) (upd d) other := by rfl
'''
  if i in [1,2,3,4,5]:
   s+=f'''  change {prefix} (upd (@replace ({typ}) ops other)) =
    @replace ({typ}) ({prefix} (upd ops)) other
  exact (congrArg ({prefix}) (hu ops)).trans ({previous} (upd ops) other)
'''
  else:
   s+=f'''  change upd ({prefix} (@replace ({typ}) ops other)) =
    @replace ({typ}) (upd ({prefix} ops)) other
  exact (congrArg upd ({previous} ops other)).trans (hu ({prefix} ops))
'''
 s+=f'\n#print axioms stage{i}\nend R1Z.PDict_RemainingCommute231\n'
 p.joinpath(f'PDict_RemainingCommute231_{i:02}.lean').write_text(s)
