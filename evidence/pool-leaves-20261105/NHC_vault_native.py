"""Bounded custody parser branches; no whole-buffer zero scan or hash body."""
from pathlib import Path
import sys,subprocess,difflib,json
E=Path(__file__).resolve().parent;family,mode=sys.argv[1:3];assert mode in ['positive','negative']
if family in ['token_flags','token_delegated_amount'] and (E/'NHC_RESERVE_DYNAMIC').exists():raise SystemExit('Reserved final four native slots for unbounded-span geometry attempts')
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';read=lambda p:subprocess.check_output(['git','show',rev+':'+p],text=True)
code='';domain='';err_token='ProgramError::Custom(0x4153_2015)';err_config='ProgramError::Custom(0x4153_201A)'
if family.startswith('array'):
 n=int(family[5:]);code=f'let raw:[u8;{n}]=kani::any();let len:usize=kani::any();kani::assume(len<={n});let r=token_array::<{n}>(&raw[..len]);\n'
 code+='let mut observed=r;'+('if let Ok(ref mut a)=observed{a[0]^=1;}' if mode=='negative' else '')+f'if len!={n}{{assert!(observed==Err({err_token}));}}else{{let j:usize=kani::any();kani::assume(j<{n});assert!(observed.unwrap()[j]==raw[j]);}}\n'
 domain=f'array conversion with length 0..{n}; exact-length value and short rejection branches'
elif family.startswith('copt'):
 key='key' in family;n=36 if key else 12;fn='parse_coption_pubkey' if key else 'parse_coption_u64';branch=family.split('_')[1]
 code=f'let mut raw:[u8;{n}]=kani::any();\n'
 if branch=='some':
  code+='raw[..4].copy_from_slice(&1u32.to_le_bytes());let r='+fn+'(&raw).unwrap().unwrap();'
  if key:code+='let j:usize=kani::any();kani::assume(j<32);let mut observed=r.to_bytes()[j];'+('observed^=1;' if mode=='negative' else '')+'assert!(observed==raw[4+j]);'
  else:code+='let mut observed=r;'+('observed^=1;' if mode=='negative' else '')+'assert!(observed==u64::from_le_bytes(raw[4..12].try_into().unwrap()));'
  domain=f'exact {n}-byte COption Some tag 1; every payload byte arbitrary; no zero loop reached'
 else:
  if branch=='bad':code+='let tag:u32=kani::any();kani::assume(tag>1);raw[..4].copy_from_slice(&tag.to_le_bytes());let r='+fn+'(&raw);'
  else:code+=f'let len:usize=kani::any();kani::assume(len<{n});let r='+fn+'(&raw[..len]);'
  code+='let mut observed=r;'+('observed=Ok(None);' if mode=='negative' else '')+f'assert!(matches!(observed,Err(e) if e=={err_token}));'
  domain=f'COption {branch} rejection branch only, exact or short {n}-byte window; no zero loop reached'
elif family.startswith('mint'):
 code='let mut raw:[u8;82]=kani::any();'
 if family=='mint_wronglen':code+='let len:usize=kani::any();kani::assume(len<82);let r=parse_legacy_mint_v1(&raw[..len]);let mut observed=r;'+('observed=Ok(LegacyMintV1{supply:0,decimals:0});' if mode=='negative' else '')+f'assert!(matches!(observed,Err(e) if e=={err_config}));'
 else:
  code+='raw[..4].copy_from_slice(&1u32.to_le_bytes());raw[46..50].copy_from_slice(&1u32.to_le_bytes());'
  if family=='mint_uninit':code+='let state:u8=kani::any();kani::assume(state!=1);raw[45]=state;let r=parse_legacy_mint_v1(&raw);let mut observed=r;'+('observed=Ok(LegacyMintV1{supply:0,decimals:0});' if mode=='negative' else '')+'assert!(matches!(observed,Err(e) if e==ProgramError::Custom(0x4153_2014)));'
  else:
   code+='raw[45]=1;let r=parse_legacy_mint_v1(&raw).unwrap();'
   field='supply' if family=='mint_supply' else 'decimals';expected='u64::from_le_bytes(raw[36..44].try_into().unwrap())' if field=='supply' else 'raw[44]'
   code+='let mut observed=r.'+field+';'+('observed^=1;' if mode=='negative' else '')+'assert!(observed=='+expected+');'
 domain='mint parser exact 82-byte Some/Some COption class, or wrong-length rejection; None classes not covered; no zero loop'
else:
 code='let mut raw:[u8;165]=kani::any();'
 if family=='token_wronglen':code+='let len:usize=kani::any();kani::assume(len<165);let r=parse_legacy_token_account_v1(&raw[..len]);let mut failed=matches!(r,Err(e) if e=='+err_config+');'+('failed=!failed;' if mode=='negative' else '')+'assert!(failed);'
 else:
  code+='raw[72..76].copy_from_slice(&1u32.to_le_bytes());'
  if family=='token_badstate':code+='let state:u8=kani::any();kani::assume(state!=1);raw[108]=state;let r=parse_legacy_token_account_v1(&raw);let mut failed=matches!(r,Err(e) if e=='+err_token+');'+('failed=!failed;' if mode=='negative' else '')+'assert!(failed);'
  else:
   code+='raw[108]=1;raw[109..113].copy_from_slice(&1u32.to_le_bytes());raw[129..133].copy_from_slice(&1u32.to_le_bytes());let r=parse_legacy_token_account_v1(&raw).unwrap();'
   field=family[6:]
   if field in ['mint','authority']:
    off=0 if field=='mint' else 32;code+='let j:usize=kani::any();kani::assume(j<32);let mut observed=r.'+field+'.to_bytes()[j];'+('observed^=1;' if mode=='negative' else '')+f'assert!(observed==raw[{off}+j]);'
   elif field=='flags':code+='let mut observed=r.has_delegate&&r.is_native&&r.has_close_authority;'+('observed=!observed;' if mode=='negative' else '')+'assert!(observed);'
   else:
    off=64 if field=='amount' else 121;code+='let mut observed=r.'+field+';'+('observed^=1;' if mode=='negative' else '')+f'assert!(observed==u64::from_le_bytes(raw[{off}..{off+8}].try_into().unwrap()));'
 domain='token parser exact 165-byte Some/Some/Some class, or bad-state/wrong-length rejection; None classes not covered; no zero loop'
s='''use super::*;
#[kani::proof]
#[kani::unwind(166)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFO_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NFO_KMX::KMX_copy_from_slice)]
#[kani::stub(alloc::alloc::realloc,crate::NFO_KMX::KMX_realloc)]
fn association(){
'''+code+'\n}\n';patch=''
for p in ['programs/aspis-pool/src/vault.rs','programs/aspis-pool/src/lib.rs']:
 f=read(p);after=f+'\n#[cfg(kani)]\n#[path="NHC_Vault.rs"]\nmod NHC_Vault;\n' if p.endswith('vault.rs') else '#![cfg_attr(kani, feature(allocator_api))]\n'+f+'\n#[cfg(kani)]\nextern crate alloc;\n#[cfg(kani)]\n#[path="../../../KMX_stubs.rs"]\npub mod NFO_KMX;\n'
 patch+=''.join(difflib.unified_diff(f.splitlines(True),after.splitlines(True),fromfile='a/'+p,tofile='b/'+p))
p='programs/aspis-pool/src/NHC_Vault.rs';patch+='--- /dev/null\n+++ b/'+p+'\n@@ -0,0 +1,'+str(len(s.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in s.splitlines())
(E/'NHC_native.patch').write_text(patch);(E/'NHC_CURRENT.json').write_text(json.dumps(dict(kind='actual custody parser '+family,mode=mode,source=s,domain=domain,modifies=[],production_credit=False,remaining='complete None/zero-loop/model/physical caller domain and mutation frame'),indent=1)+'\n')
print('vault::NHC_Vault::association')
