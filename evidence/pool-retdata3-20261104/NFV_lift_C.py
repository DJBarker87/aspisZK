from pathlib import Path
import subprocess,json,sys,difflib,hashlib
E=Path(__file__).resolve().parent;packet=sys.argv[1];control=sys.argv[2]
assert packet in ['byte',*[f'value-{i}' for i in range(8)]];assert control in ['positive','negative','context-negative','infos-negative']
ids={'byte':(13,14),'value-0':(15,16),'value-1':(17,18),'value-2':(19,20),'value-3':(21,22),'value-4':(23,24),'value-5':(25,26),'value-6':(27,28),'value-7':(29,61)}
old=ids[packet][control=='negative'];p=E.parent/'pool-retdata2-20261104'/f'NFR_K{old:03}-shape.json';base=json.loads(p.read_text());s=base['source']
assert s.count('assert!(infos.is_empty());')==1
s=s.replace("infos:*const AccountInfo<'static>",'infos:*const ()').replace('assert!(infos.is_empty());','assert!(infos.len()==8&&core::ptr::eq(infos.as_ptr().cast::<()>(),self.infos));')
oldctx=' let instruction=Instruction{program_id:selected,accounts:Vec::new(),data:Vec::new()};'
assert s.count(oldctx)==1
ctx=''
for i in range(8):
 ctx+=f' let key{i}=Pubkey::new_from_array(kani::any());let owner{i}=Pubkey::new_from_array(kani::any());let mut lam{i}:u64=kani::any();let mut data{i}=[];\n'
 ctx+=f' let info{i}=AccountInfo::new(&key{i},kani::any(),kani::any(),&mut lam{i},&mut data{i},&owner{i},kani::any(),kani::any());\n'
ctx+=' let infos=['+','.join(f'info{i}' for i in range(8))+'];\n'
ctx+=' let metas:Box<[AccountMeta]>=Box::new(['+','.join(f'AccountMeta::new_readonly(key{i},false)' for i in range(7))+']);\n'
ctx+=' let request:[u8;320]=kani::any();let request:Box<[u8]>=Box::new(request);\n'
ctx+=' let instruction=Instruction{program_id:selected,accounts:metas.into_vec(),data:request.into_vec()};'
s=s.replace(oldctx,ctx).replace('infos:core::ptr::null()','infos:infos.as_ptr().cast::<()>()').replace('native(selected,&instruction,&[],','native(selected,&instruction,&infos,')
if control=='context-negative':
 s=s.replace(' let actual=native(selected,&instruction,&infos,',' let other=Instruction{program_id:selected,accounts:Vec::new(),data:Vec::new()};\n let actual=native(selected,&other,&infos,')
if control=='infos-negative':
 s=s.replace(' let actual=native(selected,&instruction,&infos,',' let other_infos=['+','.join(f'infos[{i}].clone()' for i in range(8))+'];\n let actual=native(selected,&instruction,&other_infos,')
patch=''
for path in ['programs/aspis-pool/src/pair_forest_dispatch.rs','programs/aspis-pool/src/lib.rs']:
 f=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+path],text=True)
 hook=f+'\n#[cfg(kani)]\n#[path="NFV_CJoin.rs"]\nmod NFV_CJoin;\n' if path.endswith('pair_forest_dispatch.rs') else '#![cfg_attr(kani, feature(allocator_api))]\n'+f+'\n#[cfg(kani)]\nextern crate alloc;\n#[cfg(kani)]\n#[path="../../../KMX_stubs.rs"]\npub mod NFO_KMX;\n'
 patch+=''.join(difflib.unified_diff(f.splitlines(True),hook.splitlines(True),fromfile='a/'+path,tofile='b/'+path))
path='programs/aspis-pool/src/NFV_CJoin.rs';patch+='--- /dev/null\n+++ b/'+path+'\n@@ -0,0 +1,'+str(len(s.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in s.splitlines())
(E/'NFV_native.patch').write_text(patch);(E/'NFV_CURRENT.json').write_text(json.dumps(dict(mode='C-context-'+packet+'-'+control,source=s,origin=str(p),origin_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),classification='strict context-domain lift of validated NFR SAME-object packet:7meta/320request/8info, same borrowed Instruction and info-array place; returned capacity=len792; input account-data prestate/role admission remains B',namespace='new NFV_CJoin lane module; not a rename used to repair a verdict; original internal/native/association function names retained'),indent=1)+'\n')
