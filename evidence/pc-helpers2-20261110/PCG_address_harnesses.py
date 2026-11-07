from pathlib import Path
import json
E=Path(__file__).resolve().parent;meta=json.loads((E/'PCG_ADDRESS_MAP.json').read_text());p=E/'PCG_Address.rs';s=p.read_text().split('// Generated exact-request helper harnesses.')[0]
s+='// Generated exact-request helper harnesses.\n'
for row,m in meta.items():
 args=m['args'].replace('program,','');params='let program:[u8;32]=kani::any();let pool:[u8;32]=kani::any();'
 callargs='&c.program,&Pubkey::new_from_array(pool)'
 if row in ['374','375']:params+='let profile:[u8;32]=kani::any();let release:[u8;32]=kani::any();';callargs+=',&profile,&release'
 if row=='323':params+='let sequence:u64=kani::any();';callargs+=',sequence'
 module=m['path'].rsplit('/',1)[1].removesuffix('.rs')
 s+='''#[kani::proof] #[kani::unwind(70)]
#[kani::stub(Pubkey::find_program_address,find_reply)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
'''+f'fn request_{row}(){{'+params+f'let request=reference::request_{row}(program,{args});'
 s+='let c=Context{program:Pubkey::new_from_array(program),request,outer:core::ptr::null(),reply:Pubkey::new_from_array(kani::any()),bump:kani::any(),is_ok:true,error:0,calls:Cell::new(0)};'
 s+=f'let got=crate::{module}::{m["function"]}({callargs});'
 s+='assert_eq!(c.calls.get(),1);assert!((got==(c.reply,c.bump))!=cfg!(PCG_NEG_ADDRESS));}\n'
p.write_text(s)
t=json.loads((E/'PCG_TASKS.json').read_text())
for j,row in enumerate(meta):
 for neg in [False,True]:
  a=f'PCG_K{34+2*j+int(neg):03}';x=json.loads(json.dumps(t['PCG_K031' if neg else 'PCG_K033']));old=x['command'][2][:-5];x=json.loads(json.dumps(x).replace(old,a));x['target']='POOL:'+row+' exact request '+('control' if neg else 'actual helper');cmd=x['native_command'];cmd[cmd.index('--harness')+1]='PCG_Address::request_'+row;t[a]=x
(E/'PCG_TASKS.json').write_text(json.dumps(t,indent=1)+'\n')
