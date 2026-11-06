from pathlib import Path
import subprocess,json,hashlib,base64,difflib
E=Path(__file__).resolve().parent;R='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
S=(E/'NKM_native_generated.rs.txt').read_text()
for name,attrs in [
 ('secure_circle_point_from_parameter','#[kani::requires(canonical(parameter)&&l.len==0&&canonical_replies(l))]\n#[kani::modifies(&mut l.events,&mut l.len)]\n#[kani::ensures(|r|(*r==circle_ref(l))!=cfg!(NKM_contract_invert))]\n'),
 ('secure_ood_circle_point_from_parameter','#[kani::requires(l.count==0)]\n#[kani::modifies(&mut l.parameter,&mut l.count)]\n#[kani::ensures(|r|(*r==ood_ref(parameter,l))!=cfg!(NKM_contract_invert))]\n'),
 ('circle_fallback_point','#[kani::requires(l.count==0)]\n#[kani::modifies(&mut l.parameter,&mut l.count)]\n#[kani::ensures(|r|(*r==fallback_ref(l))!=cfg!(NKM_contract_invert))]\n')]:S=S.replace('pub fn '+name+'(',attrs+'pub fn '+name+'(',1)
S+='\n'+(E/'NKM_contracts.rs.txt').read_text()
inputs={};oldpins=json.loads((E/'NKM_SOURCE_PINS.json').read_text())
for n,raw in [
 ('crates/aspis-r1-cost-probe/src/NKM_native.rs',S.encode()),
 ('crates/aspis-core/src/NKM_arbitrary.rs',(E/'NKM_arbitrary.rs.txt').read_bytes()),
 ('crates/aspis-core/src/lib.rs',subprocess.check_output(['git','show',R+':crates/aspis-core/src/lib.rs'])+b'\n#[cfg(kani)]\nmod NKM_arbitrary;\n')]:
 old=oldpins.get(n)
 if old is None:
  r=subprocess.run(['git','show',R+':'+n],capture_output=True);old=hashlib.sha256(r.stdout).hexdigest()if r.returncode==0 else None
 inputs[n]=dict(before=old,sha256=hashlib.sha256(raw).hexdigest(),data=base64.b64encode(raw).decode());oldpins[n]=hashlib.sha256(raw).hexdigest()
(E/'NKM_CONTRACT_OVERLAY.json').write_text(json.dumps(inputs));(E/'NKM_SOURCE_PINS.json').write_text(json.dumps(oldpins,indent=2)+'\n')
frozen=json.loads((E/'NKM_FROZEN_FILE_PINS.json').read_text());frozen.pop('crates/aspis-core/src/lib.rs',None);(E/'NKM_FROZEN_FILE_PINS.json').write_text(json.dumps(frozen,indent=2)+'\n')
patch=''
for n,r in inputs.items():
 old=subprocess.run(['git','show',R+':'+n],capture_output=True);before=old.stdout.decode() if old.returncode==0 else ''
 patch+=''.join(difflib.unified_diff(before.splitlines(True),base64.b64decode(r['data']).decode().splitlines(True),fromfile='a/'+n if before else '/dev/null',tofile='b/'+n))
(E/'NKM_contract_harness.patch').write_text(patch)
p=E/'NKM_gate.py';s=p.read_text().replace("frozen='578",'''for n,row in json.loads((B/'NKM_CONTRACT_OVERLAY.json').read_text()).items():
 p=S/n;current=sha(p) if p.exists() else None
 assert current in [row['before'],row['sha256']],('unexpected overlay input',n)
 raw=base64.b64decode(row['data']);assert hashlib.sha256(raw).hexdigest()==row['sha256']
 if current!=row['sha256']:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(raw)
frozen='578''');p.write_text(s)
p=E/'NKM_run.py';s=p.read_text().replace("'NKM_EXTRA_INPUTS.json']","'NKM_EXTRA_INPUTS.json','NKM_CONTRACT_OVERLAY.json']");p.write_text(s)
base=json.loads((E/'NKM_K011.json').read_text())
jobs=[('result_weak',False,False),('result_inverted',True,False),('result_real',False,False),('result_unimplied',True,False),('result_frame',True,False),('circle_contract',False,False),('circle_contract',True,True),('ood_contract',False,False),('ood_contract',True,True),('fallback_contract',False,False),('fallback_contract',True,True),('copy_control',False,False),('copy_control',True,False)]
for i,(name,negative,invert)in enumerate(jobs,12):
 a=f'NKM_K{i:03}';x=json.loads(json.dumps(base));x['attempt']=a;x['module']='NKM_native::'+name;x['sources'].append('NKM_CONTRACT_OVERLAY.json');x['command'][2]=a+'.json';x['negative_control']=negative;x['native_command'][x['native_command'].index('--harness')+1]=x['module'];x['native_command']+=['-Z','function-contracts'];x['env']['RUSTFLAGS']='-Copt-level=3 -C link-arg=-Wl,--threads=1'+(' --cfg NKM_contract_invert'if invert else ' --cfg NKM_invert'if name=='copy_control'and negative else '')
 x['collect']=[n.replace('NKM_K011',a)for n in x['collect']];x['expected_time']='Optimized native function contract / exact returned-Result fidelity calibration; field ops remain oracle boundaries'
 (E/(a+'.json')).write_text(json.dumps(x))
