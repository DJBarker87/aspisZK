from pathlib import Path
import subprocess,json,difflib
E=Path(__file__).resolve().parent;P='b936275465600469312d1f058cdc91ea2a11f3dc';R='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
path='programs/aspis-pool/src/registry.rs';orig=subprocess.check_output(['git','show',P+':'+path],text=True)
s=orig.replace('pub(crate) struct AuthenticatedVerifierSelectionV1 {','#[cfg_attr(kani,derive(kani::Arbitrary))]\npub(crate) struct AuthenticatedVerifierSelectionV1 {')
s=s.replace('    pub(crate) fn matches(\n','    #[cfg_attr(all(kani,not(PCB_NEG_370)),kani::ensures(|r| *r == PCB_370::reference(self,pool,verifier_program,profile_binding,release_binding,statement_version)))]\n    #[cfg_attr(all(kani,PCB_NEG_370),kani::ensures(|r| *r != PCB_370::reference(self,pool,verifier_program,profile_binding,release_binding,statement_version)))]\n    pub(crate) fn matches(\n')
s=s.replace('    pub(crate) fn matches_verifier_owner(self, owner: &Pubkey) -> bool {','    #[cfg_attr(all(kani,not(PCB_NEG_371)),kani::ensures(|r| *r == PCB_371::reference(self,owner)))]\n    #[cfg_attr(all(kani,PCB_NEG_371),kani::ensures(|r| *r != PCB_371::reference(self,owner)))]\n    pub(crate) fn matches_verifier_owner(self, owner: &Pubkey) -> bool {')
for id in ['370','371']:s+=f'\n#[cfg(any(kani,PCB_EXTRACT))]\n#[path="PCB_{id}.rs"]\nmod PCB_{id};\n'
(E/'PCB_registry.rs.txt').write_text(s);(E/'PCB_REGISTRY.patch').write_text(''.join(difflib.unified_diff(orig.splitlines(True),s.splitlines(True),fromfile='a/'+path,tofile='b/'+path)))
(E/'PCB_370.rs').write_text('''use super::*;
pub(super) fn reference(s:AuthenticatedVerifierSelectionV1,pool:[u8;32],verifier_program:[u8;32],profile_binding:[u8;32],release_binding:[u8;32],statement_version:u8)->bool {
 s.pool==pool && s.verifier_program==verifier_program && s.profile_binding==profile_binding && s.release_binding==release_binding && s.statement_version==statement_version
}
#[cfg(kani)] #[kani::proof_for_contract(AuthenticatedVerifierSelectionV1::matches)]
fn matches_contract(){let s:AuthenticatedVerifierSelectionV1=kani::any();let _=s.matches(kani::any(),kani::any(),kani::any(),kani::any(),kani::any());}
''')
(E/'PCB_371.rs').write_text('''use super::*;
pub(super) fn reference(s:AuthenticatedVerifierSelectionV1,owner:&Pubkey)->bool {
 match s.expected_verifier_loader {None=>true,Some(expected)=>owner.to_bytes()==expected}
}
#[cfg(kani)] #[kani::proof_for_contract(AuthenticatedVerifierSelectionV1::matches_verifier_owner)]
fn owner_contract(){let s:AuthenticatedVerifierSelectionV1=kani::any();let owner=Pubkey::new_from_array(kani::any());let _=s.matches_verifier_owner(&owner);}
''')
p='crates/aspis-statement/src/pool_v1/format.rs';origf=subprocess.check_output(['git','show',R+':'+p],text=True);sf=origf.replace('pub struct VerifierPolicyV1 {','#[cfg_attr(kani,derive(kani::Arbitrary))]\npub struct VerifierPolicyV1 {');(E/'PCB_format.rs.txt').write_text(sf);(E/'PCB_FORMAT.patch').write_text(''.join(difflib.unified_diff(origf.splitlines(True),sf.splitlines(True),fromfile='a/'+p,tofile='b/'+p)))
t=json.loads((E/'PCB_TASKS.json').read_text())
for i,(id,h,neg) in enumerate([('370','matches_contract',False),('370','matches_contract',True),('371','owner_contract',False),('371','owner_contract',True)]):
 a=f'PCB_K{45+i:03}';x=json.loads(json.dumps(t['PCB_K041']));x['files'].update({'PCB_src/'+path:'PCB_registry.rs.txt','PCB_src/'+p:'PCB_format.rs.txt','PCB_src/programs/aspis-pool/src/PCB_370.rs':'PCB_370.rs','PCB_src/programs/aspis-pool/src/PCB_371.rs':'PCB_371.rs'});x['command']=['python3','PCB_gate.py',a+'.json'];x['collect']=[n.replace('PCB_K041',a) for n in x['collect']];x['target']='POOL:'+id+(' inverted control' if neg else ' actual contract');x['native_command'][x['native_command'].index('--harness')+1]='registry::PCB_'+id+'::'+h
 if neg:x['env']={'RUSTFLAGS':'-C link-arg=-Wl,--threads=1 --cfg PCB_NEG_'+id}
 t[a]=x
(E/'PCB_TASKS.json').write_text(json.dumps(t,indent=1)+'\n')
