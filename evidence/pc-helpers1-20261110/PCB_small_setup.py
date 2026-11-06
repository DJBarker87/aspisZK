from pathlib import Path
import subprocess,json,difflib
E=Path(__file__).resolve().parent
REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';POOL='b936275465600469312d1f058cdc91ea2a11f3dc'
def original(path):return subprocess.check_output(['git','show',(POOL if path.startswith('programs/') else REV)+':'+path],text=True)
files={};patch=''
def save(path,s):
 name='PCB_'+Path(path).stem+'.rs.txt';(E/name).write_text(s);files['PCB_src/'+path]=name
p='crates/aspis-core/src/field.rs';s=original(p).replace('pub struct M31(pub u32);','#[cfg_attr(kani,derive(kani::Arbitrary))]\npub struct M31(pub u32);');save(p,s)
p='crates/aspis-statement/src/pool_v1/root_history.rs';s=(E/'PCB_root_history.rs.txt').read_text();s=s.replace('pub struct RootHistoryPageV1 {','#[cfg_attr(kani,derive(kani::Arbitrary))]\npub struct RootHistoryPageV1 {')
s=s.replace('    pub fn is_full(&self) -> bool {','    #[cfg_attr(all(kani,not(PCB_NEG_242)),kani::ensures(|r| *r == PCB_242::reference(self)))]\n    #[cfg_attr(all(kani,PCB_NEG_242),kani::ensures(|r| *r != PCB_242::reference(self)))]\n    pub fn is_full(&self) -> bool {')
s+='\n#[cfg(any(kani,PCB_EXTRACT))]\n#[path="PCB_242.rs"]\nmod PCB_242;\n';save(p,s)
p='crates/aspis-statement/src/pool_v1/pair_tree_profile.rs';s=original(p).replace('pub struct PoolV1PairLeafWitnessV1 {','#[cfg_attr(kani,derive(kani::Arbitrary))]\npub struct PoolV1PairLeafWitnessV1 {');s=s.replace('    pub fn second_sentinel(&self) -> M31 {','    #[cfg_attr(all(kani,not(PCB_NEG_221)),kani::ensures(|r| *r == PCB_221::reference(self)))]\n    #[cfg_attr(all(kani,PCB_NEG_221),kani::ensures(|r| *r != PCB_221::reference(self)))]\n    pub fn second_sentinel(&self) -> M31 {');s+='\n#[cfg(any(kani,PCB_EXTRACT))]\n#[path="PCB_221.rs"]\nmod PCB_221;\n';save(p,s)
p='programs/aspis-pool/src/pair_forest.rs';s=original(p).replace('pub struct PoolV1PairForestTerminalBumpHintsV1 {','#[cfg_attr(kani,derive(kani::Arbitrary))]\npub struct PoolV1PairForestTerminalBumpHintsV1 {');s=s.replace('    fn vault(self) -> VaultBumpHintsV1 {','    #[cfg_attr(all(kani,not(PCB_NEG_300)),kani::ensures(|r| *r == PCB_300::reference(self)))]\n    #[cfg_attr(all(kani,PCB_NEG_300),kani::ensures(|r| *r != PCB_300::reference(self)))]\n    fn vault(self) -> VaultBumpHintsV1 {');s+='\n#[cfg(any(kani,PCB_EXTRACT))]\n#[path="PCB_300.rs"]\nmod PCB_300;\n';save(p,s)
refs={'242':('crates/aspis-statement/src/pool_v1','pub(super) fn reference(page:&RootHistoryPageV1)->bool { page.filled==256 }','#[kani::proof_for_contract(RootHistoryPageV1::is_full)]\nfn small_contract(){let p:RootHistoryPageV1=kani::any();let _=p.is_full();}'),
'221':('crates/aspis-statement/src/pool_v1','pub(super) fn reference(leaf:&PoolV1PairLeafWitnessV1)->M31 { leaf.second_commitment[7] }','#[kani::proof_for_contract(PoolV1PairLeafWitnessV1::second_sentinel)]\nfn small_contract(){let p:PoolV1PairLeafWitnessV1=kani::any();let _=p.second_sentinel();}'),
'300':('programs/aspis-pool/src','pub(super) fn reference(h:PoolV1PairForestTerminalBumpHintsV1)->VaultBumpHintsV1 { VaultBumpHintsV1 {vault_authority:h.vault_authority,vault_token_account:h.vault_token_account} }','#[kani::proof_for_contract(PoolV1PairForestTerminalBumpHintsV1::vault)]\nfn small_contract(){let p:PoolV1PairForestTerminalBumpHintsV1=kani::any();let _=p.vault();}')}
for id,(folder,ref,harness) in refs.items():
 n='PCB_'+id+'.rs';(E/n).write_text('use super::*;\n'+ref+'\n#[cfg(kani)]\n'+harness+'\n');files['PCB_src/'+folder+'/'+n]=n
for n,v in files.items():
 if not v.endswith('.rs.txt'):continue
 path=n[8:];patch+=''.join(difflib.unified_diff(original(path).splitlines(True),(E/v).read_text().splitlines(True),fromfile='a/'+path,tofile='b/'+path))
(E/'PCB_SMALL.patch').write_text(patch)
t=json.loads((E/'PCB_TASKS.json').read_text());B='/home/dombarker/project-offloads/codex-pc-helpers1-20261110'
for i,id in enumerate(['242','221','300']):
 for neg in [False,True]:
  a=f'PCB_K{25+2*i+int(neg):03}';x=json.loads(json.dumps(t['PCB_K015']));x['files']={'PCB_gate.py':'PCB_gate.py',**files,**{k:v for k,v in t['PCB_K014']['files'].items() if k not in files}};x['target']='POOL:'+id+(' inverted control' if neg else ' actual contract');x['command']=['python3','PCB_gate.py',a+'.json'];x['collect']=[n.replace('PCB_K015',a) for n in x['collect']];stem={'242':'pool_v1::root_history','221':'pool_v1::pair_tree_profile','300':'pair_forest'}[id];x['native_command'][x['native_command'].index('--harness')+1]=stem+'::PCB_'+id+'::small_contract'
  if id=='300':
   x['native_command'][x['native_command'].index('--manifest-path')+1]=B+'/PCB_src/programs/aspis-pool/Cargo.toml';x['native_command'][x['native_command'].index('--features')+1]=','.join(s.split('/',1)[1] for s in x['pool_features'].split(','))
  if neg:x['env']={'RUSTFLAGS':f'-C link-arg=-Wl,--threads=1 --cfg PCB_NEG_{id}'}
  t[a]=x
(E/'PCB_TASKS.json').write_text(json.dumps(t,indent=1)+'\n')
