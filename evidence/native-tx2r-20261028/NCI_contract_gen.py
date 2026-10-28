from NCI_extend import extend,attrs
h='''
#[cfg(kani)] mod NCI_contracts {
use super::*;
#[kani::requires(r.bytes.len()==64 && r.at<=48)]
#[kani::modifies(&mut r.at)]
#[kani::ensures(|_: &[u8;16]| r.at==old(r.at)+16)]
fn weak(r:&mut Reader<'_>)->[u8;16]{r.raw::<16>()}
#[kani::requires(r.bytes.len()==64 && r.at<=48)]
#[kani::modifies(&mut r.at)]
#[kani::ensures(|out: &[u8;16]| out[0]!=r.bytes[old(r.at)])]
fn inverted(r:&mut Reader<'_>)->[u8;16]{r.raw::<16>()}
#[kani::requires(r.bytes.len()==64 && r.at<=48)]
#[kani::modifies()]
#[kani::ensures(|_: &[u8;16]| true)]
fn bad_modifies(r:&mut Reader<'_>)->[u8;16]{r.raw::<16>()}
#[kani::requires(r.bytes.len()==64 && r.at<=48)]
#[kani::modifies(&mut r.at)]
#[kani::ensures(|out: &[u8;16]| r.at==old(r.at)+16 && (0..16).all(|j|out[j]==r.bytes[old(r.at)+j]))]
fn strong(r:&mut Reader<'_>)->[u8;16]{r.raw::<16>()}
'''
na=attrs.replace('#[kani::proof] ','')
for func in ['weak','inverted','bad_modifies','strong']:
 h+=f'#[kani::proof_for_contract({func})] '+na+f'''fn {func}_contract(){{let bytes:[u8;64]=kani::any();let start:usize=kani::any();let mut r=Reader{{bytes:&bytes,at:start}};let _={func}(&mut r);}}\n'''
for kind in ['real_bytes','weak_cursor','weak_unimplied','strong_bytes','strong_wrong']:
 attr=attrs
 if kind.startswith('weak'):attr+='#[kani::stub_verified(weak)]\n'
 if kind.startswith('strong'):attr+='#[kani::stub_verified(strong)]\n'
 fn='strong' if kind.startswith('strong') else 'weak'
 assertion='r.at==start+16' if kind=='weak_cursor' else 'out[j]'+('!=' if kind=='strong_wrong' else '==')+'bytes[start+j]'
 h+=attr+f'''fn {kind}(){{let bytes:[u8;64]=kani::any();let start:usize=kani::any();kani::assume(start<=48);let mut r=Reader{{bytes:&bytes,at:start}};let out={fn}(&mut r);let j:usize=kani::any();kani::assume(j<16);assert!({assertion});}}\n'''
h+='}\n'
extend('NCI_contracts.patch',h)
