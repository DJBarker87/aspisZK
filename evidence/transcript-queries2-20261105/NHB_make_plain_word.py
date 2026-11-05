from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent;mode=sys.argv[1] if len(sys.argv)>1 else 'full'
subprocess.run([sys.executable,str(E/'NHB_make_direct_word.py'),mode],check=True)
s=(E/'NHB_direct_word.rs.txt').read_text();lines=s.splitlines(True)
requires=next(x.strip()[len('#[kani::requires('):-2] for x in lines if x.startswith('#[kani::requires('))
base=requires.split(' && old_value==')[0]
lines=[x for x in lines if not x.startswith(('#[kani::requires','#[kani::ensures'))]
s=''.join(lines).replace('#[kani::proof_for_contract(NHB_native_word)]','#[kani::proof]')
a=s.index('fn NHB_native_word_contract()');s=s[:a]+'''fn NHB_native_word_contract() {
 let accepted:[u32;22]=kani::any();let len:usize=kani::any();let draws:usize=kani::any();
 let block:[u8;32]=kani::any();let start:usize=kani::any();let window:usize=kani::any();
 kani::assume('''+base+''');
 let old_value=accepted[window];
 let candidate=u32::from_le_bytes([block[4*start],block[4*start+1],block[4*start+2],block[4*start+3]]) & ((1<<18)-1);
 let member=NHB_natural_member(&accepted,len,candidate);
 let expected=NHB_scalar_ref(len,draws,start,window,old_value,candidate,member);
 let actual=NHB_native_word(accepted,len,draws,block,start,window,old_value,candidate,member);
 assert!(actual==expected);
}
'''
(E/'NHB_plain_word.rs.txt').write_text(s)
(E/'NHB_PLAIN_WORD.json').write_text(json.dumps(dict(mode=mode,annotation='ordinary proof window; historical harness name unchanged',change='pre-observations computed directly before call; no contract snapshots or array-containing postcondition closures',native_contains='executed, not stubbed',external_modifies='owned values only; full pointwise poststate observed',source_body_unchanged=True),indent=2)+'\n')
