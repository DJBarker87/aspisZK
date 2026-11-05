"""Split the excluded dense byte-law cut by one fixed native limb window."""
from pathlib import Path
E=Path(__file__).resolve().parent;p=E/'NHF_wide.rs.txt';s=p.read_text()
a=s.index('impl DecodeLog');b=s.index("fn cut<'a>",a)
body='''const NHF_WINDOW:usize=NHF_WINDOW_VALUE;
fn natural_word(bytes:&[u8],i:usize)->u32{let at=4*i;u32::from_le_bytes([bytes[at],bytes[at+1],bytes[at+2],bytes[at+3]])}
impl DecodeLog {fn decode(&mut self,bytes:&[u8])->Option<E>{
 self.calls+=1;assert!(bytes.as_ptr() as usize==self.proof+7495&&bytes.len()==32);
 match self.reply{
 None=>kani::assume(natural_word(bytes,NHF_WINDOW)>=2147483647),
 Some(value)=>{
  kani::assume(natural_word(bytes,0)<2147483647);
  kani::assume(natural_word(bytes,1)<2147483647);
  kani::assume(natural_word(bytes,2)<2147483647);
  kani::assume(natural_word(bytes,3)<2147483647);
  kani::assume(natural_word(bytes,4)<2147483647);
  kani::assume(natural_word(bytes,5)<2147483647);
  kani::assume(natural_word(bytes,6)<2147483647);
  kani::assume(natural_word(bytes,7)<2147483647);
  kani::assume(value.to_limbs()[NHF_WINDOW]==natural_word(bytes,NHF_WINDOW));
 }}self.reply}}
'''
s=s[:a]+body+s[b:]
s=s.replace('let slot:usize=kani::any();kani::assume(slot<8);','let slot=NHF_WINDOW;')
s=s.replace('assert_eq!(v.inactive.to_limbs()[slot],expected.to_limbs()[slot]);','assert_eq!(v.inactive.to_limbs()[slot],expected.to_limbs()[slot]);\n  assert_eq!(v.inactive.to_limbs()[slot],natural_word(&proof[7495..7527],NHF_WINDOW));')
s=s.replace('// Full byte/Option packet constraints are enforced in DecodeLog::decode.\n// The same-input natural law is NHF_ViewDecoder.result; no success premise.','// One fixed limb window: Some covers canonical input, None covers an invalid\n// word at this window. Lean joins all eight on the SAME reply/source bytes.')
(E/'NHF_WIDE_WINDOW_TEMPLATE.rs.txt').write_text(s)
