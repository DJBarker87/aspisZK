"""One exact original-byte observation, avoiding the excluded dense word shape."""
from pathlib import Path
E=Path(__file__).resolve().parent;s=(E/'NHF_wide.rs.txt').read_text()
a=s.index('const NHF_WINDOW:');b=s.index("fn cut<'a>",a)
body='''const NHF_BYTE:usize=NHF_BYTE_VALUE;
impl DecodeLog {fn decode(&mut self,bytes:&[u8])->Option<E>{
 self.calls+=1;assert!(bytes.as_ptr() as usize==self.proof+7495&&bytes.len()==32);
 assert_eq!(bytes[NHF_BYTE],self.original_byte);
 if let Some(value)=self.reply{
  let actual=((value.to_limbs()[NHF_BYTE/4]>>(8*(NHF_BYTE%4)))&255) as u8;
  kani::assume(actual==bytes[NHF_BYTE]);
 }
 self.reply}}
'''
s=s[:a]+body+s[b:]
s=s.replace('struct DecodeLog {proof:usize,reply:Option<E>,calls:usize}','struct DecodeLog {proof:usize,reply:Option<E>,calls:usize,original_byte:u8}')
s=s.replace('let slot=NHF_WINDOW;','let slot=NHF_BYTE/4;')
s=s.replace('reply,calls:0};','reply,calls:0,original_byte:proof[7495+NHF_BYTE]};')
s=s.replace('assert_eq!(v.inactive.to_limbs()[slot],natural_word(&proof[7495..7527],NHF_WINDOW));','assert_eq!(((v.inactive.to_limbs()[slot]>>(8*(NHF_BYTE%4)))&255) as u8,proof[7495+NHF_BYTE]);')
s=s.replace('// One fixed limb window: Some covers canonical input, None covers an invalid\n// word at this window. Lean joins all eight on the SAME reply/source bytes.','// One immutable byte window on the ORIGINAL arbitrary full proof. The CLOSED\n// decoder packet supplies the tag and all other byte laws; this cut enforces\n// its selected Some-byte law and treats None conservatively. Lean assembles\n// all32 observations on the SAME produced record, not independent replies.')
(E/'NHF_WIDE_BYTE_TEMPLATE.rs.txt').write_text(s)
