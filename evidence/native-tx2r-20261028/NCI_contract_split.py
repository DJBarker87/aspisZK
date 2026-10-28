from NCI_extend import edit,attrs
from pathlib import Path
E=Path(__file__).resolve().parent

def transform(s):
 start=s.index('#[cfg(kani)] mod NCI_contracts')
 end=s.find('#[cfg(kani)] mod NCI_steps',start)
 if end<0:end=len(s)
 part=s[start:end]
 part=part.replace('r.bytes.len()==64 && r.at<=48','r.bytes.len()==64 && r.at<=48 && index<16')
 for fn in ['weak','weak_bad','inverted','bad_modifies','strong']:
  part=part.replace(f"fn {fn}(r:&mut Reader<'_>)",f"fn {fn}(r:&mut Reader<'_>,index:usize)")
  part=part.replace(fn+'(&mut r)',fn+'(&mut r,index)')
 part=part.replace('out[0]!=r.bytes[old(r.at)]','out[index]!=r.bytes[old(r.at)+index]')
 part=part.replace('(0..16).all(|j|out[j]==r.bytes[old(r.at)+j])','out[index]==r.bytes[old(r.at)+index]')
 part=part.replace('let mut r=Reader{bytes:&bytes,at:start};','let index:usize=kani::any();kani::assume(index<16);let mut r=Reader{bytes:&bytes,at:start};')
 part=part.replace('let j:usize=kani::any();kani::assume(j<16);','let j=index;')
 last=part.rfind('}')
 new=attrs+'''#[kani::stub_verified(strong)]
fn parent_domain(){let bytes=[0u8;1768];let mut r=Reader{bytes:&bytes,at:712};let _=strong(&mut r,0);}
'''
 part=part[:last]+new+part[last:]
 return s[:start]+part+s[end:]
edit('NCI_contract_cell.patch',transform)
