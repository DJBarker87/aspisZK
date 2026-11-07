from pathlib import Path
import re,json,lzma,base64
E=Path(__file__).resolve().parent;x=json.loads(lzma.decompress((E/'PCG_FROZEN_INPUTS.json.xz').read_bytes()))
def enum(text,name):return re.search(r'pub enum '+name+r'\s*\{.*?\n\}',text,re.S)[0]
s=''
for p,n in [('programs/aspis-pool/src/deposit_transport.rs','DepositInstructionFormatErrorV1'),('programs/aspis-pool/src/instruction.rs','PoolInstructionFormatErrorV1')]:
 s+='#[derive(Clone,Copy)]\n'+enum(base64.b64decode(x[p]).decode(),n)+'\n'
s+=enum((E/'PCG_solana_program_error.rs.txt').read_text(),'ProgramError')+'\n'
s+='pub fn reference287(_e:DepositInstructionFormatErrorV1)->PoolInstructionFormatErrorV1{PoolInstructionFormatErrorV1::InvalidDeposit}\n'
s+='pub fn reference288(_e:PoolInstructionFormatErrorV1)->ProgramError{ProgramError::InvalidInstructionData}\n'
(E/'PCG_conversion_reference.rs').write_text(s)
s=(E/'PCG_extract_address.py').read_text().replace('PCG_address_reference.rs','PCG_conversion_reference.rs').replace('PCG_address_ref','PCG_conversion_ref').replace('PCG_address.llbc','PCG_conversion.llbc').replace('PCG_address_extracted','PCG_conversion_extracted').replace('PCG_AddressRef','PCG_ConversionRef').replace('PCG_ADDRESS_EXTRACTION_PINS','PCG_CONVERSION_EXTRACTION_PINS');s=s.replace("roots=['crate::request_'+str(i) for i in [374,375,376,377,390,391,323]]+['crate::stored_matches']","roots=['crate::reference287','crate::reference288']");(E/'PCG_extract_conversions.py').write_text(s)
t=json.loads((E/'PCG_TASKS.json').read_text());t['PCG_E005']=dict(kind='extract',target='Isolated full-carrier From references287/288; changed from timed-out full Pool selection',files={'PCG_extract_conversions.py':'PCG_extract_conversions.py','PCG_conversion_reference.rs':'PCG_conversion_reference.rs'},command=['python3','PCG_extract_conversions.py'],collect=['PCG_CONVERSION_EXTRACTION_PINS.json','PCG_conversion_extracted/PCG_ConversionRef/Types.lean','PCG_conversion_extracted/PCG_ConversionRef/Funs.lean']);(E/'PCG_TASKS.json').write_text(json.dumps(t,indent=1)+'\n')
