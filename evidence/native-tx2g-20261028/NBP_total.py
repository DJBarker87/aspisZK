from pathlib import Path
s='\n'.join('import '+m for m in ['NBP_DecodeWord']+[f'NBP_Decode{i}' for i in range(1,8)]+['NBP_DecodeSuccess'])+'\n'
s+='''set_option autoImplicit false
noncomputable section
namespace NBP_DigestDecode
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder NBP_DecodeWord
/-- Source order, including all noncanonical rejections. -/
def decoded (bytes : Array U8 32#usize) :
    core.result.Result (Array U32 8#usize) atomic_statement.AtomicStatementError :=
'''
for i in range(8):s+=f'  if word bytes {i} >= P then .Err .NonCanonicalDigest else\n'
s+='  .Ok (NBG_WideBytes.limbs bytes)\n\ntheorem result (bytes : Array U8 32#usize) :\n    atomic_statement.decode_digest_canonical bytes = ok (decoded bytes) := by\n'
for i in range(8):
 s+='  '* (i+1)+f'by_cases h{i} : word bytes {i} >= P\n'
 s+='  '*(i+1)+'· '+f'simpa only [decoded,'+','.join(f'h{j},if_neg' for j in range(i))+(',' if i else '')+f'h{i},if_pos] using '+('NBP_DecodeWord.reject0' if i==0 else f'NBP_Decode{i}.result')+' bytes '+ ' '.join(f'(lt_of_not_ge h{j})' for j in range(i))+(' ' if i else '')+f'h{i}\n'
 s+='  '*(i+1)+'· '+ ('\n' if i<7 else 'simpa only [decoded,'+','.join(f'h{j},if_neg' for j in range(8))+'] using NBP_DecodeSuccess.result bytes '+' '.join(f'(lt_of_not_ge h{j})' for j in range(8))+'\n')
s+='\n#print axioms result\nend NBP_DigestDecode\n'
Path('lean/NBP_DigestDecode.lean').write_text(s)
