from pathlib import Path
import re
E=Path(__file__).resolve().parent;s=(E/'NMT_stage1_owned.Funs.lean').read_text();root='r1_pool_adapter.owned.stage1_owned';sig=s[s.index('def '+root):];sig=sig[:sig.index(':= do')];at=sig.index('\n  (program_id');header=sig[:at].replace('def '+root,'theorem NMT_wrong_count',1);tail=sig[at:sig.rfind(':\n')]
params=re.findall(r'\((NMT_call_\d+) :',header);apply=' '.join(params+['program_id','accounts','data']);err='ok (core.result.Result.Err solana_program_error.ProgramError.InvalidInstructionData)'
text='import NMT_stage1_owned.Funs\nset_option autoImplicit false\nnoncomputable section\nnamespace NMT_stage1_owned\nopen Aeneas Aeneas.Std Result\n'+header+tail+''' (count : (Slice.len accounts != 3#usize)=true) :
 r1_pool_adapter.owned.stage1_owned '''+apply+''' =
 (do
  let first ← NMT_call_1 core.cmp.PartialEqU8 data (Array.make 2#usize [3#u8,10#u8])
  if first then '''+err+''' else do
   let _second ← NMT_call_1 core.cmp.PartialEqU8 data (Array.make 2#usize [3#u8,11#u8])
   '''+err+''') := by
 unfold r1_pool_adapter.owned.stage1_owned
 cases h : NMT_call_1 core.cmp.PartialEqU8 data (Array.make 2#usize [3#u8,10#u8]) with
 | fail e => simp only [h,bind_tc_fail]
 | div => simp only [h,bind_tc_div]
 | ok first =>
   cases first <;> simp only [h,bind_tc_ok, count,ite_true,ite_false]
   cases h2 : NMT_call_1 core.cmp.PartialEqU8 data (Array.make 2#usize [3#u8,11#u8]) with
   | fail e => simp only [h2,bind_tc_fail]
   | div => simp only [h2,bind_tc_div]
   | ok second => cases second <;> simp only [h2,bind_tc_ok,count,ite_true,ite_false]
#print axioms NMT_wrong_count
end NMT_stage1_owned
''';(E/'NMT_345Guard.lean').write_text(text)
