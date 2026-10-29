from pathlib import Path
R=Path(__file__).resolve().parents[2];P=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';s=(P/'PV_RDB2D_SamplerCore.lean').read_text();ns='R1Z.PV_RDB2D_SamplerRestoration'
def definition(name):
 a=s.index('def host_sampler.'+name);b=s.index('\n/--',a);return s[a:b].strip()
header='''namespace R1Z.PV_RDB2D_SamplerRestoration
open Aeneas Aeneas.Std Result ControlFlow PV_B2_C_Sampler
set_option autoImplicit false
abbrev Words := Array U32 8#usize

def borrow (current : Words) (index : Usize) : Result (U32 × (Words → U32 → Result Words)) := do
  let word ← Array.index_usize current index
  ok (word,fun now value => Array.update now index value)

theorem restoration (current now : Words) (index : Usize) (word : U32)
    (read : Array.index_usize current index=ok word) :
    borrow current index=ok (word,fun valueStore replacement => Array.update valueStore index replacement) := by
  simp only [borrow,read,bind_tc_ok]
#print axioms restoration
'''
body=definition('low_base_p_digits_loop1_loop0.body').replace('def host_sampler.low_base_p_digits_loop1_loop0.body','def divisionBody').replace('let i1 ← Array.index_usize quotient j1','let (i1,back) ← borrow quotient j1').replace('let quotient1 ← Array.update quotient j1 i5','let quotient1 ← back quotient i5')
proof='''
theorem division_body (q : Words) (r : U64) (j : Usize) :
    divisionBody q r j=host_sampler.low_base_p_digits_loop1_loop0.body q r j := by
  simp only [divisionBody,host_sampler.low_base_p_digits_loop1_loop0.body,borrow,bind_assoc_eq,bind_tc_ok] <;> rfl
#print axioms division_body
end R1Z.PV_RDB2D_SamplerRestoration
'''
(P/'PV_RDB2D_DivisionRestoration.lean').write_text('import R1Z.PV_RDB2D_SamplerCore\n'+header+body+'\n'+proof)
body=definition('add_small_base_p_loop.body').replace('def host_sampler.add_small_base_p_loop.body','def carryBody').replace('let i1 ← Array.index_usize digits i','let (i1,back) ← borrow digits i').replace('let digits1 ← Array.update digits i i6','let digits1 ← back digits i6')
proof='''
theorem carry_body (q : Words) (r : U32) (j : Usize) :
    carryBody q r j=host_sampler.add_small_base_p_loop.body q r j := by
  simp only [carryBody,host_sampler.add_small_base_p_loop.body,borrow,bind_assoc_eq,bind_tc_ok] <;> rfl
#print axioms carry_body
end R1Z.PV_RDB2D_SamplerRestoration
'''
(P/'PV_RDB2D_CarryRestoration.lean').write_text('import R1Z.PV_RDB2D_DivisionRestoration\nnamespace '+ns+'\nopen Aeneas Aeneas.Std Result ControlFlow PV_B2_C_Sampler\nset_option autoImplicit false\n'+body+'\n'+proof)
