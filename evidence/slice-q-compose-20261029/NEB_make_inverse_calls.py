from pathlib import Path
E=Path(__file__).resolve().parent
steps=[('m','mul','x','x'),('t2','mul','m','x'),('m1','square','t2','2'),('t4','mul','m1','t2'),('m2','square','t4','4'),('t8','mul','m2','t4'),('m3','square','t8','8'),('t16','mul','m3','t8'),('m4','square','t16','8'),('t24','mul','m4','t8'),('m5','square','t24','4'),('t28','mul','m5','t4'),('m6','mul','t28','t28'),('t29','mul','m6','x'),('t30','mul','t29','t29'),('m7','mul','t30','t30'),('out','mul','m7','x')]
s='''import NEB_SquareDomains
import NBG_InverseBridge
set_option autoImplicit false
noncomputable section
namespace NEB_InverseCalls
open Aeneas Aeneas.Std Result AspisR1
'''
s+='\n/-- The actual seventeen-call DAG; no canonical input assumption or inner\ncallee domain/interpretation hypothesis is added. Zero is handled separately. -/\ntheorem nonzero (x : U32) (nonzero : x != 0#u32) :\n    ∃ '+' '.join(t[0] for t in steps)+' : U32,\n'
calls=[]
for n,kind,a,b in steps:
 expr=(f'FIo_Native.aspis_core.field.M31.mul {a} {b}' if kind=='mul' else f'AspisR1M31Inverse.field.square_n FIo_Native.aspis_core.field.M31.mul {a} {b}#usize')
 calls.append(expr);s+=f'      {expr}=ok {n} ∧ {n}.val<2147483647 ∧\n'
s+='      AspisR1M31Inverse.field.M31.inv FIo_Native.aspis_core.field.M31.mul x=ok out := by\n'
for n,kind,a,b in steps:
 if kind=='mul':s+=f'  obtain ⟨{n},h_{n},_,c_{n}⟩ := LPf_BaseMultiply.source {a} {b}\n'
 else:s+=f'  obtain ⟨{n},h_{n},_,c_{n}0⟩ := NEB_SquareDomains.source {a} {b}#usize\n  have c_{n} : {n}.val<2147483647 := c_{n}0 (by decide)\n'
s+='  refine ⟨'+','.join(t[0] for t in steps)+','+','.join(q for t in steps for q in ['h_'+t[0],'c_'+t[0]])+',?_⟩\n'
s+='  simp only [AspisR1M31Inverse.field.M31.inv,nonzero,bind_tc_ok,\n    '+','.join('h_'+t[0] for t in steps)+']\n  simp [massert]\n'
s+='''
theorem zero : AspisR1M31Inverse.field.M31.inv FIo_Native.aspis_core.field.M31.mul 0#u32 =
    Port4C_InverseExecution.inverse_owned 0#u32 := NBG_InverseBridge.inverse_result _

#print axioms nonzero
#print axioms zero
end NEB_InverseCalls
end
'''
(E/'NEB_InverseCalls.lean').write_text(s)
