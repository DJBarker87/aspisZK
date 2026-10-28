"""Generate executable Lean observations; not a theorem or decision proof."""
from pathlib import Path
D=Path('evidence/pv-b3p6-20261028/lean');p=2147483647
q=lambda n:'{ c0 := { a := '+str(n%p)+'#u32, b := '+str((n*17)%p)+'#u32 }, c1 := { a := '+str((n*31)%p)+'#u32, b := '+str((n*47)%p)+'#u32 } }'
def arr(values):return '(Array.make '+str(len(values))+'#usize ['+',\n'.join(values)+'] (by rfl))'
out=['import PV_B3P_P227_06\nnamespace PV_B3P_Fidelity227\nopen Aeneas Aeneas.Std PV_B3P_227\nset_option autoImplicit false\n-- Executable finite validation only; none of these evaluations is a theorem.\ndef report {n : Usize} (r : Result (Array aspis_core.field.QM31 n)) : String :=\n match r with\n | .ok xs => reprStr (xs.val.flatMap (fun q => [q.c0.a.val,q.c0.b.val,q.c1.a.val,q.c1.b.val]))\n | .fail _ => "FAIL"\n | .div => "DIV"\n']
for seed in (0,1,7,19):
 out.append(f'def state{seed} : Array aspis_core.field.QM31 16#usize := '+arr([q((seed+1)*131+i)for i in range(16)]))
 out.append(f'def constants{seed} : Array U32 16#usize := '+arr([str((seed+1)*173+i)+'#u32'for i in range(16)]))
 out.append(f'def extConstants{seed} : Array aspis_core.field.QM31 16#usize := '+arr([q((seed+1)*173+i)for i in range(16)]))
 for name,args in [('external_linear_lazy',f'state{seed}'),('internal_linear_lazy',f'state{seed}'),('full_round',f'state{seed} extConstants{seed}'),('full_round_m31_constants',f'state{seed} constants{seed}'),('full_round_packed',f'state{seed} extConstants{seed}'),('full_round_m31_constants_packed',f'state{seed} constants{seed}'),('internal_round',f'state{seed} ({q(seed+71)})')]:
  out.append(f'#eval "{name}:{seed}=" ++ report (reference_poseidon.{name} {args})')
 ps=[]
 for i in range(3):ps.append(f'let p{i} ← reference_field.PreparedQm31Multiplier.new ({q((seed+1)*31+i)});')
 prepared='(do '+ ' '.join(ps)+' let value ← reference_field.qm31_sum_products3_prepared '+arr(['p0','p1','p2'])+' '+arr([q((seed+1)*43+i)for i in range(3)])+'; .ok '+arr(['value'])+')'
 out.append(f'#eval "qm31_sum_products3_prepared:{seed}=" ++ report '+prepared)
 dot='(do let value ← reference_field.qm31_m31_dot '+arr([q((seed+1)*59+i)for i in range(7)])+' '+arr([str((seed+1)*61+i)+'#u32'for i in range(7)])+'; .ok '+arr(['value'])+')'
 out.append(f'#eval "qm31_m31_dot:{seed}=" ++ report '+dot)
out.append('end PV_B3P_Fidelity227\n');(D/'PV_B3P_Fidelity227.lean').write_text('\n\n'.join(out))
