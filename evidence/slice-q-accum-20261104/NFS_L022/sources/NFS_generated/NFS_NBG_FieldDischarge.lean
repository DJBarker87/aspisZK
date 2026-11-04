import Lean
import NFN_PhaseTransport
import NFS_LPi_MixedValues
import NFS_NBG_WideCarriers

set_option autoImplicit false
namespace NFS_NBG_FieldDischarge
open Aeneas Aeneas.Std Result AspisR1 NFN_LPi_FieldValues

def modQ (q : QW) : QW :=
  ((q.1.1%2147483647,q.1.2%2147483647),(q.2.1%2147483647,q.2.2%2147483647))
def scaleQ (q : QW) (s : Nat) : QW :=
  ((q.1.1*s%2147483647,q.1.2*s%2147483647),
   (q.2.1*s%2147483647,q.2.2*s%2147483647))

theorem canonical_fio (x : NQ) : ∃ z,
    FIo_Native.aspis_core.field.wide_exact.canonical_qm31 x = ok z ∧
      canonQ z ∧ qw z = modQ (qw x) := by
  obtain ⟨a,ha,va⟩ := NFS_NBG_WideCarriers.remainder x.c0.a
  obtain ⟨b,hb,vb⟩ := NFS_NBG_WideCarriers.remainder x.c0.b
  obtain ⟨c,hc,vc⟩ := NFS_NBG_WideCarriers.remainder x.c1.a
  obtain ⟨d,hd,vd⟩ := NFS_NBG_WideCarriers.remainder x.c1.b
  have ca : a.val<2147483647 := by rw [va]; exact Nat.mod_lt _ (by decide)
  have cb : b.val<2147483647 := by rw [vb]; exact Nat.mod_lt _ (by decide)
  have cc : c.val<2147483647 := by rw [vc]; exact Nat.mod_lt _ (by decide)
  have cd : d.val<2147483647 := by rw [vd]; exact Nat.mod_lt _ (by decide)
  refine ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,?_,⟨⟨ca,cb⟩,⟨cc,cd⟩⟩,
    Prod.ext (Prod.ext va vb) (Prod.ext vc vd)⟩
  simp only [FIo_Native.aspis_core.field.wide_exact.canonical_qm31,
    FIo_Native.aspis_core.field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call,
    FIo_Native.aspis_core.field.P,ha,hb,hc,hd,bind_tc_ok]

theorem wide_scale (x : NE) (s : U32) : ∃ z,
    FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 x s = ok z ∧
      canonE z ∧ ew z = (scaleQ (qw x.c0) (s.val%2147483647),
        scaleQ (qw x.c1) (s.val%2147483647)) := by
  obtain ⟨r,hr,vr⟩ := NFS_NBG_WideCarriers.remainder s
  obtain ⟨a,ha,ca,va⟩ := NFS_LPi_MixedValues.qm_m31 x.c0 r
  obtain ⟨b,hb,cb,vb⟩ := NFS_LPi_MixedValues.qm_m31 x.c1 r
  refine ⟨⟨a,b⟩,?_,⟨ca,cb⟩,Prod.ext ?_ ?_⟩
  · simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31,
      FIo_Native.aspis_core.field.P,hr,ha,hb,bind_tc_ok]
  · simpa only [ew,scaleQ,qw,cw,vr] using va
  · simpa only [ew,scaleQ,qw,cw,vr] using vb

theorem wide_qm (x : NE) (y : NQ) (hx : canonE x) : ∃ z,
    FIo_Native.aspis_core.field.wide_exact.WideExact.mul_qm31 x y = ok z ∧
      canonE z ∧ ew z = (mulQ (qw x.c0) (modQ (qw y)),
        mulQ (qw x.c1) (modQ (qw y))) := by
  obtain ⟨r,hr,cr,vr⟩ := canonical_fio y
  obtain ⟨a,ha,ca,va⟩ := NFS_LPi_TowerValues.qm_mul x.c0 r hx.1 cr
  obtain ⟨b,hb,cb,vb⟩ := NFS_LPi_TowerValues.qm_mul x.c1 r hx.2 cr
  refine ⟨⟨a,b⟩,?_,⟨ca,cb⟩,Prod.ext ?_ ?_⟩
  · simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.mul_qm31,hr,ha,hb,bind_tc_ok]
  · simpa only [ew,vr] using va
  · simpa only [ew,vr] using vb

#print axioms canonical_fio
#print axioms wide_scale
#print axioms wide_qm
#print axioms AspisR1.NFN_LPf_BaseMultiply.source
#print axioms AspisR1.NFN_LPi_FieldValues.cm_mul
#print axioms AspisR1.NFS_LPi_TowerValues.qm_mul
#print axioms AspisR1.NFS_LPi_TowerValues.wide_mul
#print axioms AspisR1.NFS_LPi_TowerValues.mul_u
#print axioms AspisR1.NFS_LPi_MixedValues.cm_m31
#print axioms AspisR1.NFS_LPi_MixedValues.qm_m31
end NFS_NBG_FieldDischarge

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
