import NNG_CheckpointGraph345
import NNG_Calls345
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_CheckpointField345
open Aeneas Aeneas.Std NMT_345 RSL

theorem clone_true (e : PE) : NNG_Observe345.clone true e=.ok e := by
 simp only [NNG_Observe345.clone,Bool.not_true,Bool.and_false,Bool.false_eq_true,if_false]
#print axioms clone_true

theorem ops_true : NNG_LengthNative345.ops true=NGL_CheckpointModel.install baseOps := by
 unfold NNG_LengthNative345.ops
 have f : (fun e=>mapOuter toPE (NNG_Observe345.clone true (fromPE e)))=
  (NGL_CheckpointModel.install baseOps).op35 := by
  funext e
  rw [clone_true]
  change Result.ok (toPE (fromPE e))=Result.ok e
  rw [to_fromPE]
 rw [f]
#print axioms ops_true

theorem source (a : Account) (program : Key) (writable : Bool) (env : Env) :
 (NNG_Calls345.calls env).c14 a program writable=
 mapOuter (mapCore id fromPE) (NNG_EquationNative345.native true a program writable) := by
 unfold NNG_Calls345.calls NNG_EquationNative345.native
 rw [ops_true]
#print axioms source

theorem observation (a : Account) (program : Key) (writable : Bool) (env : Env) :
 NNG_Observe345.observe id ((NNG_Calls345.calls env).c14 a program writable)=
 NNG_Phases345.checkpointObservation true (account a) (key program) writable := by
 rw [source]
 exact NNG_CheckpointGraph345.native_eq true a program writable
#print axioms observation
end AspisR1.NNG_CheckpointField345
