import NNG_StateCalls094
import LIBC_Usize
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_GeometryCall094
open Aeneas Aeneas.Std Result NMT_tx1 NNG_Carriers094 NNG_StateCalls094

theorem graph (env : RSL.Env) (p : verifier.Prepared) (start finish : Usize)
 (domain : LIBC_Geometry.Domain (toT12 p,start.val,finish.val)) :
 LIBC_Geometry.child.run (toT12 p,start.val,finish.val) env
  (LIB_Carriers.resultObs (port toT14) [] (geometry env p.queries start finish)) := by
 refine ⟨domain,Or.inl ?_⟩
 have first : LIBC_Usize.raw start.val=start := LIBC_Usize.from_native start start.hmax
 have last : LIBC_Usize.raw finish.val=finish := LIBC_Usize.from_native finish finish.hmax
 change _=LIB_Carriers.resultObs LIBC_Geometry.port []
  (Port3_GeometryStage.geometry NFN_NEW_GeometryDictionary.adopted (toT12 p).queries
   (LIBC_Usize.raw start.val) (LIBC_Usize.raw finish.val))
 rw [first,last]
 apply obs_outer
 intro r
 rw [port_reply]
 cases r <;> simp only [fromT14_inverse,LIBC_Geometry.port]
#print axioms graph
end AspisR1.NNG_GeometryCall094
