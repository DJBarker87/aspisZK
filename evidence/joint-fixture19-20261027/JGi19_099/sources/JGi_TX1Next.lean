import JGi_TX1Control
set_option autoImplicit false
namespace AspisR1.JGi_TX1Next
open Aeneas Aeneas.Std Result AspisR1CurrentCaller

/-- Forward source control at the next actual cut. The full enclosing prepare
call is an explicit local obligation; originalNew alone is not substituted. -/
theorem source {H : Type} (ops : Ops) (D : aspis_core.digest.Digest32 H)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (hash : H) (zero : aspis_core.field.wide_exact.WideExact)
    (p : verifier.Prepared) (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (zeroCall : aspis_core.field.wide_exact.WideExact.ZERO ops=ok zero)
    (prepareCall : verifier.candidate.prepare ops D semantic proof hash none (Array.repeat 29#usize zero)=ok (.Ok p,scratch)) :
    JGi_TX1Control.afterScan ops D semantic pub proof hash=
      Tx1Reachability.afterPrepare ops D pub proof 10#usize hash none p scratch := by
  unfold JGi_TX1Control.afterScan
  simp only [zeroCall,prepareCall,bind_tc_ok,Aeneas.Std.uncurry]
#print axioms source
end AspisR1.JGi_TX1Next
