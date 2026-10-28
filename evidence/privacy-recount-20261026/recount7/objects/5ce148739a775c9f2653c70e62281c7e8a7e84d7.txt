import R1Z.ProverRwP6BodyData
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP6BodyGammaPort
open Aeneas Aeneas.Std Result ProverRwFull ProverRwP6PowersNativeStep
variable [ExternalTypes]
def gammaPort (ops : ExternalFuns) (N : Usize) (x : W) : Result (Array W N) :=
  if h : N=29#usize then
    h.symm ▸ ProverRwP6ResultMap.map (ProverRwP6ArrayMap.map fromW)
      (AspisR1ProducerRelease47.gamma (toW x))
  else (ProverRwP6BodyStore.selected ops).op254 N x

theorem port_source (ops : ExternalFuns) (N : Usize) (x : W) :
    gammaPort ops N x = (ProverRwP6BodyStore.selected ops).op254 N x := by
  unfold gammaPort
  split
  · next h => subst N; exact (ProverRwP6BodyGamma.source ops x).symm
  · rfl

theorem restore254 (d : ExternalFuns) : {d with op254 := d.op254}=d := rfl

def dictionary (ops : ExternalFuns) : ExternalFuns :=
  {ProverRwP6BodyStore.selected ops with op254 := gammaPort ops}

theorem dictionary_exact (ops : ExternalFuns) : dictionary ops = ProverRwP6BodyStore.selected ops :=
  (congrArg (fun cb => {ProverRwP6BodyStore.selected ops with op254 := cb})
    (funext (fun N => funext (fun x => port_source ops N x)))).trans
    (restore254 (ProverRwP6BodyStore.selected ops))

-- Complete actual caller Result. This substitution uses the proved gamma
-- equation on all raw inputs; it does not assume a successful caller or a
-- returned-proof equality, and it does not assert equality to the security game.
theorem body (ops : ExternalFuns) {S : Type}
    (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (v : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (binding digest : Array U8 32#usize)
    (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets) (s : S) :
    ProverRwBodyNativeWideInstall.execute (dictionary ops) store pub compiled v hash binding digest attempt s =
      ProverRwP6BodyStore.execute ops store pub compiled v hash binding digest attempt s :=
  congrArg (fun d => ProverRwBodyNativeWideInstall.execute d store pub compiled v hash
    binding digest attempt s) (dictionary_exact ops)
#print axioms port_source
#print axioms restore254
#print axioms dictionary_exact
#print axioms body
end R1Z.ProverRwP6BodyGammaPort
