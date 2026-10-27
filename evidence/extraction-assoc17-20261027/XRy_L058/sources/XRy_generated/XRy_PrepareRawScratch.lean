import XRy_PrepareCallbacks
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRo_Join_ResultTransport XRo_Join_ResultPair
set_option autoImplicit false
noncomputable section
namespace XRy_PrepareRawScratch

def boundaries : AspisR1PublicPreparation.PreparedScratchModel.Boundaries :=
 { sampling := XRo_Join_Installed.actual.sampling
   powers := XRn_Join_Release.weights.powers
   claim := XRo_Join_PreparedBoundaries.cachedClaim }

theorem prepare (low : XRq_SamplerInterface.Low)
 (leaf : ∀ b, low b=AspisR1Post25Sampler.sampler.low_base_p_digits b)
 {H : Type} (D : C.D H) (sem : C.Sem H) (v : C.View) (hash : H)
 (g : Array C.E 29#usize) :
 mapR (fun p => (inner cprepared ce p.1,p.2))
   (XRy_NarrowPrepare.prepare low (ed D) (es sem) (eview v) hash g) =
 AspisR1PublicPreparation.PreparedScratchModel.prepare boundaries D sem v hash g := by
 unfold XRy_NarrowPrepare.prepare AspisR1PublicPreparation.PreparedScratchModel.prepare
 simp only [boundaries,eview]
 rw [XRy_PrepareCallbacks.state]
 simp only [←XRo_Join_Installed.start,←XRy_PrepareCallbacks.scalar low leaf,
   ←XRy_PrepareCallbacks.queries,←XRy_PrepareCallbacks.scalar_k,
   ←XRs_ClosedCallbacks.serializer,←XRo_Join_Transcript.folds,
   mapR_bind,bind_map,map_let_pair,map_if,map_flow,map_ok]
 congr 1
 funext initial
 congr 1
 funext t
 congr 1
 funext pair
 rcases pair with ⟨gamma,t1⟩
 apply XRy_QueryTransport.bind_cont
 intro bytes
 apply XRy_QueryTransport.bind_cont
 intro payload
 rw [←XRy_PrepareCallbacks.scalar low leaf D t1 28#u8 payload false]
 rw [bind_map]
 apply XRy_QueryTransport.bind_cont
 rintro ⟨kappa,t2⟩
 rw [←XRy_PrepareCallbacks.scalar low leaf D t2 29#u8 v.round0 false]
 rw [bind_map]
 apply XRy_QueryTransport.bind_cont
 rintro ⟨alpha0,t3⟩
 apply XRy_QueryTransport.bind_cont
 intro folds
 rw [map_if]
 by_cases hf : folds=2#usize
 · simp only [if_pos hf]
   repeat' (apply XRy_QueryTransport.bind_cont; intro)
   rw [←XRy_PrepareCallbacks.scalar low leaf,bind_map]
   apply XRy_QueryTransport.bind_cont
   rintro ⟨alpha1,t4⟩
   rw [←XRy_PrepareCallbacks.queries,bind_map]
   apply XRy_QueryTransport.bind_cont
   rintro ⟨r,t5⟩
   cases r with
   | Err e => rfl
   | Ok q =>
     trace_state
 · trace_state

#print axioms prepare
end XRy_PrepareRawScratch
end
