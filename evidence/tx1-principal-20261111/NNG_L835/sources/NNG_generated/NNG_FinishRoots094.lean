import NNG_ModelHead136
import RPz7_S1SemanticFinishRootsV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_FinishRoots094
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NNG_Transport
/-- The SAME complete finish copies C1 into its first root slot. -/
theorem returned {W : Type} (env : RSL.Env) (s : Parent Unit W) (out : r1_semantic.Verified Unit)
 (native : NNG_Emitted.emitted (NNG_ConcreteCalls136.calls env) s=.ok (.Ok out)) :
 ∃ root,(toT11 out).roots=Array.make 2#usize [(toT12 s.prefixValue).c1_root,root] := by
 have model := NNG_ModelSuccess136.finish env s out native
 obtain ⟨payload,copied,root,_,_,_,same⟩ := AspisR1PublicPreparation.S1SemanticFinishRoots.finish_root_calls
  AspisS1ExtractedRoundChildren.children (NNG_LegacyConfig136.boundaries env)
  (NNG_Install.digest s.digest) (toT9 s.publicValue) (toT12 s.prefixValue)
  (toT10 s.transcript) (toT3 s.challenges) none (toT11 out) model
 exact ⟨root,same⟩
#print axioms returned
end AspisR1.NNG_FinishRoots094
