import S1PowersCallbackSlotsV1
import S1TopPrepareRangesV1
set_option autoImplicit false
namespace AspisS1PreparedPowersCallbacks
open Aeneas Aeneas.Std Result
open AspisS1TopPrepareCarrier AspisS1TopPowers AspisS1PowersCallbackChain
open AspisR1PowersConcreteMul AspisR1PowersExactProduct

def callbackE (value : Top.E) : CallbackWide :=
  let x := claimE value
  ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,
   ⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩

theorem canonical (value : Top.E)
    (h : AspisR1CurrentPreparedClaim.Concrete.Canonical (claimE value)) :
    Canonical (callbackE value) := h

def one : CallbackWide :=
  AspisR1LoopPowers.toOld AspisR1LoopPowers.field.WideExact.ONE

theorem one_canonical : Canonical one := AspisR1LoopPowers.one_canonical

theorem one_decode : decode one=1 := AspisR1LoopPowers.one_decode

/-- Complete callback prefix INCLUDING the last poststate, at the exact
0..N-1 source index order. -/
def Complete (N : Usize) (x : CallbackWide) : Prop :=
  ∃ values last,
    execute N (one,x) (slots N)=ok (values,(last,x)) ∧
    values.length=N.val ∧ Canonical last ∧ decode last=decode x^N.val ∧
    ∀ j, (hj : j<values.length) →
      Canonical (values[j]'hj) ∧ decode (values[j]'hj)=decode x^j

theorem complete (N : Usize) (x : CallbackWide) (hx : Canonical x) : Complete N x := by
  obtain ⟨values,last,run,len,canonicalLast,decodedLast,cells⟩ :=
    total_exact N (slots N) one x one_canonical hx
  refine ⟨values,last,run,len.trans (slots_length N),canonicalLast,?_,?_⟩
  · simpa only [one_decode,one_mul,slots_length] using decodedLast
  · intro j hj
    simpa only [one_decode,one_mul] using cells j hj

/-- From the SAME complete top preparation success: no independent canonical
seed, powers success or per-callback arithmetic/termination premise. The
original from_fn-to-chain association remains a native/Std boundary. -/
theorem prepared_complete (ops : AspisR1CurrentCaller.Ops) {H : Type}
    (D : VTop_Stages.aspis_core.digest.Digest32 H)
    (pub : VTop_Stages.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : H) (input scratch : Array Top.E 29#usize) (prepared : Top.Prepared)
    (success : AspisS1TopPrepareSource.prepare ops D pub proof hash none input=
      ok (.Ok prepared,scratch)) :
    Complete 29#usize (callbackE prepared.gamma) ∧ Complete 7#usize (callbackE prepared.kappa) := by
  have seeds := AspisS1TopPrepareSource.prepare_gamma_kappa_canonical ops D pub proof hash input scratch prepared success
  exact ⟨complete _ _ (canonical _ seeds.1),complete _ _ (canonical _ seeds.2)⟩

#print axioms complete
#print axioms prepared_complete
#print axioms canonical
#print axioms one_canonical
#print axioms one_decode
end AspisS1PreparedPowersCallbacks
