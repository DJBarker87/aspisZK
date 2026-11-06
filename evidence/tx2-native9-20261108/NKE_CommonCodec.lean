import NKE_Free
import NJU_CommonObserved
set_option autoImplicit false
noncomputable section
namespace NKE_CommonCodec
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NJU_CommonObserved
open NKE_Free

def resume (ck : Slice U8) (proof : Slice U8) (pub : Slice U8) : Codec Event (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) := by
 classical
 refine {encode := .resume ck proof pub
         decode := fun event=>match event with
          | .resume x0 x1 x2 reply=>if x0=ck ∧ x1=proof ∧ x2=pub then some reply else none
          | _=>none
         roundtrip := ?_}
 intro reply
 simp

def powers (gamma : aspis_core.field.wide_exact.WideExact) : Codec Event (Array aspis_core.field.wide_exact.WideExact 29#usize) := by
 classical
 refine {encode := .powers gamma
         decode := fun event=>match event with
          | .powers x0 reply=>if x0=gamma then some reply else none
          | _=>none
         roundtrip := ?_}
 intro reply
 simp

def inactive (bytes : Slice U8) : Codec Event (Option aspis_core.field.wide_exact.WideExact) := by
 classical
 refine {encode := .inactive bytes
         decode := fun event=>match event with
          | .inactive x0 reply=>if x0=bytes then some reply else none
          | _=>none
         roundtrip := ?_}
 intro reply
 simp

def merkle (proof : Slice U8) (p : verifier.Prepared) (root : Array U8 32#usize) : Codec Event (core.result.Result (Unit) verifier.Error) := by
 classical
 refine {encode := .merkle proof p root
         decode := fun event=>match event with
          | .merkle x0 x1 x2 reply=>if x0=proof ∧ x1=p ∧ x2=root then some reply else none
          | _=>none
         roundtrip := ?_}
 intro reply
 simp

def geometry (queries : Array U32 22#usize) (next : Usize) : Codec Event (core.result.Result (verifier.QueryGeometry) verifier.Error) := by
 classical
 refine {encode := .geometry queries next
         decode := fun event=>match event with
          | .geometry x0 x1 reply=>if x0=queries ∧ x1=next then some reply else none
          | _=>none
         roundtrip := ?_}
 intro reply
 simp

def pending (weights : Slice aspis_core.field.QM31) : Codec Event (core.result.Result (verifier.BatchedWeights) verifier.Error) := by
 classical
 refine {encode := .pending weights
         decode := fun event=>match event with
          | .pending x0 reply=>if x0=weights then some reply else none
          | _=>none
         roundtrip := ?_}
 intro reply
 simp

def query (proof : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator) (g : Array aspis_core.field.wide_exact.WideExact 29#usize) (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights) : Codec Event (core.result.Result (verifier.Accumulator × verifier.BatchedWeights) verifier.Error) := by
 classical
 refine {encode := .query proof p a g geometry pending
         decode := fun event=>match event with
          | .query x0 x1 x2 x3 x4 x5 reply=>if x0=proof ∧ x1=p ∧ x2=a ∧ x3=g ∧ x4=geometry ∧ x5=pending then some reply else none
          | _=>none
         roundtrip := ?_}
 intro reply
 simp

def flush (pending : verifier.BatchedWeights) (weights : Slice aspis_core.field.QM31) : Codec Event (Slice aspis_core.field.QM31) := by
 classical
 refine {encode := .flush pending weights
         decode := fun event=>match event with
          | .flush x0 x1 reply=>if x0=pending ∧ x1=weights then some reply else none
          | _=>none
         roundtrip := ?_}
 intro reply
 simp

def finish (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator) : Codec Event (core.result.Result (Unit) verifier.Error) := by
 classical
 refine {encode := .finish v p a
         decode := fun event=>match event with
          | .finish x0 x1 x2 reply=>if x0=v ∧ x1=p ∧ x2=a then some reply else none
          | _=>none
         roundtrip := ?_}
 intro reply
 simp

#print axioms resume
#print axioms powers
#print axioms inactive
#print axioms merkle
#print axioms geometry
#print axioms pending
#print axioms query
#print axioms flush
#print axioms finish
end NKE_CommonCodec
