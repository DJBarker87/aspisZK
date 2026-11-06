import NKE_Free
import NJU_ResumeObserved
set_option autoImplicit false
noncomputable section
namespace NKE_ResumeCodec
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved
open NKE_Free

def digest (chunks : Slice (Slice U8)) : Codec Event (Array U8 32#usize) := by
 classical
 refine {encode := .digest chunks
         decode := fun event=>match event with
          | .digest x0 reply=>if x0=chunks then some reply else none
          | _=>none
         roundtrip := ?_}
 intro reply
 simp

def headerAny (it : core.slice.iter.Iter U8) : Codec Event (Bool × core.slice.iter.Iter U8) := by
 classical
 refine {encode := .headerAny it
         decode := fun event=>match event with
          | .headerAny x0 reply=>if x0=it then some reply else none
          | _=>none
         roundtrip := ?_}
 intro reply
 simp

def k (reader : verifier.Reader) : Codec Event (core.result.Result (aspis_core.field.QM31) verifier.Error × verifier.Reader) := by
 classical
 refine {encode := .k reader
         decode := fun event=>match event with
          | .k x0 reply=>if x0=reader then some reply else none
          | _=>none
         roundtrip := ?_}
 intro reply
 simp

def e (reader : verifier.Reader) : Codec Event (core.result.Result (aspis_core.field.wide_exact.WideExact) verifier.Error × verifier.Reader) := by
 classical
 refine {encode := .e reader
         decode := fun event=>match event with
          | .e x0 reply=>if x0=reader then some reply else none
          | _=>none
         roundtrip := ?_}
 intro reply
 simp

def semantic (bytes : Slice U8) (cursor : Usize) : Codec Event (core.result.Result (Array aspis_core.field.QM31 10#usize × Usize) verifier.Error) := by
 classical
 refine {encode := .semantic bytes cursor
         decode := fun event=>match event with
          | .semantic x0 x1 reply=>if x0=bytes ∧ x1=cursor then some reply else none
          | _=>none
         roundtrip := ?_}
 intro reply
 simp

def weights (bytes : Slice U8) (cursor : Usize) (before : alloc.vec.Vec aspis_core.field.QM31) : Codec Event (core.result.Result (alloc.vec.Vec aspis_core.field.QM31 × Usize) verifier.Error) := by
 classical
 refine {encode := .weights bytes cursor before
         decode := fun event=>match event with
          | .weights x0 x1 x2 reply=>if x0=bytes ∧ x1=cursor ∧ x2=before then some reply else none
          | _=>none
         roundtrip := ?_}
 intro reply
 simp

def validate (queries : Array U32 22#usize) : Codec Event (core.result.Result (Unit) verifier.Error) := by
 classical
 refine {encode := .validate queries
         decode := fun event=>match event with
          | .validate x0 reply=>if x0=queries then some reply else none
          | _=>none
         roundtrip := ?_}
 intro reply
 simp

def filled (n : Usize) (value : aspis_core.field.QM31) : Codec Event (core.result.Result (alloc.vec.Vec aspis_core.field.QM31) aspis_core.r0.Error) := by
 classical
 refine {encode := .filled n value
         decode := fun event=>match event with
          | .filled x0 x1 reply=>if x0=n ∧ x1=value then some reply else none
          | _=>none
         roundtrip := ?_}
 intro reply
 simp

def raw (n : Usize) (reader : verifier.Reader) : Codec Event (Array U8 n × verifier.Reader) := by
 classical
 refine {encode := .raw n reader
         decode := fun event=>match event with
          | .raw n1 reader1 reply=>if h : n1=n then
              if reader1=reader then some (h ▸ reply) else none
             else none
          | _=>none
         roundtrip := ?_}
 intro reply
 simp

#print axioms digest
#print axioms headerAny
#print axioms k
#print axioms e
#print axioms semantic
#print axioms weights
#print axioms validate
#print axioms filled
#print axioms raw
end NKE_ResumeCodec
