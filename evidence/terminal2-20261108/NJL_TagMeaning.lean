import NJL_TagChunks
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_TagMeaning
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (decode K)
open ExtractedMaskQM31Exact (M31Exact)
open NJL_TagRawTrace (Selectors dot)
def encode (w : Fin 4 → M31Exact) : K := ⟨⟨w 0,w 1⟩,⟨w 2,w 3⟩⟩
theorem encode_add (x y : Fin 4 → M31Exact) : encode (fun i=>x i+y i)=encode x+encode y := rfl
theorem encode_zero : encode (fun _=>0)=0 := rfl
theorem encode_decode (q : NQ) : encode (fun i=>(NJB_Words.word q i).val)=decode q := rfl
/-- Scalar tag products agree with multiplication by the SAME natural tag
in the retained exact field; this uses no concrete recurrence reduction. -/
theorem scalar (q : NQ) (n : Nat) :
 encode (fun i=>((NJB_Words.word q i).val*n : Nat))=decode q*(n : K) := by
 apply QuadraticAlgebra.ext <;> apply QuadraticAlgebra.ext <;>
  simp [encode,decode,ExtractedMaskQM31Exact.decode,FIv_NativeArithmetic.qm,
   FIv_NativeArithmetic.cm,NJB_Words.word]
def model (s : Selectors) (xs : List (Fin 272)) : K :=
 (xs.map (fun t=>decode (NJB_ActiveReference.high s (NJL_TagData.block t))*(NJL_TagData.tag t).val)).sum
/-- Symbolic natural-word sum to exact-field weighted sum. The registry is
shared by native scalar observations and the model, not supplied as a premise. -/
theorem value (s : Selectors) (xs : List (Fin 272)) :
 encode (fun i=>(dot s xs i : M31Exact))=model s xs := by
 induction xs with
 | nil => exact encode_zero
 | cons t ts ih =>
  have same : (fun i=>(dot s (t::ts) i : M31Exact))=
   (fun i=>((NJL_TagWords.highWord s t i).val*(NJL_TagWords.tagWord t).val : Nat)+ (dot s ts i : M31Exact)) := by
   funext i;simp only [dot,List.map_cons,List.sum_cons,Nat.cast_add]
  rw [same,encode_add,ih]
  have castProduct : encode (fun i=>((NJL_TagWords.highWord s t i).val*(NJL_TagWords.tagWord t).val : Nat))=
   decode (NJB_ActiveReference.high s (NJL_TagData.block t))*(NJL_TagData.tag t).val := by
   simp only [NJL_TagWords.highWord,NJL_TagWords.tagWord,NJL_TagWords.cast64]
   exact scalar _ _
  rw [castProduct]
  rfl
theorem residue (n : Nat) : ((n%2147483647 : Nat) : M31Exact)=(n : M31Exact) := by simp
#print axioms encode_add
#print axioms encode_zero
#print axioms encode_decode
#print scalar
#print axioms scalar
#print value
#print axioms value
#print axioms residue
end AspisR1.NJL_TagMeaning
end
