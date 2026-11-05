import NIG_NewDomain
import NGM_FinishDomain
set_option autoImplicit false
namespace NIG_FinishInput
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2

/-- Four raw little-endian bytes, before any field decoder or callee reply. -/
def word (bytes:List U8) (start:Nat):Nat:=
 (bytes[start]?.getD 0#u8).val+256*(bytes[start+1]?.getD 0#u8).val+
 65536*(bytes[start+2]?.getD 0#u8).val+16777216*(bytes[start+3]?.getD 0#u8).val

def Windows (bytes:Slice U8) (n:Nat):Prop:=bytes.val.length=32*n ∧
 ∀ i,n>i→∀ j,j<8→word bytes.val (32*i+4*j)<2147483647

/-- The exact primitive caller obligation at tx2_common's final call. No
computed pair/claim/dot equality or child success is an input field. -/
structure Domain (proof:Slice U8) (v:verifier.View) (p:verifier.Prepared)
 (a:verifier.Accumulator):Prop where
 accumulator:NGM_FinishDomain.AccumulatorDomain a
 s2:p.variant=transport.Variant.S2
 claim:NBO_TailDomain.WideCanonical p.claim
 alpha:∀ i, i<2 → ∀ x,p.alpha.val[i]?=some x→NBO_TailDomain.WideCanonical x
 kappa:NBO_TailDomain.WideCanonical p.kappa
 semantic:∀ q∈p.semantic_alpha.val,NGW_NewInterface.CanonK q
 points:∀ point∈p.z.val,NGW_NewInterface.CanonK point.x ∧ NGW_NewInterface.CanonK point.y
 round0:v.round0.val=(proof.val.drop 7527).take 224
 round1:v.round1.val=(proof.val.drop 7783).take 224
 final:v.final_message.val=(proof.val.drop 8007).take 2048
 round0_words:Windows v.round0 7
 round1_words:Windows v.round1 7
 final_words:Windows v.final_message 64

/-- Constructor primitive domains are supplied by the named caller predicate,
not by assuming the result of NEW or finish succeeds. -/
theorem new_inputs (proof:Slice U8) (v:verifier.View) (p:verifier.Prepared)
 (a:verifier.Accumulator) (h:Domain proof v p a):
 NGW_ConstructorArrays.Holds NGW_NewInterface.CanonK p.semantic_alpha ∧
 NGW_ConstructorArrays.Holds (fun point=>NGW_NewInterface.CanonK point.x ∧ NGW_NewInterface.CanonK point.y) p.z:=
 ⟨h.semantic,h.points⟩
#print axioms new_inputs
end NIG_FinishInput
