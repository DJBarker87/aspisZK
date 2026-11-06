import NJP_PermutationPacket
import NJE_CompressSeed

set_option autoImplicit false
noncomputable section
namespace NJP_CompressionPacket
open Aeneas Aeneas.Std Result
abbrev State := NJE_RoundTrace.State
abbrev Digest := Fin 8 → U32

def model (left right : Digest) : Digest := fun i => NJP_FieldEncoding.word
 (R0P.nodeCompress (fun j => ((left j).val:NJA_Matrix.K)) (fun j => ((right j).val:NJA_Matrix.K)) i)

/-- K010/K011/K012 transcribes one SAME seeded-state permutation call and the
same first-eight reply limbs. Native reply is arbitrary in the harness; the
root installs the CLOSED-candidate permutation model, under (y)/(aq)(5).
No successful child-result or free dictionary clause is retained. -/
structure CallerCut (left right : Digest) (seeded reply : State) (out : Digest)
    (calls : Nat) : Prop where
 seed : seeded=NJE_CompressSeed.seed left right
 call_count : calls=1
 output : ∀ i, out i=reply ⟨i.val,by omega⟩

theorem TX1_305 (left right : Digest)
    (hl : ∀ i, (left i).val<2147483647) (hr : ∀ i, (right i).val<2147483647)
    (seeded : State) (out : Digest) (calls : Nat)
    (cut : CallerCut left right seeded (NJP_PermutationPacket.model seeded) out calls) :
    out=model left right ∧ calls=1 ∧
    (ok out : Result Digest)=ok (model left right) := by
 have seed_value := (NJE_CompressSeed.value left right hl hr).2
 have same : out=model left right := by
   funext i
   rw [cut.output i,cut.seed]
   have argument := seed_value.trans (NJA_Compress.seed_model _ _)
   have encoded := congrArg (fun s : Fin 16 → NJA_Matrix.K =>
     NJP_FieldEncoding.word (R0P.poseidonPermutation s ⟨i.val,by omega⟩)) argument
   simpa only [NJP_PermutationPacket.model,model,R0P.nodeCompress,R0P.digestOf] using encoded
 exact ⟨same,cut.call_count,congrArg (fun x => (ok x : Result Digest)) same⟩

theorem child_domain (left right : Digest)
    (hl : ∀ i, (left i).val<2147483647) (hr : ∀ i, (right i).val<2147483647) :
    NJE_RoundTrace.Canonical (NJE_CompressSeed.seed left right) :=
 (NJE_CompressSeed.value left right hl hr).1

#print TX1_305
#print axioms TX1_305
#print child_domain
#print axioms child_domain
end NJP_CompressionPacket
end
