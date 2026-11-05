import NIW_AlignAllocatorPhase
import NIW_AlignPowersReply
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignPairPhase
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl

structure Input where
 owner : Ref W
 alpha : Ref (Array E 2#usize)
 message : Ref (Slice U8)
 kappa : E
 ap0Address : Nat
 ap1Address : Nat
 commonAddress : Nat
 lowAddress : Nat
 scratchAddress : Nat
 partsAddress : Nat

def context (i : Input) (ap0 ap1 : Powers) : Context :=
 ⟨i.owner,i.alpha,i.message,⟨i.ap0Address,ap0⟩,⟨i.ap1Address,ap1⟩,i.kappa,
  i.commonAddress,i.lowAddress,i.scratchAddress,i.partsAddress⟩

structure Log where
 powers0 : Result Powers
 powers1 : Option (Result Powers)
 allocator : Option NIW_AlignAllocatorPhase.Log

def run (r : NP6_StdModel.Reservation) (i : Input) : Result NR × Log :=
 let powers0 := FIo_Native.weights.powers 4#usize (epick i.alpha.value 0)
 match powers0 with
 | fail err => (fail err,⟨powers0,none,none⟩)
 | div => (div,⟨powers0,none,none⟩)
 | ok ap0 =>
  let powers1 := FIo_Native.weights.powers 4#usize (epick i.alpha.value 1)
  match powers1 with
  | fail err => (fail err,⟨powers0,some powers1,none⟩)
  | div => (div,⟨powers0,some powers1,none⟩)
  | ok ap1 =>
   let parent := NIW_AlignAllocatorPhase.run r (context i ap0 ap1)
   (parent.1,⟨powers0,some powers1,some parent.2⟩)

/-- The actual two source-returned powers index the complete parent witness.
This relation is a conclusion to produce, never a root hypothesis. -/
def Certificate (r : NP6_StdModel.Reservation) (i : Input) (observed : Result NR × Log) : Prop :=
 match observed.2.powers0,observed.2.powers1 with
 | ok ap0,some (ok ap1) =>
  FIo_Native.weights.powers 4#usize (epick i.alpha.value 0)=ok ap0 ∧
  FIo_Native.weights.powers 4#usize (epick i.alpha.value 1)=ok ap1 ∧
  canonical ap0 ∧ canonical ap1 ∧ NIT_AllocatorChain.Trace (context i ap0 ap1) r observed.1
 | _,_ => False

theorem certificate (r : NP6_StdModel.Reservation) (i : Input)
 (domain : NIT_PairDomain.Domain i.owner.value i.alpha.value i.message.value i.kappa) :
 Certificate r i (run r i) := by
 have p0 := NIW_AlignPowersReply.source 4#usize (epick i.alpha.value 0)
  (NIT_PairComposition.epick_canonical i.alpha.value domain.alphas 0)
 have p1 := NIW_AlignPowersReply.source 4#usize (epick i.alpha.value 1)
  (NIT_PairComposition.epick_canonical i.alpha.value domain.alphas 1)
 cases call0 : FIo_Native.weights.powers 4#usize (epick i.alpha.value 0) with
 | fail err => simp only [call0,NIW_AlignFieldReply.Produced] at p0
 | div => simp only [call0,NIW_AlignFieldReply.Produced] at p0
 | ok ap0 =>
  simp only [call0,NIW_AlignFieldReply.Produced] at p0
  cases call1 : FIo_Native.weights.powers 4#usize (epick i.alpha.value 1) with
  | fail err => simp only [call1,NIW_AlignFieldReply.Produced] at p1
  | div => simp only [call1,NIW_AlignFieldReply.Produced] at p1
  | ok ap1 =>
   simp only [call1,NIW_AlignFieldReply.Produced] at p1
   simp only [run,call0,call1,Certificate]
   exact ⟨call0,call1,p0,p1,NIW_AlignAllocatorPhase.trace r (context i ap0 ap1) domain p0 p1⟩

#print axioms certificate
end AspisR1.NIW_AlignPairPhase
