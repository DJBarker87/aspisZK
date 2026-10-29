import R1Z.PV_RunJoin_QueryHead63
import R1Z.PV_RunJoin_QueryEncoded63
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_QueryTail63
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open PV_RunJoin_QueryScript63 (W)
open PV_RunJoin_ResultPost41

def run (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (cc1 cc2 : host_commitment.Commitment)
    (u : aspis_core.r0.domain.FibreIndex) (folded : Slice W)
    (salts : host_commitment.PrivateSalts) (out : alloc.vec.Vec U8) : Result (alloc.vec.Vec U8) :=
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  do
    let first ← host_commitment.Commitment.opening_salt cc1 u
    let salt1 ← core.option.Option.unwrap first
    let out1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out (Array.to_slice salt1)
    let second ← host_commitment.Commitment.opening_salt cc2 u
    let salt2 ← core.option.Option.unwrap second
    let out2 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out1 (Array.to_slice salt2)
    let encoded ← PV_RunJoin_QueryEncoded63.encode base heap box ops folded u
    let out3 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out2 (alloc.vec.Vec.deref encoded)
    let quarter ← u / 4#usize
    let salt ← host_commitment.PrivateSalts.get salts quarter
    let out4 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out3 (Array.to_slice salt)
    ok out4

theorem factor (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (cc1 cc2 : host_commitment.Commitment)
    (u : aspis_core.r0.domain.FibreIndex) (folded : Slice W)
    (salts : host_commitment.PrivateSalts) (out : alloc.vec.Vec U8) :
    PV_RunJoin_ByteScript63.run
      (@PV_RunJoin_QueryScript63.tail (types base) (selected base heap box ops) cc1 cc2 u folded salts) out=
      run base heap box ops cc1 cc2 u folded salts out := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  simp only [PV_RunJoin_QueryScript63.tail,PV_RunJoin_ByteScript63.run,run,
    PV_RunJoin_QueryEncoded63.encode,PV_RunJoin_QueryWindow63.window,
    aspis_core.r0.domain.FibreIndex.get,PV_RunJoin_QueryHead63.get,
    ProverRwDictionaryDomain.fibreGet,bind_tc_ok,bind_assoc_eq]
  rfl

theorem length (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (cc1 cc2 : host_commitment.Commitment)
    (u : aspis_core.r0.domain.FibreIndex) (bound : u.val<262144) (folded : Slice W)
    (salts : host_commitment.PrivateSalts) (out : alloc.vec.Vec U8) :
    Post (fun next => next.length=out.length+224) (run base heap box ops cc1 cc2 u folded salts out) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  unfold run
  apply PV_RunJoin_ResultPost41.bind
  intro first
  apply PV_RunJoin_ResultPost41.bind
  intro salt1
  apply PV_RunJoin_PostBind63.guarded _ _ _ _ (PV_RunJoin_SliceBound62.append out (Array.to_slice salt1))
  intro out1 h1
  change out1.length=out.length+salt1.val.length at h1
  rw [salt1.property] at h1
  apply PV_RunJoin_ResultPost41.bind
  intro second
  apply PV_RunJoin_ResultPost41.bind
  intro salt2
  apply PV_RunJoin_PostBind63.guarded _ _ _ _ (PV_RunJoin_SliceBound62.append out1 (Array.to_slice salt2))
  intro out2 h2
  change out2.length=out1.length+salt2.val.length at h2
  rw [salt2.property] at h2
  apply PV_RunJoin_PostBind63.guarded _ _ _ _
    (PV_RunJoin_QueryEncoded63.length base heap box ops folded u bound)
  intro encoded he
  apply PV_RunJoin_PostBind63.guarded _ _ _ _
    (PV_RunJoin_SliceBound62.append out2 (alloc.vec.Vec.deref encoded))
  intro out3 h3
  change out3.length=out2.length+encoded.length at h3
  rw [he] at h3
  apply PV_RunJoin_ResultPost41.bind
  intro quarter
  apply PV_RunJoin_ResultPost41.bind
  intro salt
  apply PV_RunJoin_PostBind63.guarded _ _ _ _ (PV_RunJoin_SliceBound62.append out3 (Array.to_slice salt))
  intro out4 h4
  change out4.length=out3.length+salt.val.length at h4
  rw [salt.property] at h4
  change out4.length=out.length+224
  change out1.length=out.length+32 at h1
  change out2.length=out1.length+32 at h2
  change out4.length=out3.length+32 at h4
  omega

#print axioms run
#print axioms factor
#print axioms length
end R1Z.PV_RunJoin_QueryTail63
