import Lean
import NGU_Part000
import ClaimDotConcreteAdapterV1
import S5QRaw.EbyKPushDecodedProductUpdateV1
-- Retargeted LPm_PublicState
set_option autoImplicit false
namespace AspisR1.NGU_LPm_PublicState
open Aeneas Aeneas.Std Result NFN_LPi_FieldValues
abbrev Dot := FIo_Native.fast_pairing.canonical.Dot
abbrev Raw := Array U64 4#usize

def update (s : Dot) (r : Raw) : Dot :=
  ⟨Array.make 4#usize [
    NGU_LPf_DotPushFour.update s.sums.val[0]! r.val[0]!,
    NGU_LPf_DotPushFour.update s.sums.val[1]! r.val[1]!,
    NGU_LPf_DotPushFour.update s.sums.val[2]! r.val[2]!,
    NGU_LPf_DotPushFour.update s.sums.val[3]! r.val[3]!]⟩

def values (r : Raw) : Nat×Nat×Nat×Nat :=
  (r.val[0]!.val,r.val[1]!.val,r.val[2]!.val,r.val[3]!.val)

/-- Strengthen inherited totality to the SAME raw values and SAME four
updated state words. The raw-call observation is derived, never supplied. -/
theorem private_source (s : Dot) (a b : NGU_LPi_RawValues.Q)
    (ha : NGU_LPi_RawValues.Canon a) (hb : NGU_LPi_RawValues.Canon b) :
    ∃ r : Raw, FIo_Native.fast_pairing.canonical.Q.raw a b=ok r ∧
      values r=NGU_LPi_RawValues.spec a b ∧
      FIo_Native.fast_pairing.canonical.Dot.push s a b=ok (update s r) := by
  obtain ⟨s0,s1,s2,s3,shape⟩ := NGU_LPf_ArrayFour.shape s.sums
  obtain ⟨r0,r1,r2,r3,raw,meaning⟩ := NGU_LPi_RawValues.source a b ha hb
  have same : s=⟨Array.make 4#usize [s0,s1,s2,s3]⟩ := by
    cases s
    exact congrArg FIo_Native.fast_pairing.canonical.Dot.mk shape
  subst s
  refine ⟨Array.make 4#usize [r0,r1,r2,r3],raw,meaning,?_⟩
  simpa only [update,Array.make,List.getElem!_cons_zero,List.getElem!_cons_succ] using
    NGU_LPf_DotPushCut.source a b s0 s1 s2 s3 r0 r1 r2 r3 raw

/-- Public push with both actual half-products and complete state updates.
Canonicality and count are the existing public caller domain. -/
theorem source (s : FIo_Native.fast_pairing.EbyKDot) (value : NE) (scalar : NQ)
    (hv : canonE value) (hq : canonQ scalar) (count : s.count.val<4096) :
    ∃ (lo hi : Raw) (out : FIo_Native.fast_pairing.EbyKDot),
      FIo_Native.fast_pairing.EbyKDot.push s value scalar=ok (.Ok (),out) ∧
      values lo=NGU_LPi_RawValues.spec (NGU_LPi_CheckedInputs.q value.c0) (NGU_LPi_CheckedInputs.q scalar) ∧
      values hi=NGU_LPi_RawValues.spec (NGU_LPi_CheckedInputs.q value.c1) (NGU_LPi_CheckedInputs.q scalar) ∧
      out.c0=update s.c0 lo ∧ out.c1=update s.c1 hi ∧ out.count.val=s.count.val+1 := by
  have ca := NGU_LPi_CheckedInputs.canonical value.c0 hv.1
  have cb := NGU_LPi_CheckedInputs.canonical value.c1 hv.2
  have cq := NGU_LPi_CheckedInputs.canonical scalar hq
  obtain ⟨lo,_,lov,left⟩ := private_source s.c0 _ _ ca cq
  obtain ⟨hi,_,hiv,right⟩ := private_source s.c1 _ _ cb cq
  have below : ¬s.count ≥ FIo_Native.fast_pairing.MAX_TERMS := by
    simp only [FIo_Native.fast_pairing.MAX_TERMS]
    scalar_tac
  have i0 : Array.index_usize (Array.make 2#usize
      [NGU_LPi_CheckedInputs.q value.c0,NGU_LPi_CheckedInputs.q value.c1]) 0#usize =
      ok (NGU_LPi_CheckedInputs.q value.c0) := rfl
  have i1 : Array.index_usize (Array.make 2#usize
      [NGU_LPi_CheckedInputs.q value.c0,NGU_LPi_CheckedInputs.q value.c1]) 1#usize =
      ok (NGU_LPi_CheckedInputs.q value.c1) := rfl
  let out : FIo_Native.fast_pairing.EbyKDot :=
    ⟨update s.c0 lo,update s.c1 hi,Usize.wrapping_add s.count 1#usize⟩
  have call : FIo_Native.fast_pairing.EbyKDot.push s value scalar=ok (.Ok (),out) := by
    simp only [FIo_Native.fast_pairing.EbyKDot.push,if_neg below,
      NGU_LPi_CheckedInputs.from_wide,bind_tc_ok,NGU_LPi_CheckedInputs.checked scalar hq,
      core.result.Result.Insts.CoreOpsTry.branch,i0,i1,left,right,lift]
    rfl
  obtain ⟨other,otherCall,otherCount⟩ := NGU_LPi_PublicPush.source s value scalar hv hq count
  have unique : out=other := congrArg Prod.snd (Result.ok.inj (call.symm.trans otherCall))
  exact ⟨lo,hi,out,call,lov,hiv,rfl,rfl,by rw [unique]; exact otherCount⟩

#print axioms private_source
#print axioms source
end AspisR1.NGU_LPm_PublicState

-- Retargeted LPm_RawPort
set_option autoImplicit false
namespace AspisR1.NGU_LPm_RawPort
open Aeneas Aeneas.Std Result NFN_LPi_FieldValues
abbrev State := AspisR1EbyKPushDotBackend.PushState
abbrev Native := FIo_Native.fast_pairing.EbyKDot

def statePort (s : Native) : State := ⟨⟨s.c0.sums⟩,⟨s.c1.sums⟩,s.count⟩

def qPort (x : NQ) : AspisR1CurrentPreparedClaim.aspis_core.field.QM31 :=
  ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩

def ePort (x : NE) : AspisR1CurrentPreparedClaim.Concrete.E := ⟨qPort x.c0,qPort x.c1⟩

/-- The retained cohort uses THIS same raw operation; an unrelated raw
product with the same name is never substituted. -/
theorem raw_eq (a b : FIo_Native.fast_pairing.canonical.Q) :
    AspisR1EbyKPushDecodedProductUpdate.QRaw a b =
      FIo_Native.fast_pairing.canonical.Q.raw a b := by
  change AspisR1CanonicalQRawUnified.canonical.Q.raw a b = _
  exact (NGU_LPi_RawAssociation.source_eq a b).symm

theorem state_fields (s : Native) :
    (statePort s).c0.sums=s.c0.sums ∧ (statePort s).c1.sums=s.c1.sums ∧
      (statePort s).count=s.count := ⟨rfl,rfl,rfl⟩

#print axioms raw_eq
#print axioms state_fields
#check AspisR1EbyKPushDecodedProductUpdate.successful_push_decoded_product_update
#check AspisR1FinishDotSourceABI.finishFromPush_total
#print AspisR1DotPushLocal.Proof.updatedSums
#print AspisR1EbyKPushDecodedProductUpdate.castSums
#print AspisR1EbyKPushDecodedProductUpdate.tupleAdd
end AspisR1.NGU_LPm_RawPort

-- Retargeted LPm_UpdatePort
set_option autoImplicit false
namespace AspisR1.NGU_LPm_UpdatePort
open Aeneas Aeneas.Std Result
#print AspisR1DotPushLocal.Proof.updateWord
#print AspisR1EbyKPushDotBackend.dotViaRaw

def dotPort (s : NGU_LPm_PublicState.Dot) : AspisR1EbyKPushDotBackend.PushDot := ⟨s.sums⟩

theorem word (s r : U64) :
    NGU_LPf_DotPushFour.update s r = AspisR1DotPushLocal.Proof.updateWord s r := by
  rfl

theorem sums (s : NGU_LPm_PublicState.Dot) (r : NGU_LPm_PublicState.Raw) :
    (dotPort (NGU_LPm_PublicState.update s r)).sums =
      AspisR1DotPushLocal.Proof.updatedSums (dotPort s).sums r := by
  obtain ⟨s0,s1,s2,s3,ss⟩ := NGU_LPf_ArrayFour.shape s.sums
  obtain ⟨r0,r1,r2,r3,rr⟩ := NGU_LPf_ArrayFour.shape r
  simp only [dotPort,NGU_LPm_PublicState.update,AspisR1DotPushLocal.Proof.updatedSums,
    ss,rr,Array.make,List.getElem!_cons_zero,List.getElem!_cons_succ,word]
  rfl

open Lean Elab Command in
run_elab do
  let env ← getEnv
  for entry in env.constants.toList do
    let dn := entry.1
    if "AspisR1DotPushLocal.Proof".isPrefixOf dn.toString then logInfo m!"{dn}"
#print AspisR1DotPushLocal.canonical.Dot.push
#print axioms word
#print axioms sums
end AspisR1.NGU_LPm_UpdatePort

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
