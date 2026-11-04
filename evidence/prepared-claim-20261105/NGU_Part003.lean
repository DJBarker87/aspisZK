import Lean
import NGU_Part001
import NGU_Part002
import NGU_Part000
import CurrentClaimScalarBody
-- Retargeted LPm_DotPort
set_option autoImplicit false
namespace AspisR1.NGU_LPm_DotPort
open Aeneas Aeneas.Std Result
open NGU_LPm_RawPort NGU_LPm_UpdatePort

theorem private_call (s : NGU_LPm_PublicState.Dot)
    (a b : FIo_Native.fast_pairing.canonical.Q) (raw : NGU_LPm_PublicState.Raw)
    (call : FIo_Native.fast_pairing.canonical.Q.raw a b=ok raw) :
    AspisR1EbyKPushDotBackend.dotViaRaw AspisR1EbyKPushDecodedProductUpdate.QRaw
      (dotPort s) a b=ok (dotPort (NGU_LPm_PublicState.update s raw)) := by
  have modelRaw : AspisR1EbyKPushDecodedProductUpdate.QRaw a b=ok raw := by
    rw [raw_eq]
    exact call
  have model := AspisR1DotPushLocal.Proof.push_total_from_raw
    AspisR1EbyKPushDecodedProductUpdate.QRaw ⟨s.sums⟩ a b raw modelRaw
  simp only [AspisR1EbyKPushDotBackend.dotViaRaw,dotPort,model,bind_tc_ok]
  have hsum : (NGU_LPm_PublicState.update s raw).sums =
      AspisR1DotPushLocal.Proof.updatedSums s.sums raw := sums s raw
  rw [hsum]

#print axioms private_call
#check AspisR1S5EbyKPushTotalityV1.push_success_of_valid_scalar
end AspisR1.NGU_LPm_DotPort

-- Retargeted LPm_PublicPort
set_option autoImplicit false
namespace AspisR1.NGU_LPm_PublicPort
open Aeneas Aeneas.Std Result NFN_LPi_FieldValues NGU_LPm_RawPort NGU_LPm_UpdatePort

 theorem raw_values_injective (x y : NGU_LPm_PublicState.Raw)
    (same : NGU_LPm_PublicState.values x=NGU_LPm_PublicState.values y) : x=y := by
  obtain ⟨a,b,c,d,hx⟩ := NGU_LPf_ArrayFour.shape x
  obtain ⟨e,f,g,h,hy⟩ := NGU_LPf_ArrayFour.shape y
  subst x; subst y
  simp only [NGU_LPm_PublicState.values,Array.make,List.getElem!_cons_zero,
    List.getElem!_cons_succ,Prod.mk.injEq] at same
  rcases same with ⟨ha,hb,hc,hd⟩
  simp only [UScalar.eq_of_val_eq ha,UScalar.eq_of_val_eq hb,
    UScalar.eq_of_val_eq hc,UScalar.eq_of_val_eq hd]

theorem raw_meaning (a b : NGU_LPi_RawValues.Q) (ha : NGU_LPi_RawValues.Canon a)
    (hb : NGU_LPi_RawValues.Canon b) (r : NGU_LPm_PublicState.Raw)
    (call : FIo_Native.fast_pairing.canonical.Q.raw a b=ok r) :
    NGU_LPm_PublicState.values r=NGU_LPi_RawValues.spec a b := by
  obtain ⟨r0,r1,r2,r3,actual,meaning⟩ := NGU_LPi_RawValues.source a b ha hb
  have unique := Result.ok.inj (call.symm.trans actual)
  rw [unique]
  exact meaning

theorem state_ext (x y : State) (lo : x.c0.sums=y.c0.sums)
    (hi : x.c1.sums=y.c1.sums) (count : x.count=y.count) : x=y := by
  rcases x with ⟨⟨a⟩,⟨b⟩,c⟩
  rcases y with ⟨⟨d⟩,⟨e⟩,f⟩
  simp_all only

/-- The concrete native public step and the retained concrete cohort step
return the SAME complete eight-word state. All call/value observations are
derived from their total source theorems, not supplied as whole step equality. -/
theorem source (s : Native) (v : NE) (q : NQ)
    (hv : canonE v) (hq : canonQ q) (count : s.count.val<4096) :
    ∃ out, FIo_Native.fast_pairing.EbyKDot.push s v q=ok (.Ok (),out) ∧
      AspisR1EbyKPushDotBackend.pushWithDotBackend AspisR1EbyKPushDecodedProductUpdate.QRaw
        (statePort s) (AspisR1S5ClaimDotConcreteAdapter.toPushWide (ePort v))
        (AspisR1S5ClaimDotConcreteAdapter.toPushQm (qPort q))=ok (.Ok (),statePort out) := by
  let vm := AspisR1S5ClaimDotConcreteAdapter.toPushWide (ePort v)
  let qm := AspisR1S5ClaimDotConcreteAdapter.toPushQm (qPort q)
  have cv : AspisR1EbyKPowerValueCanonicalToPush.pushCanonical vm := hv
  have cc : (statePort s).count < AspisR1EbyKPushExplicitOpsV1.maxTerms := by
    simp only [statePort,AspisR1EbyKPushExplicitOpsV1.maxTerms]
    scalar_tac
  have cq : ∀ x ∈ (AspisR1EbyKPushDotBackend.scalarQ qm).val,x.val<2147483647 := by
    intro x hx
    simp only [qm,AspisR1EbyKPushDotBackend.scalarQ,
      AspisR1S5ClaimDotConcreteAdapter.toPushQm,qPort,Array.make,
      List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl
    · exact hq.1.1
    · exact hq.1.2
    · exact hq.2.1
    · exact hq.2.2
  obtain ⟨lo,hi,out,ncall,lv,hv0,h0,h1,inc⟩ := NGU_LPm_PublicState.source s v q hv hq count
  obtain ⟨model,mcall⟩ := AspisR1S5EbyKPushTotalityV1.push_success_of_valid_scalar
    (statePort s) vm qm cv cc cq
  obtain ⟨ml,mr,mlcall,mrcall,mlsum,mrsum,_,minc,_⟩ :=
    AspisR1EbyKPushDotBackend.successful_push_exact_backend
      AspisR1EbyKPushDecodedProductUpdate.QRaw (statePort s) vm qm model mcall
  change AspisR1EbyKPushDecodedProductUpdate.QRaw (NGU_LPi_CheckedInputs.q v.c0)
    (NGU_LPi_CheckedInputs.q q)=ok ml at mlcall
  change AspisR1EbyKPushDecodedProductUpdate.QRaw (NGU_LPi_CheckedInputs.q v.c1)
    (NGU_LPi_CheckedInputs.q q)=ok mr at mrcall
  rw [raw_eq] at mlcall mrcall
  have mlval := raw_meaning _ _ (NGU_LPi_CheckedInputs.canonical v.c0 hv.1)
    (NGU_LPi_CheckedInputs.canonical q hq) ml mlcall
  have mrval := raw_meaning _ _ (NGU_LPi_CheckedInputs.canonical v.c1 hv.2)
    (NGU_LPi_CheckedInputs.canonical q hq) mr mrcall
  have mleq := raw_values_injective ml lo (mlval.trans lv.symm)
  have mreq := raw_values_injective mr hi (mrval.trans hv0.symm)
  subst ml; subst mr
  have loeq : model.c0.sums=(statePort out).c0.sums := by
    change model.c0.sums=out.c0.sums
    rw [mlsum,h0]
    exact (sums s.c0 lo).symm
  have hieq : model.c1.sums=(statePort out).c1.sums := by
    change model.c1.sums=out.c1.sums
    rw [mrsum,h1]
    exact (sums s.c1 hi).symm
  have ceq : model.count=(statePort out).count := UScalar.eq_of_val_eq (minc.trans inc.symm)
  have same := state_ext model (statePort out) loeq hieq ceq
  rw [same] at mcall
  exact ⟨out,ncall,mcall⟩

#print axioms raw_values_injective
#print axioms raw_meaning
#print axioms state_ext
#print axioms source
end AspisR1.NGU_LPm_PublicPort

-- Retargeted LPm_FinishPort
set_option autoImplicit false
namespace AspisR1.NGU_LPm_FinishPort
open Aeneas Aeneas.Std Result NFN_LPi_FieldValues NGU_LPm_RawPort
abbrev E := AspisR1CurrentPreparedClaim.Concrete.E

def words (x : E) : List U32 :=
  [x.c0.c0.a,x.c0.c0.b,x.c0.c1.a,x.c0.c1.b,
   x.c1.c0.a,x.c1.c0.b,x.c1.c1.a,x.c1.c1.b]

theorem words_injective (x y : E) (same : words x=words y) : x=y := by
  rcases x with ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,⟨⟨e,f⟩,⟨g,h⟩⟩⟩
  rcases y with ⟨⟨⟨i,j⟩,⟨k,l⟩⟩,⟨⟨m,n⟩,⟨o,p⟩⟩⟩
  simp only [words,List.cons.injEq,and_true] at same
  rcases same with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  rfl

theorem from_finish_words (x : AspisR1CurrentPreparedClaim.ClaimParser.FinishE) :
    words (AspisR1CurrentPreparedClaim.ClaimParser.fromFinish x)=
      AspisR1FinishDotSourceABI.finishWords x := rfl

#print AspisR1EbyKFinish.Proof.word

theorem word_eq (r : U64) (v : U32) (value : v.val=r.val%2147483647) :
    v=AspisR1EbyKFinish.Proof.word r := by
  apply UScalar.eq_of_val_eq
  rw [value]
  rfl

/-- Complete native finalizer return equals the retained concrete cohort
finalizer after the explicit eight-word owner port. -/
theorem source (s : Native) : ∃ out,
    FIo_Native.fast_pairing.EbyKDot.finish s=ok out ∧
    (AspisR1S5ClaimDotConcreteAdapter.concreteOps AspisR1EbyKPushDecodedProductUpdate.QRaw).finishDot
      (statePort s)=ok (ePort out) := by
  obtain ⟨out,native,h0,h1,h2,h3,h4,h5,h6,h7⟩ := NGU_LPf_PublicDotAllStates.source s
  obtain ⟨finish,call,_,layout⟩ := AspisR1FinishDotSourceABI.finishFromPush_total (statePort s)
  have w0 := word_eq _ _ h0
  have w1 := word_eq _ _ h1
  have w2 := word_eq _ _ h2
  have w3 := word_eq _ _ h3
  have w4 := word_eq _ _ h4
  have w5 := word_eq _ _ h5
  have w6 := word_eq _ _ h6
  have w7 := word_eq _ _ h7
  have same : AspisR1CurrentPreparedClaim.ClaimParser.fromFinish finish=ePort out := by
    apply words_injective
    rw [from_finish_words,layout]
    obtain ⟨a,b,c,d,left⟩ := NGU_LPf_ArrayFour.shape s.c0.sums
    obtain ⟨e,f,g,h,right⟩ := NGU_LPf_ArrayFour.shape s.c1.sums
    simp only [statePort,left,right,Array.make,List.cons_append,List.nil_append,
      List.map_cons,List.map_nil,words,ePort,qPort,w0,w1,w2,w3,w4,w5,w6,w7]
    rfl
  refine ⟨out,native,?_⟩
  change (do let finish ← AspisR1FinishDotSourceABI.finishFromPush (statePort s)
             ok (AspisR1CurrentPreparedClaim.ClaimParser.fromFinish finish))=ok (ePort out)
  rw [call,bind_tc_ok,same]

#print axioms words_injective
#print axioms from_finish_words
#print axioms word_eq
#print axioms source
end AspisR1.NGU_LPm_FinishPort

-- Retargeted LPf_DotResidueStep
set_option autoImplicit false
namespace AspisR1.NGU_LPf_DotResidueStep
open Aeneas Aeneas.Std

theorem source (sum raw : U64) (n : Nat) (hn : n < 4096)
    (hs : sum.val ≤ n*NGU_LPf_DotWordStep.bound) :
    (NGU_LPf_DotPushFour.update sum raw).val % 2147483647 =
      (sum.val + raw.val) % 2147483647 := by
  unfold NGU_LPf_DotPushFour.update
  rw [(NGU_LPf_DotWordStep.value sum raw n hn hs).1,NFN_LPf_ReductionWord.fold_value]
  rw [Nat.add_mod,LPe_MersenneReduction.fold_mod]
  exact (Nat.add_mod sum.val raw.val 2147483647).symm

#print axioms source
end AspisR1.NGU_LPf_DotResidueStep

-- Retargeted LPm_WordFold
set_option autoImplicit false
namespace AspisR1.NGU_LPm_WordFold
open Aeneas Aeneas.Std
abbrev bound := NGU_LPf_DotWordStep.bound

def run (sum : U64) : List U64 → U64
  | [] => sum
  | raw::xs => run (NGU_LPf_DotPushFour.update sum raw) xs

/-- Every reached count supplies the next native step's no-wrap invariant.
All raw representatives are included; no multiplication is evaluated here. -/
theorem bounded (xs : List U64) (sum : U64) (n : Nat)
    (fits : n+xs.length ≤ 4096) (hs : sum.val ≤ n*bound) :
    (run sum xs).val ≤ (n+xs.length)*bound := by
  induction xs generalizing sum n with
  | nil => simpa only [run,List.length_nil,Nat.add_zero] using hs
  | cons raw xs ih =>
    have hn : n<4096 := by simp only [List.length_cons] at fits; omega
    have update := (NGU_LPf_DotWordStep.value sum raw n hn hs).2
    have tail := ih (NGU_LPf_DotPushFour.update sum raw) (n+1)
      (by simp only [List.length_cons] at fits; omega) update
    simpa only [run,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using tail

/-- Product-sum value invariant for an arbitrary source-shaped prefix, on
EVERY raw u64 sequence fitting the public count cap. -/
theorem residues (xs : List U64) (sum : U64) (n : Nat)
    (fits : n+xs.length ≤ 4096) (hs : sum.val ≤ n*bound) :
    (run sum xs).val%2147483647 =
      (sum.val+(xs.map UScalar.val).sum)%2147483647 := by
  induction xs generalizing sum n with
  | nil => simp only [run,List.map_nil,List.sum_nil,Nat.add_zero]
  | cons raw xs ih =>
    have hn : n<4096 := by simp only [List.length_cons] at fits; omega
    have update := (NGU_LPf_DotWordStep.value sum raw n hn hs).2
    have tail := ih (NGU_LPf_DotPushFour.update sum raw) (n+1)
      (by simp only [List.length_cons] at fits; omega) update
    rw [run,tail]
    rw [Nat.add_mod,NGU_LPf_DotResidueStep.source sum raw n hn hs,←Nat.add_mod]
    simp only [List.map_cons,List.sum_cons,Nat.add_assoc]

theorem twenty_nine (xs : List U64) (size : xs.length=29) :
    (run 0#u64 xs).val ≤ 29*bound ∧
    (run 0#u64 xs).val%2147483647 = (xs.map UScalar.val).sum%2147483647 := by
  constructor
  · simpa only [size,Nat.zero_add] using bounded xs 0#u64 0 (by omega) (by decide)
  · simpa only [show (0#u64).val=0 from rfl,Nat.zero_add] using
      residues xs 0#u64 0 (by omega) (by decide)

#print axioms bounded
#print axioms residues
#print axioms twenty_nine
end AspisR1.NGU_LPm_WordFold

-- Retargeted LPm_PublicFold
set_option autoImplicit false
namespace AspisR1.NGU_LPm_PublicFold
open Aeneas Aeneas.Std Result NFN_LPi_FieldValues NGU_LPm_RawPort
abbrev B := NGU_LPf_DotWordStep.bound
abbrev M := AspisR1EbyKPushDecodedProductUpdate.M
abbrev Quad := M×M×M×M
abbrev Eight := Quad×Quad

def Bounded (s : Native) (n : Nat) : Prop := s.count.val=n ∧
  (∀ x∈s.c0.sums.val,x.val≤n*B) ∧ (∀ x∈s.c1.sums.val,x.val≤n*B)

def meaning (s : Native) : Eight :=
  (AspisR1EbyKPushDecodedProductUpdate.castSums s.c0.sums,
   AspisR1EbyKPushDecodedProductUpdate.castSums s.c1.sums)

def plus (a b : Eight) : Eight :=
  (AspisR1EbyKPushDecodedProductUpdate.tupleAdd a.1 b.1,
   AspisR1EbyKPushDecodedProductUpdate.tupleAdd a.2 b.2)

def contribution (v : NE) (q : NQ) : Eight :=
  let x := AspisR1S5ClaimDotConcreteAdapter.toPushWide (ePort v)
  let y := AspisR1S5ClaimDotConcreteAdapter.toPushQm (qPort q)
  let scalar := (((y.c0.a.val : M),(y.c0.b.val : M)),(y.c1.a.val : M),(y.c1.b.val : M))
  (R22RawQmProductResidues.qmulCoefficients
    (((x.c0.c0.a.val : M),(x.c0.c0.b.val : M)),(x.c0.c1.a.val : M),(x.c0.c1.b.val : M)) scalar,
   R22RawQmProductResidues.qmulCoefficients
    (((x.c1.c0.a.val : M),(x.c1.c0.b.val : M)),(x.c1.c1.a.val : M),(x.c1.c1.b.val : M)) scalar)

def fold (initial : Eight) : List (NE×NQ) → Eight
  | [] => initial
  | (v,q)::xs => fold (plus initial (contribution v q)) xs

theorem dot_bound (s : NGU_LPm_PublicState.Dot) (r : NGU_LPm_PublicState.Raw) (n : Nat)
    (hn : n<4096) (hs : ∀ x∈s.sums.val,x.val≤n*B) :
    ∀ x∈(NGU_LPm_PublicState.update s r).sums.val,x.val≤(n+1)*B := by
  obtain ⟨a,b,c,d,shape⟩ := NGU_LPf_ArrayFour.shape s.sums
  obtain ⟨e,f,g,h,raw⟩ := NGU_LPf_ArrayFour.shape r
  intro x hx
  simp only [NGU_LPm_PublicState.update,shape,raw,Array.make,List.getElem!_cons_zero,
    List.getElem!_cons_succ,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl
  all_goals
    apply (NGU_LPf_DotWordStep.value _ _ n hn _).2
    apply hs
    simp only [shape,Array.make,List.mem_cons,List.not_mem_nil,or_false]
    tauto

theorem below46 (x : U64) (n : Nat) (hn : n≤4096) (hx : x.val≤n*B) : x.val<2^46 := by
  norm_num only [Nat.reducePow]
  dsimp only [B,NGU_LPf_DotWordStep.bound] at hx
  omega

/-- Full native/cohort step and decoded FIELD product-sum update. The imported
R22 theorem supplies the multiplication interpretation; it is not re-proved. -/
theorem step (s : Native) (v : NE) (q : NQ) (n : Nat) (hn : n<29)
    (hs : Bounded s n) (hv : canonE v) (hq : canonQ q) :
    ∃ out, FIo_Native.fast_pairing.EbyKDot.push s v q=ok (.Ok (),out) ∧
      Bounded out (n+1) ∧ meaning out=plus (meaning s) (contribution v q) := by
  have count : s.count.val<4096 := by rw [hs.1]; omega
  obtain ⟨out,native,model⟩ := NGU_LPm_PublicPort.source s v q hv hq count
  obtain ⟨lo,hi,other,otherCall,_,_,h0,h1,inc⟩ := NGU_LPm_PublicState.source s v q hv hq count
  have same : out=other := congrArg Prod.snd (Result.ok.inj (native.symm.trans otherCall))
  subst other
  have bounds : Bounded out (n+1) := by
    refine ⟨by rw [inc,hs.1],?_,?_⟩
    · rw [h0]; exact dot_bound s.c0 lo n (by omega) hs.2.1
    · rw [h1]; exact dot_bound s.c1 hi n (by omega) hs.2.2
  have cv : AspisR1EbyKPowerValueCanonicalToPush.pushCanonical
      (AspisR1S5ClaimDotConcreteAdapter.toPushWide (ePort v)) := hv
  have acc0 : ∀ x∈(statePort s).c0.sums.val,x.val<2^46 := by
    intro x hx; exact below46 x n (by omega) (hs.2.1 x hx)
  have acc1 : ∀ x∈(statePort s).c1.sums.val,x.val<2^46 := by
    intro x hx; exact below46 x n (by omega) (hs.2.2 x hx)
  have values := AspisR1EbyKPushDecodedProductUpdate.successful_push_decoded_product_update
    (statePort s) _ _ (statePort out) cv acc0 acc1 model
  exact ⟨out,native,bounds,Prod.ext values.1 values.2⟩

inductive Trace : List (NE×NQ) → Native → Native → Prop where
  | done (s : Native) : Trace [] s s
  | step {v : NE} {q : NQ} {xs : List (NE×NQ)} {s next out : Native}
      (canonicalV : canonE v) (canonicalQ : canonQ q)
      (call : FIo_Native.fast_pairing.EbyKDot.push s v q=ok (.Ok (),next))
      (tail : Trace xs next out) : Trace ((v,q)::xs) s out

/-- Ordered public fold for every source-shaped successful prefix, including
all29 iterations at every one of the six points. No sum-value invariant is an
input hypothesis; it follows from the source calls and zero-prefix bounds. -/
theorem trace_value {xs : List (NE×NQ)} {s out : Native} (tr : Trace xs s out)
    (n : Nat) (fits : n+xs.length≤29) (hs : Bounded s n) :
    Bounded out (n+xs.length) ∧ meaning out=fold (meaning s) xs := by
  induction tr generalizing n with
  | done s => exact ⟨by simpa only [List.length_nil,Nat.add_zero] using hs,rfl⟩
  | @step v q xs s next out hv hq call tail ih =>
    have hn : n<29 := by simp only [List.length_cons] at fits; omega
    obtain ⟨actual,actualCall,hbound,hvalue⟩ := step s v q n hn hs hv hq
    have same : actual=next := congrArg Prod.snd (Result.ok.inj (actualCall.symm.trans call))
    subst actual
    obtain ⟨last,value⟩ := ih (n+1) (by simp only [List.length_cons] at fits; omega) hbound
    constructor
    · simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using last
    · rw [fold,←hvalue]
      exact value

#print axioms dot_bound
#print axioms below46
#print axioms step
#print axioms trace_value
end AspisR1.NGU_LPm_PublicFold

-- Retargeted LPm_PublicTwentyNine
set_option autoImplicit false
namespace AspisR1.NGU_LPm_PublicTwentyNine
open Aeneas Aeneas.Std Result NFN_LPi_FieldValues NGU_LPm_RawPort NGU_LPm_PublicFold

def zero : Native :=
  ⟨⟨Array.repeat 4#usize 0#u64⟩,⟨Array.repeat 4#usize 0#u64⟩,0#usize⟩

theorem source_new : FIo_Native.fast_pairing.EbyKDot.new=ok zero := rfl

theorem initial_bound : Bounded zero 0 := by
  refine ⟨rfl,?_,?_⟩
  all_goals
    intro x hx
    simp only [zero,Array.repeat,List.mem_replicate] at hx
    rcases hx with ⟨_,rfl⟩
    simp only [Nat.zero_mul]
    decide

/-- ONE theorem applies to each of the six actual point traces. The local
native calls determine the value; no public field-sum equality is assumed. -/
theorem source (xs : List (NE×NQ)) (out : Native) (size : xs.length=29)
    (tr : Trace xs zero out) :
    Bounded out 29 ∧ meaning out=fold (meaning zero) xs := by
  have result := trace_value tr 0 (by omega) initial_bound
  simpa only [size,Nat.zero_add] using result

#print axioms source_new
#print axioms initial_bound
#print axioms source
end AspisR1.NGU_LPm_PublicTwentyNine

-- Retargeted LPm_SemanticSelections
set_option autoImplicit false
namespace AspisR1.NGU_LPm_SemanticSelections
open Aeneas Aeneas.Std Result AspisR1CurrentPreparedClaim

/-- Exact source array/index routing, including its Result failures. No
canonicality or supplied scalar-read observation is needed. -/
theorem claims {Dot Hash : Type} (ops : ClaimDotOps Dot) (sem : r1_semantic.Verified Hash)
    (y1 : Slice U8) (point lane : Usize) (hp : point.val<3) :
    ClaimScalar.read ops sem y1 point lane =
      (do let row ← Array.index_usize sem.claims point; Array.index_usize row lane) := by
  have small : point≤2#usize := by scalar_tac
  simp only [ClaimScalar.read,if_pos small]

theorem extra {Dot Hash : Type} (ops : ClaimDotOps Dot) (sem : r1_semantic.Verified Hash)
    (y1 : Slice U8) (point lane : Usize) (hp : point.val=3) :
    ClaimScalar.read ops sem y1 point lane = Array.index_usize sem.extra lane := by
  have large : ¬point≤2#usize := by scalar_tac
  simp only [ClaimScalar.read,if_neg large,hp]

theorem before_z1 {Dot Hash : Type} (ops : ClaimDotOps Dot) (sem : r1_semantic.Verified Hash)
    (y1 : Slice U8) (point lane : Usize) (hp : point.val=4) :
    ClaimScalar.read ops sem y1 point lane = Array.index_usize sem.before_z1 lane := by
  have large : ¬point≤2#usize := by scalar_tac
  simp only [ClaimScalar.read,if_neg large,hp]

#print axioms claims
#print axioms extra
#print axioms before_z1
end AspisR1.NGU_LPm_SemanticSelections

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
