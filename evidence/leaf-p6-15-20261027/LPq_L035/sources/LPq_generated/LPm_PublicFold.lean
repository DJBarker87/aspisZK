import LPm_PublicPort
import LPm_WordFold
set_option autoImplicit false
namespace AspisR1.LPm_PublicFold
open Aeneas Aeneas.Std Result LPi_FieldValues LPm_RawPort
abbrev B := LPf_DotWordStep.bound
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

theorem dot_bound (s : LPm_PublicState.Dot) (r : LPm_PublicState.Raw) (n : Nat)
    (hn : n<4096) (hs : ∀ x∈s.sums.val,x.val≤n*B) :
    ∀ x∈(LPm_PublicState.update s r).sums.val,x.val≤(n+1)*B := by
  obtain ⟨a,b,c,d,shape⟩ := LPf_ArrayFour.shape s.sums
  obtain ⟨e,f,g,h,raw⟩ := LPf_ArrayFour.shape r
  intro x hx
  simp only [LPm_PublicState.update,shape,raw,Array.make,List.getElem!_cons_zero,
    List.getElem!_cons_succ,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl
  all_goals
    apply (LPf_DotWordStep.value _ _ n hn _).2
    apply hs
    simp only [shape,Array.make,List.mem_cons,List.not_mem_nil,or_false]
    tauto

theorem below46 (x : U64) (n : Nat) (hn : n≤4096) (hx : x.val≤n*B) : x.val<2^46 := by
  norm_num only [Nat.reducePow]
  dsimp only [B,LPf_DotWordStep.bound] at hx
  omega

/-- Full native/cohort step and decoded FIELD product-sum update. The imported
R22 theorem supplies the multiplication interpretation; it is not re-proved. -/
theorem step (s : Native) (v : NE) (q : NQ) (n : Nat) (hn : n<29)
    (hs : Bounded s n) (hv : canonE v) (hq : canonQ q) :
    ∃ out, FIo_Native.fast_pairing.EbyKDot.push s v q=ok (.Ok (),out) ∧
      Bounded out (n+1) ∧ meaning out=plus (meaning s) (contribution v q) := by
  have count : s.count.val<4096 := by rw [hs.1]; omega
  obtain ⟨out,native,model⟩ := LPm_PublicPort.source s v q hv hq count
  obtain ⟨lo,hi,other,otherCall,_,_,h0,h1,inc⟩ := LPm_PublicState.source s v q hv hq count
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
end AspisR1.LPm_PublicFold
