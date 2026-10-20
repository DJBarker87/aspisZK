import FinishDotCountBoundV3
import FinishDotConcreteOps
import S5QRaw.EbyKPushDecodedProductUpdateV1
import FinishCandidateDotSuccess
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FinishDotDecodedProductTrace
open AspisR1FinishDotCountBoundV2
open AspisR1FinishDotConcreteOps
open AspisR1EbyKPushDecodedProductUpdate
open AspisR1FinishRelationCurrent

abbrev M := AspisR1.R22RawQmProductResidues.M
abbrev PushState := AspisR1FinishDotSourceABI.PushState
abbrev FinishE := AspisR1CurrentWide.Proof.FinishE
abbrev FinishQM := AspisR1CurrentWide.Proof.FinishQM

abbrev Delta := (M × M × M × M) × (M × M × M × M)

def stateDelta (s : PushState) : Delta := (castSums s.c0.sums, castSums s.c1.sums)
def deltaAdd (x y : Delta) : Delta := (tupleAdd x.1 y.1, tupleAdd x.2 y.2)

def queryDelta (x : FinishE) (q : FinishQM) : Delta :=
  (AspisR1.R22RawQmProductResidues.qmulCoefficients
    ((x.c0.c0.a.val,x.c0.c0.b.val),(x.c0.c1.a.val,x.c0.c1.b.val))
    ((q.c0.a.val,q.c0.b.val),(q.c1.a.val,q.c1.b.val)),
   AspisR1.R22RawQmProductResidues.qmulCoefficients
    ((x.c1.c0.a.val,x.c1.c0.b.val),(x.c1.c1.a.val,x.c1.c1.b.val))
    ((q.c0.a.val,q.c0.b.val),(q.c1.a.val,q.c1.b.val)))

def deltaSum : List (Usize × FinishE × FinishQM) → Delta
  | [] => (0,0)
  | t::xs => deltaAdd (queryDelta t.2.1 t.2.2) (deltaSum xs)

def countInv (j : Nat) (s : PushState) : Prop :=
  sumsBelowCount j s.c0.sums ∧ sumsBelowCount j s.c1.sums ∧ s.count.val = j

theorem members_lt_two46 (k : Nat) (s : Array U64 4#usize)
    (hk : k < 4096) (hs : sumsBelowCount k s) :
    ∀ x ∈ s.val, x.val < 2^46 := by
  intro x hx
  have hmem := List.mem_iff_getElem.mp hx
  rcases hmem with ⟨i, hi, hix⟩
  subst x
  have hi4 : i < 4 := by simpa [s.property] using hi
  have hbound := count_bound_to_preaccumulator k s hk hs i hi4
  exact hbound

theorem chain_product_trace {W : Type}
    (base : FinishOps W PushState)
    (fm : Slice U8) (ws : Slice FinishQM)
    (fieldCanonical : ∀ j x, base.field fm j = .ok x →
      AspisR1EbyKPowerValueCanonicalToPush.pushCanonical (toPushWide x))
    {j : Usize} {initial final : PushState}
    (trace : FinishCandidateDotTrace.Chain (withConcreteDot base AspisR1EbyKPushDecodedProductUpdate.QRaw) fm ws j initial final)
    (hinv : countInv j.val initial) :
    ∃ xs : List (Usize × FinishE × FinishQM),
      stateDelta final = deltaAdd (stateDelta initial) (deltaSum xs) ∧
      xs.length + j.val = ws.len.val ∧
      (∀ k, ∀ hk : k < xs.length, (xs[k]'hk).1.val = j.val + k) ∧
      (∀ t ∈ xs, t.1 < ws.len ∧ base.field fm t.1 = .ok t.2.1 ∧
        Slice.index_usize ws t.1 = .ok t.2.2) ∧
      countInv ws.len.val final := by
  induction trace with
  | done j s hend =>
      have hinv' : countInv ws.len.val s := by
        rw [← hend]
        exact hinv
      refine ⟨[], ?_, ?_, ?_, ?_, hinv'⟩
      · simp [stateDelta,deltaAdd,tupleAdd,deltaSum]
      · simp [hend]
      · intro k hk
        simp at hk
      · simp
  | @step j j1 s s1 out x q active hread hweight hpush hincrement tail ih =>
      obtain ⟨lo,hi,hlo,hhi,hstate0,hstate1,hguard,hcount,hscalar⟩ :=
        AspisR1EbyKPushDotBackend.successful_push_exact_backend AspisR1EbyKPushDecodedProductUpdate.QRaw s (toPushWide x) (toPushQM q) s1 (by simpa [withConcreteDot] using hpush)
      have hk : j.val < 4096 := by
        have hc : s.count.val < 4096 := by simpa [AspisR1EbyKPushExplicitOpsV1.maxTerms] using hguard
        have hcj : s.count.val = j.val := hinv.2.2
        omega
      have hacc0 := members_lt_two46 j.val s.c0.sums hk hinv.1
      have hacc1 := members_lt_two46 j.val s.c1.sums hk hinv.2.1
      have hcan := fieldCanonical j x hread
      have hupdate := successful_push_decoded_product_update s (toPushWide x) (toPushQM q) s1 hcan hacc0 hacc1 (by simpa [withConcreteDot] using hpush)
      have hstepinv := invariant_step base AspisR1EbyKPushDecodedProductUpdate.QRaw j j1 s s1 x q hpush hincrement hinv
      obtain ⟨xs, htailDelta, htailLen, htailSeq, htailReads, htailInv⟩ := ih hstepinv
      have hidx0 := UScalar.add_equiv j 1#usize
      rw [hincrement] at hidx0
      have hidx : j1.val = j.val + 1 := hidx0.2.1
      refine ⟨(j,x,q)::xs, ?_, ?_, ?_, ?_, htailInv⟩
      · have hlocal0 : castSums s1.c0.sums = tupleAdd (castSums s.c0.sums) (queryDelta x q).1 := by
          simpa [toPushWide,toPushQM,queryDelta] using hupdate.1
        have hlocal1 : castSums s1.c1.sums = tupleAdd (castSums s.c1.sums) (queryDelta x q).2 := by
          simpa [toPushWide,toPushQM,queryDelta] using hupdate.2
        have h0 := congrArg Prod.fst htailDelta
        have h1 := congrArg Prod.snd htailDelta
        simp only [stateDelta, deltaAdd, deltaSum] at h0 h1 ⊢
        apply Prod.ext
        · rw [h0, hlocal0]
          simp [tupleAdd, add_assoc]
        · rw [h1, hlocal1]
          simp [tupleAdd, add_assoc]
      · simp only [List.length_cons] at htailLen ⊢
        omega
      · intro k hk
        cases k with
        | zero => simp
        | succ k =>
          have hk' : k < xs.length := by simpa using hk
          have htail := htailSeq k hk'
          have hget : ((j,x,q)::xs)[k+1]'hk = xs[k]'hk' := by simp
          rw [hget, htail, hidx]
          omega
      · intro t ht
        simp only [List.mem_cons] at ht
        rcases ht with hhead | htail
        · subst t
          exact ⟨active,hread,hweight⟩
        · exact htailReads t htail


theorem successful_concrete_finish_query_product_trace {W : Type}
    (base : FinishOps W PushState)
    (fm : Slice U8) (ws : Slice FinishQM) (out : FinishE)
    (fieldCanonical : ∀ j x, base.field fm j = .ok x →
      AspisR1EbyKPowerValueCanonicalToPush.pushCanonical (toPushWide x))
    (hrun : verifier.finish_query_dot
      (withConcreteDot base AspisR1EbyKPushDecodedProductUpdate.QRaw) fm ws = .ok (.Ok out)) :
    ∃ final : PushState, ∃ xs : List (Usize × FinishE × FinishQM),
      AspisR1FinishDotSourceABI.finishFromPush final = .ok out ∧ final.count.val = ws.len.val ∧
      stateDelta final = deltaSum xs ∧ xs.length = ws.len.val ∧
      (∀ k, ∀ hk : k < xs.length, (xs[k]'hk).1.val = k) ∧
      (∀ t ∈ xs, t.1 < ws.len ∧ base.field fm t.1 = .ok t.2.1 ∧
        Slice.index_usize ws t.1 = .ok t.2.2) := by
  obtain ⟨initial,final,hnew,hchain,hfinish⟩ :=
    FinishCandidateDotTrace.finish_success_trace
      (withConcreteDot base AspisR1EbyKPushDecodedProductUpdate.QRaw) fm ws out hrun
  have hzero : initial = EbyKNewToPushStateABI.pushZero :=
    Result.ok.inj (hnew.symm.trans sourceNewDot_zero)
  have hinit : countInv 0 initial := by
    rw [hzero]
    refine ⟨?_, ?_, rfl⟩
    · intro i hi
      have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
      rcases cases with h | h | h | h <;> subst i <;>
        simp [EbyKNewToPushStateABI.pushZero]
    · intro i hi
      have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
      rcases cases with h | h | h | h <;> subst i <;>
        simp [EbyKNewToPushStateABI.pushZero]
  obtain ⟨xs,hdelta,hlen,hseq,hreads,hinv⟩ := chain_product_trace base fm ws fieldCanonical hchain hinit
  have hzeroDelta : stateDelta initial = (0,0) := by
    rw [hzero]
    simp [stateDelta, castSums, EbyKNewToPushStateABI.pushZero]
  have hfinish' : AspisR1FinishDotSourceABI.finishFromPush final = .ok out := by
    simpa [withConcreteDot] using hfinish
  refine ⟨final,xs,hfinish',hinv.2.2,?_,?_,?_,hreads⟩
  · calc
      stateDelta final = deltaAdd (stateDelta initial) (deltaSum xs) := hdelta
      _ = deltaSum xs := by rw [hzeroDelta]; simp [deltaAdd,tupleAdd]
  · have hzeroIdx : (0#usize).val = 0 := rfl
    change xs.length + (0#usize).val = ws.len.val at hlen
    rw [hzeroIdx, Nat.add_zero] at hlen
    exact hlen
  · intro k hk
    simpa using hseq k hk

#print axioms chain_product_trace
#print axioms successful_concrete_finish_query_product_trace

end AspisR1FinishDotDecodedProductTrace
