import KpowersCurrentQMSemanticsV1
import CurrentWideQMField
import ExtractedCurrentQM31Exact
import S4FromFnP6GeneratedInterface

open Aeneas Aeneas.Std Result
set_option autoImplicit false

namespace AspisR1S3KpowersTotalConstructiveV1

open AspisR1S9HelperP6
open AspisR1S9HelperP6PowerSemanticsV1
open AspisR1FromFnP6
open AspisR1FromFnP6Generated

abbrev Q := field.QM31
abbrev C := weights.kpowers.closure (4#usize)

private def fromOld (x : AspisR1CurrentWide.Proof.Old.QM31) : AspisR1CurrentWide.field.QM31 :=
  ⟨⟨x.c0.a, x.c0.b⟩, ⟨x.c1.a, x.c1.b⟩⟩

private theorem toQM_fromOld (x : AspisR1CurrentWide.Proof.Old.QM31) :
    AspisR1CurrentWide.Proof.toQM (fromOld x) = x := by cases x <;> rfl

private theorem current_qm_mul_total (x y : AspisR1CurrentWide.field.QM31)
    (hx : AspisR1CurrentWide.Proof.CanonicalQM x)
    (hy : AspisR1CurrentWide.Proof.CanonicalQM y) :
    ∃ z, AspisR1CurrentWide.field.QM31.mul x y = .ok z ∧
      AspisR1CurrentWide.Proof.CanonicalQM z := by
  obtain ⟨raw, hraw, hcan, _⟩ :=
    AspisR1.ExtractedCurrentQM31Exact.current_qm_mul_exact
      (AspisR1CurrentWide.Proof.toQM x) (AspisR1CurrentWide.Proof.toQM y) hx hy
  have hsame := AspisR1CurrentWide.Proof.qm_mul_same x y
  rw [hraw] at hsame
  refine ⟨fromOld raw, ?_, ?_⟩
  · cases hmul : AspisR1CurrentWide.field.QM31.mul x y with
    | fail e => simp [hmul] at hsame
    | div => simp [hmul] at hsame
    | ok z =>
        have hz : AspisR1CurrentWide.Proof.toQM z = raw := by
          simpa [hmul, bind_tc_ok] using hsame
        have hback : fromOld (AspisR1CurrentWide.Proof.toQM z) = z := by cases z <;> rfl
        have hzback : z = fromOld raw := by
          calc
            z = fromOld (AspisR1CurrentWide.Proof.toQM z) := hback.symm
            _ = fromOld raw := congrArg fromOld hz
        exact congrArg Result.ok hzback
  · change AspisR1.ExtractedCurrentQM31Exact.CurrentCanonicalQM
      (AspisR1CurrentWide.Proof.toQM (fromOld raw))
    rw [toQM_fromOld]
    exact hcan

private def stateOK (state : C) : Nat → Prop := fun _ =>
  currentQMSemantics.canonical state.1 ∧ currentQMSemantics.canonical state.2

private theorem qmul_total_helper (a q : Q)
    (ha : currentQMSemantics.canonical a)
    (hq : currentQMSemantics.canonical q) :
    ∃ z, FieldOps.qmMul a q = .ok z ∧ currentQMSemantics.canonical z := by
  obtain ⟨out, hout, hcan⟩ := current_qm_mul_total
    (helperToCurrentQM a) (helperToCurrentQM q) ha hq
  refine ⟨currentToHelperQM out, ?_, ?_⟩
  · change (do
      let z ← AspisR1CurrentWide.field.QM31.mul
        (helperToCurrentQM a) (helperToCurrentQM q)
      ok (currentToHelperQM z)) = .ok (currentToHelperQM out)
    rw [hout]
    rfl
  · exact hcan

private theorem small_max (n : Nat) (hn : n < 2048) : n ≤ Usize.max := by
  have hpow : n < 2 ^ UScalarTy.Usize.numBits := by
    rw [UScalarTy.Usize_numBits_eq, ← Usize.max_succ_eq_pow]
    have hmax := Usize.cMax_bound_concrete.1
    omega
  have hsucc : n < Usize.max + 1 := by
    simpa only [UScalarTy.Usize_numBits_eq, Usize.max_succ_eq_pow] using hpow
  omega

private theorem run_forward {S A : Type} (step : S → Nat → Result (A × S))
    (n : Nat) (I : S → Nat → Prop) (V : A → Prop)
    (hstep : ∀ s i, i < n → I s i → ∃ a s', step s i = .ok (a,s') ∧ V a ∧ I s' (i+1)) :
    ∀ (count start : Nat) (s : S), start+count≤n → I s start →
      ∃ vals final, AspisR1FromFnP6.statefulFromFnRun step count start s = .ok (vals,final) ∧
        vals.length=count ∧ (∀ a ∈ vals, V a) ∧ I final (start+count) := by
  intro count
  induction count with
  | zero =>
      intro start s hbound hs
      refine ⟨[],s,by simp [AspisR1FromFnP6.statefulFromFnRun],rfl,?_,?_⟩
      · intro a ha; cases ha
      · simpa using hs
  | succ count ih =>
      intro start s hbound hs
      obtain ⟨a,s',hcall,hV,hI⟩ := hstep s start (by omega) hs
      obtain ⟨vals,final,hrun,hlen,hvals,hfinal⟩ := ih (start+1) s' (by omega) hI
      refine ⟨a::vals,final,?_,by simp [hlen],?_,?_⟩
      · simp only [AspisR1FromFnP6.statefulFromFnRun,hcall,bind_tc_ok]
        change (do
          let (tail,last) ← AspisR1FromFnP6.statefulFromFnRun step count (start+1) s'
          .ok (a::tail,last)) = .ok (a::vals,final)
        rw [hrun]
        rfl
      · intro x hx
        rcases List.mem_cons.mp hx with h | h
        · simpa [h] using hV
        · exact hvals x h
      · have heq : start+(count+1)=start+1+count := by omega
        rw [heq]
        exact hfinal

theorem kpowers_success_of_canonical_seed
    (seed : Q) (hseed : currentQMSemantics.canonical seed) :
    ∃ values : Array Q (4#usize),
      @weights.kpowers currentFieldOps (4#usize) seed = .ok values := by
  let cb := weights.kpowers.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 (4#usize)
  let step : (C × Usize) → Nat → Result (Q × (C × Usize)) := fnMutStep cb
  let I : (C × Usize) → Nat → Prop := fun st i => st.2.val=i ∧ stateOK st.1 i
  let V : Q → Prop := currentQMSemantics.canonical
  have hinit : I ((field.QM31.ONE,seed),0#usize) 0 := by
    constructor
    · rfl
    · exact ⟨currentQMSemantics.one_canonical,hseed⟩
  have hstep : ∀ st i, i<4 → I st i → ∃ a st', step st i = .ok (a,st') ∧ V a ∧ I st' (i+1) := by
    intro st i hi hst
    rcases st with ⟨c,cursor⟩
    rcases c with ⟨a,q⟩
    rcases hst with ⟨hcursor,ha,hq⟩
    obtain ⟨prod,hprod,hprodcan⟩ := qmul_total_helper a q ha hq
    have hcursorCap : cursor.val + (1#usize).val ≤ Usize.max := by
      rw [hcursor]
      have hone : (1#usize).val = 1 := by decide
      rw [hone]
      calc
        i+1 ≤ 4 := by omega
        _ ≤ Usize.max := small_max 4 (by omega)
    have hcursorCap' : cursor.val + (1#usize).val ≤ UScalar.max UScalarTy.Usize := by
      simpa only [UScalar.max_USize_eq] using hcursorCap
    obtain ⟨cursor',hinc,hcursorval⟩ :=
      WP.spec_imp_exists (UScalar.add_spec (x := cursor) (y := 1#usize) hcursorCap')
    have hcall : cb.call_mut (a,q) cursor = .ok (a,(prod,q)) := by
      simp [cb, weights.kpowers.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut,
        weights.kpowers.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31,
        weights.kpowers.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once,
        weights.kpowers.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31,
        field.QM31.mul, currentFieldOps, currentQMOps, hprod, bind_tc_ok]
    refine ⟨a,((prod,q),cursor'),?_,ha,?_,?_⟩
    · unfold step fnMutStep
      rw [hcall, hinc]
      rfl
    · change cursor'.val = i+1
      rw [hcursorval, hcursor]
      simp
    · exact ⟨hprodcan,hq⟩
  obtain ⟨items,final,hrun,hlen,_hvals,_hfinal⟩ := run_forward step 4 I V hstep 4 0
    ((field.QM31.ONE,seed),0#usize) (by omega) hinit
  have hmodel : core.array.from_fn_model (4#usize) cb (field.QM31.ONE,seed) =
      .ok (⟨items,by simpa using hlen⟩,final) := by
    unfold core.array.from_fn_model core.array.from_fn_trace_model
    simp only [step] at hrun
    simp [AspisR1FromFnP6Generated.packArrayState, hrun, hlen]
  refine ⟨⟨items,by simpa using hlen⟩, ?_⟩
  unfold weights.kpowers core.array.from_fn
  simp [cb, hmodel]

#print axioms kpowers_success_of_canonical_seed

end AspisR1S3KpowersTotalConstructiveV1
