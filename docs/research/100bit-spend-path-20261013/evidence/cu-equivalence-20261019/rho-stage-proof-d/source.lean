import AspisR1RhoStage.Funs
import CuSavingsRhoQuery
import CuSavingsRhoInitializationCanonical
set_option autoImplicit false
namespace AspisR1.CuSavingsRhoStage
open Aeneas Aeneas.Std Result ControlFlow AspisR1RhoStage
open CuSavingsRhoInitRow CuSavingsRhoVector CuSavingsRhoFinishModel
abbrev Acc := verifier.Accumulator
abbrev BW := BatchedWeights
abbrev RustOut := core.result.Result Acc verifier.Error
variable [AspisR1RhoAccumulate.AccumulateCommon] [AspisR1RhoQuery.QueryCommon]
variable [AspisR1CuRho.HeapReserve]

def oldObserve (out : Acc × Option RustOut) : Result RustOut :=
  .ok (match out.2 with | none => .Ok out.1 | some r => r)
def newObserve (out : Acc × BW × Option RustOut) : Result RustOut := do
  match out.2.2 with
  | some r => .ok r
  | none =>
    let weights ← AspisR1CuRhoSource.verifier.BatchedWeights.finish out.2.1 out.1.weights
    .ok (.Ok {out.1 with weights:=weights})

/-- The actual emitted loops are related by a symbolic remaining-query
induction. No 22-query concrete normalization or successful-query premise. -/
theorem loops_equivalence {H : Type} (digest : aspis_core.Digest32 H)
    (v : verifier.View) (p : verifier.Prepared)
    (g : Array aspis_core.field.WideExact 29#usize) (hash : H)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : QueryGeometry)
    (end1 : Usize) (he : end1.val ≤ 22) (hr : Canonical p.rho)
    (fuel : Nat) (a : Acc) (b : BW)
    (hg : Good b []) (hp : Canonical a.power) (hc : b.terms.val ≤ a.next.val)
    (hl : (alloc.vec.Vec.len a.weights).val ≤ 256)
    (hrows : a.weights.val.length=b.raw.val.length)
    (hspan : end1.val-a.next.val=fuel) :
    (do let out ← stage_old_loop digest v v.variant v.inactive v.folded_root p
          {a with weights:=CuSavingsRhoQuery.canonicalVec b} g hash obs geometry end1
        oldObserve out) =
    (do let out ← stage_new_loop digest v v.variant v.inactive v.folded_root p
          a g hash obs geometry end1 b
        newObserve out) := by
  induction fuel generalizing a b with
  | zero =>
    have hstop : ¬ a.next < end1 := by change ¬ a.next.val < end1.val;omega
    have hf := CuSavingsRhoSourceFinish.source_success b a.weights hrows
    conv_lhs => rw [stage_old_loop,loop]
    conv_rhs => rw [stage_new_loop,loop]
    simp only [stage_old_loop.body,stage_new_loop.body,hstop,if_false,
      bind_tc_ok,uncurry_apply_pair,oldObserve,newObserve,hf]
    rfl
  | succ fuel ih =>
    have hgo : a.next < end1 := by change a.next.val < end1.val;omega
    have hn : a.next.val < 22 := by change a.next.val < end1.val at hgo;omega
    have hcount : b.terms.val < 22 := by omega
    have heq := CuSavingsRhoQuery.source_equivalence digest v p a b g hash obs geometry
      hg hp hr hn hcount hl hrows
    conv_lhs => rw [stage_old_loop,loop]
    conv_rhs => rw [stage_new_loop,loop]
    simp only [stage_old_loop.body,stage_new_loop.body,hgo,if_pos,
      stage_query_old,stage_query_new]
    cases hq : AspisR1RhoQuery.query_new.query_with_geometry digest v p a g hash obs geometry b with
    | fail error =>
      simp only [hq,bind_tc_fail] at heq
      simp only [heq,hq,bind_tc_fail]
    | div =>
      simp only [hq,bind_tc_div] at heq
      simp only [heq,hq,bind_tc_div]
    | ok r =>
      cases r with
      | Err error =>
        simp only [hq,bind_tc_ok,CuSavingsRhoQuery.observe] at heq
        simp only [heq,hq,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          oldObserve,newObserve]
        rfl
      | Ok pair =>
        rcases pair with ⟨a',b'⟩
        obtain ⟨hg',hcount',hlen',hw',hp',hnext',_⟩ :=
          CuSavingsRhoQuery.source_success digest v p a b g hash obs geometry
            hg hp hr hn hcount hl hrows (a',b') hq
        dsimp only [Prod.fst,Prod.snd] at hg' hcount' hlen' hw' hp' hnext'
        have hrows' : a'.weights.val.length=b'.raw.val.length := by rw [hw',hlen',hrows]
        have hf := CuSavingsRhoSourceFinish.source_success b' a'.weights hrows'
        simp only [hq,bind_tc_ok,CuSavingsRhoQuery.observe,hf] at heq
        simp only [heq,hq,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
        have hc' : b'.terms.val ≤ a'.next.val := by omega
        have hl' : (alloc.vec.Vec.len a'.weights).val ≤ 256 := by rw [hw'];exact hl
        have hspan' : end1.val-a'.next.val=fuel := by omega
        exact ih a' b' hg' hp' hc' hl' hrows' hspan'

private theorem bind_ok {A B : Type} (m : Result A) (f : A → Result B) (out : B)
    (h : (do let x ← m;f x) = .ok out) :
    ∃ x,m = .ok x ∧ f x = .ok out := by
  cases m with
  | fail error => cases h
  | div => cases h
  | ok x => exact ⟨x,rfl,h⟩

theorem initialization_success (weights : Slice aspis_core.field.QM31)
    (hc : CuSavingsRhoResumeLoans.CanonicalFrom weights 0) (out : BW)
    (h : BatchedWeights.new weights = .ok (.Ok out)) :
    Good out [] ∧ canonicalSlice out=weights ∧ out.terms.val=0 ∧
      out.raw.val.length=weights.val.length := by
  unfold BatchedWeights.new at h
  obtain ⟨r,hs,h⟩ := bind_ok _ _ _ h
  cases r with
  | Err error => cases h
  | Ok b =>
    cases core.result.Result.Ok.inj (Result.ok.inj h)
    obtain ⟨_,hg,hproj,hcount,hlen⟩ :=
      CuSavingsRhoInitializationCanonical.source_success weights hc b hs
    exact ⟨hg,hproj,hcount,hlen⟩

theorem new_outcome {H : Type} (digest : aspis_core.Digest32 H)
    (v : verifier.View) (p : verifier.Prepared) (a : Acc)
    (g : Array aspis_core.field.WideExact 29#usize) (hash : H)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : QueryGeometry) (end1 : Usize) :
    stage_new digest v p a g hash obs geometry end1 =
    (do let initialized ← BatchedWeights.new (alloc.vec.Vec.deref a.weights)
        match initialized with
        | .Err e => .ok (.Err e)
        | .Ok b => do
          let out ← stage_new_loop digest v v.variant v.inactive v.folded_root p a g hash obs geometry end1 b
          newObserve out) := by
  unfold stage_new
  cases hi : BatchedWeights.new (alloc.vec.Vec.deref a.weights) with
  | fail e => rfl
  | div => rfl
  | ok r =>
    cases r with
    | Err e => rfl
    | Ok b =>
      simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
      cases ho : stage_new_loop digest v v.variant v.inactive v.folded_root p a g hash obs geometry end1 b with
      | fail e => rfl
      | div => rfl
      | ok out =>
        rcases out with ⟨acc,bw,ret⟩
        cases ret <;> rfl

/-- Whole actual transaction stage equals the old stage preceded solely by
its extra source initializer. All initializer and query failures are retained.
The sufficient-resource obligation is thus isolated to that extra reservation. -/
theorem source_outcome {H : Type} (digest : aspis_core.Digest32 H)
    (v : verifier.View) (p : verifier.Prepared) (a : Acc)
    (g : Array aspis_core.field.WideExact 29#usize) (hash : H)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : QueryGeometry) (end1 : Usize)
    (he : end1.val ≤ 22) (hr : Canonical p.rho) (hp : Canonical a.power)
    (hc : CuSavingsRhoResumeLoans.CanonicalFrom a.weights 0)
    (hl : (alloc.vec.Vec.len a.weights).val ≤ 256) :
    stage_new digest v p a g hash obs geometry end1 =
    (do let initialized ← BatchedWeights.new (alloc.vec.Vec.deref a.weights)
        match initialized with
        | .Err e => .ok (.Err e)
        | .Ok _ => stage_old digest v p a g hash obs geometry end1) := by
  rw [new_outcome]
  cases hi : BatchedWeights.new (alloc.vec.Vec.deref a.weights) with
  | fail e => rfl
  | div => rfl
  | ok r =>
    cases r with
    | Err e => rfl
    | Ok b =>
      simp only [bind_tc_ok]
      have hc' : CuSavingsRhoResumeLoans.CanonicalFrom (alloc.vec.Vec.deref a.weights) 0 := hc
      obtain ⟨hg,hproj,hcount,hlen⟩ := initialization_success _ hc' b hi
      have hrows : a.weights.val.length=b.raw.val.length := hlen.symm
      have ha : {a with weights:=CuSavingsRhoQuery.canonicalVec b}=a := by
        change {a with weights:=canonicalSlice b}=a
        rw [hproj]
        rfl
      have hloop := loops_equivalence digest v p g hash obs geometry end1 he hr
        (end1.val-a.next.val) a b hg hp (by omega) hl hrows rfl
      rw [ha] at hloop
      rw [← hloop]
      unfold stage_old
      cases ho : stage_old_loop digest v v.variant v.inactive v.folded_root p a g hash obs geometry end1 with
      | fail e => rfl
      | div => rfl
      | ok out => rcases out with ⟨acc,ret⟩;cases ret <;> rfl

#print axioms initialization_success
#print axioms new_outcome
#print axioms source_outcome
#print axioms loops_equivalence
end AspisR1.CuSavingsRhoStage
