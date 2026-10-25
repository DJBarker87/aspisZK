import S1ClaimOwnedInnerCpsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1CurrentPreparedClaim.OwnedNestedTransfer
abbrev Parts := Array E 7#usize
abbrev OuterState := Range × Parts
abbrev RustClaim := core.result.Result E verifier.Error
abbrev PendingOuter := Parts × Option RustClaim

def finishOuter (k : Parts) (r : PendingOuter) : Result RustClaim := do
  match r.2 with
  | none => let value ← verifier.owned_sum k r.1;ok (.Ok value)
  | some result => ok result

def outerPost (k : Parts) (kont : OuterState → Result RustClaim)
    (cf : ControlFlow OuterState PendingOuter) : Result RustClaim :=
  match cf with | .done out => finishOuter k out | .cont next => kont next

def refOuterPost (kont : OuterState → Result RustClaim)
    (cf : ControlFlow OuterState RustClaim) : Result RustClaim :=
  match cf with | .done out => ok out | .cont next => kont next

def ownedOuterStep {D H : Type} {N : Usize} (ops : ClaimDotOps D)
    (sem : r1_semantic.Verified H) (y1 : Array U8 N) (g : Array E 29#usize) (s : OuterState) :=
  verifier.owned_claim_loops_loop0.body ops sem.claims sem.extra sem.before_z1 y1 g s.1 s.2

def continuePart (point : Usize) (iter1 : Range) (parts : Parts)
    (kont : OuterState → Result RustClaim) (r : RustClaim) : Result RustClaim := do
  match r with
  | .Err error => ok (.Err error)
  | .Ok value =>
    let i ← point+1#usize
    let next ← Array.update parts i value
    kont (iter1,next)

def ownedAfter {D : Type} (ops : ClaimDotOps D) (point : Usize) (iter1 : Range)
    (parts : Parts) (r : D × Option RustClaim) : Result (ControlFlow OuterState PendingOuter) := do
  match r.2 with
  | none =>
    let value ← ops.finishDot r.1
    let i ← point+1#usize
    let next ← Array.update parts i value
    ok (.cont (iter1,next))
  | some _ => ok (.done (parts,r.2))

/-- One complete emitted outer iteration in any continuation, retaining every
child call and error. The inner execution is the proved concrete instance. -/
theorem outer_step_cps {D H : Type} {N : Usize} (ops : ClaimDotOps D)
    (inst : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
    (y1 : Array U8 N) (g : Array E 29#usize) (k parts : Parts) (iter : Range)
    (kont : OuterState → Result RustClaim) :
    (do let cf ← ownedOuterStep ops sem y1 g (iter,parts);outerPost k kont cf) =
    (do let cf ← verifier.prepared_claim_loop.body ops inst sem (Array.to_slice y1) g k iter parts
        refOuterPost kont cf) := by
  cases hn : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter with
  | fail e =>
    simp only [ownedOuterStep,verifier.owned_claim_loops_loop0.body,
      verifier.prepared_claim_loop.body,hn,bind_tc_fail]
  | div =>
    simp only [ownedOuterStep,verifier.owned_claim_loops_loop0.body,
      verifier.prepared_claim_loop.body,hn,bind_tc_div]
  | ok pair =>
    rcases pair with ⟨opt,iter1⟩
    cases opt with
    | none =>
      have ho : ownedOuterStep ops sem y1 g (iter,parts)=.ok (.done (parts,none)) := by
        unfold ownedOuterStep verifier.owned_claim_loops_loop0.body
        rw [hn];rfl
      have hr : verifier.prepared_claim_loop.body ops inst sem (Array.to_slice y1) g k iter parts =
          (do let value ← verifier.prepared_claim_sum k parts;ok (.done (.Ok value))) := by
        unfold verifier.prepared_claim_loop.body
        rw [hn];rfl
      rw [ho,hr]
      simp only [bind_tc_ok,
        outerPost,refOuterPost,finishOuter,sum_eq,bind_assoc_eq] <;> rfl
    | some point =>
      have ho : ownedOuterStep ops sem y1 g (iter,parts) = (do
          let dot ← ops.newDot
          let (dot1,pending) ← verifier.owned_claim_loops_loop0_loop0 ops
            {start:=0#usize,«end»:=29#usize} sem.claims sem.extra sem.before_z1 y1 g point dot
          match pending with
          | none =>
            let value ← ops.finishDot dot1
            let i ← point+1#usize
            let next ← Array.update parts i value
            ok (.cont (iter1,next))
          | some _ => ok (.done (parts,pending))) := by
        unfold ownedOuterStep verifier.owned_claim_loops_loop0.body
        rw [hn];rfl
      have hr : verifier.prepared_claim_loop.body ops inst sem (Array.to_slice y1) g k iter parts = (do
          let r ← verifier.prepared_claim_dot ops inst sem (Array.to_slice y1) g point
          let cf ← core.result.Result.Insts.CoreOpsTry.branch r
          match cf with
          | .Continue value =>
            let i ← point+1#usize
            let next ← Array.update parts i value
            ok (.cont (iter1,next))
          | .Break residual =>
            let r1 ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              E (core.convert.FromSame verifier.Error) residual
            ok (.done r1)) := by
        unfold verifier.prepared_claim_loop.body
        rw [hn];rfl
      rw [ho,hr]
      simp only [verifier.prepared_claim_dot,bind_assoc_eq]
      apply bind_congr
      intro dot
      calc
        _ = (do
          let r ← verifier.owned_claim_loops_loop0_loop0 ops {start:=0#usize,«end»:=29#usize}
            sem.claims sem.extra sem.before_z1 y1 g point dot
          interpretPending ops (continuePart point iter1 parts kont) (fun v => ok (.Ok v)) r) := by
            apply bind_congr
            rintro ⟨dot1,pending⟩
            change Bind.bind (ownedAfter ops point iter1 parts (dot1,pending)) (outerPost k kont) =
              interpretPending ops (continuePart point iter1 parts kont) (fun v => ok (.Ok v)) (dot1,pending)
            cases pending with
            | none =>
              simp only [ownedAfter,interpretPending,continuePart,outerPost,bind_assoc_eq,bind_tc_ok] <;> rfl
            | some r =>
              cases r <;> simp only [ownedAfter,interpretPending,continuePart,outerPost,finishOuter,bind_tc_ok] <;> rfl
        _ = (do
          let r ← verifier.prepared_claim_dot_loop ops inst {start:=0#usize,«end»:=29#usize}
            sem (Array.to_slice y1) g point dot
          continuePart point iter1 parts kont r) :=
            complete_inner_cps ops inst sem y1 g point (continuePart point iter1 parts kont)
              (fun v => ok (.Ok v)) {start:=0#usize,«end»:=29#usize} dot (by decide) (by decide)
        _ = _ := by
          apply bind_congr
          intro r
          cases r <;> simp [continuePart,refOuterPost,core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            bind_assoc_eq]

#print axioms outer_step_cps
end AspisR1CurrentPreparedClaim.OwnedNestedTransfer
