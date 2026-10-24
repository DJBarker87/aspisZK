import R1Z.ProverRwRngMaterialPaths
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwRngMaterialInvariant
open Aeneas Aeneas.Std Result ProverRwRngMaterialBody
open aspis_prover.state_only_entropy aspis_prover.state_only_hiding
open aspis_core.state_only_hiding ProverRwRngMaterialControl ProverRwRngMaterialPaths
variable [TypeLeaves] [LocalLeaves]

def Returns {T : Type} (p : T → Prop) (r : Result T) : Prop :=
  ∀ out, r = .ok out → p out

omit [TypeLeaves] [LocalLeaves] in
theorem returns_bind {A B : Type} (p : B → Prop) (r : Result A) (f : A → Result B)
    (next : ∀ a, r = .ok a → Returns p (f a)) : Returns p (r >>= f) := by
  cases r with
  | fail e => intro out h; cases h
  | div => intro out h; cases h
  | ok a => exact next a rfl

def Post {S : Type} (after : S) (c : Context) (out : MaterialResult × S) : Prop :=
  out.2 = after ∧ ∀ m, out.1 = .Ok m → m.mask_nonce = c.mask_nonce

/-- For arbitrary mutable nonce policy and arbitrary admitted component
replies, every returned result retains the exact store returned by reserve;
every success gets the source context nonce. No totality or sampler law. -/
theorem layout_post {S : Type} (store : Store S) (hash : Hash)
    (binding entropy : Array U8 32#usize) (c : Context) (before after : S)
    (cells : Slice aspis_statement.trace_v4.TraceCell) (active : Array Bool 1024#usize)
    (reserved : store.reserve before c.statement_digest c.mask_nonce = .ok (true,after)) :
    Returns (Post after c)
      (build_mask_material_for_layout store hash binding c entropy before cells active) := by
  unfold build_mask_material_for_layout
  simp only [reserved,bind_tc_ok,Aeneas.Std.uncurry,ite_true]
  apply returns_bind
  intro seedStatus hseed
  cases seedStatus with
  | Err e =>
    change Returns (Post after c) (.ok (.Err e,after))
    intro out h; cases h
    exact ⟨rfl,by intro m impossible; cases impossible⟩
  | Ok seed =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
    apply returns_bind
    intro expander hexpander
    apply returns_bind
    intro inactive hinactive
    apply returns_bind
    rintro ⟨st1,s1⟩ hc1
    simp only [Aeneas.Std.uncurry]
    cases st1 with
    | Err e =>
      change Returns (Post after c) (.ok (.Err e,after))
      intro out h; cases h
      exact ⟨rfl,by intro m impossible; cases impossible⟩
    | Ok c1 =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
      apply returns_bind
      rintro ⟨st2,s2⟩ hcolumns
      simp only [Aeneas.Std.uncurry]
      cases st2 with
      | Err e =>
        change Returns (Post after c) (.ok (.Err e,after))
        intro out h; cases h
        exact ⟨rfl,by intro m impossible; cases impossible⟩
      | Ok columns =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
        apply returns_bind
        rintro ⟨st3,s3⟩ hg
        simp only [Aeneas.Std.uncurry]
        cases st3 with
        | Err e =>
          change Returns (Post after c) (.ok (.Err e,after))
          intro out h; cases h
          exact ⟨rfl,by intro m impossible; cases impossible⟩
        | Ok g =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
          apply returns_bind
          rintro ⟨st4,s4⟩ hh1
          simp only [Aeneas.Std.uncurry]
          cases st4 with
          | Err e =>
            change Returns (Post after c) (.ok (.Err e,after))
            intro out h; cases h
            exact ⟨rfl,by intro m impossible; cases impossible⟩
          | Ok h1 =>
            change Returns (Post after c) (.ok (.Ok ⟨c1,columns,g,h1,c.mask_nonce⟩,after))
            intro out h; cases h
            exact ⟨rfl,by intro m same; cases same; rfl⟩

/-- Successful material generation cannot return an unconsumed fresh ack.
Layout/cells/active-row errors may preserve it; the success branch must pass
through the actual fresh reserve. This discharges the old missing_ack
scenario at the emitted producer boundary for every local-leaf instance. -/
theorem material_success_ack (hash : Hash) (binding entropy : Array U8 32#usize)
    (c : Context) (m : StateOnlyMaskMaterial) (ack : PreReservedNonce)
    (returned : material hash binding c entropy = .ok (.Ok m,ack)) :
    ack = usedAck c ∧ m.mask_nonce = c.mask_nonce := by
  unfold material build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref at returned
  split at returned
  · cases returned
  · split at returned
    · cases returned
    · generalize hcells : cellsReply = rcells
      simp only [cellsReply] at hcells
      rw [hcells] at returned
      cases rcells with
      | fail e => cases returned
      | div => cases returned
      | ok st =>
        cases st with
        | Err e =>
          simp only [core.result.Result.map_err,bind_tc_ok] at returned
          cases returned
        | Ok cells =>
          simp only [core.result.Result.map_err,bind_tc_ok,
            core.result.Result.Insts.CoreOpsTry.branch,lift] at returned
          generalize hactive : activeReply = ractive
          simp only [activeReply] at hactive
          rw [hactive] at returned
          cases ractive with
          | fail e => cases returned
          | div => cases returned
          | ok st =>
            cases st with
            | Err e => cases returned
            | Ok active =>
              simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch] at returned
              have post := layout_post AckStore hash binding entropy c (freshAck c) (usedAck c)
                (alloc.vec.Vec.deref cells) active (acknowledgment_fresh c) (.Ok m,ack) returned
              exact ⟨post.1,post.2 m rfl⟩

#print axioms returns_bind
#print axioms layout_post
#print axioms material_success_ack
end R1Z.ProverRwRngMaterialInvariant
