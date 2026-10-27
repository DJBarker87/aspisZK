import R1Z.PV_L2_F3CompletionLaw
import R1Z.PV_L2_F3Disintegration
import R1Z.SimulatorR1
import R1Z.QueryScanIdealHistory

/-! Actual owned-decoder quotient/count law through witness absorption to
unchanged simE. The common None explicitly marks source decoder exhaustion;
this is not a native full-L1/refill/ROM event join or a new error allowance. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_L2_F3Absorption
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbortBounds R0Z.HvzkV R0Z.RefPayload
  R1Z.Batched R1Z.MaskImageVR1 R1Z.PredicateR1 R1Z.SimulatorR1
  R1Z.ProverCommitWordCarrier R1Z.ProverCommitSourceDecoder R1Z.ProverCommitTapeCompletion
  R1Z.PV_L2_F3Tape R1Z.PV_L2_F3Disintegration R1Z.PV_L2_F3CompletionLaw
attribute [local instance] Classical.propDecidable
attribute [local irreducible] sourceBase L₁ L₂ E₁ E₂
variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]
local notation "F" => sourceBase (K := K)

theorem mean_congr_instances {A : Type} {fin1 fin2 : Fintype A}
    (f g : A → ℚ) (hfg : ∀ a, f a = g a) : @mean A fin1 f = @mean A fin2 g := by
  have heq : f = g := funext hfg
  subst g
  exact QueryScanIdealHistory.mean_fintype_transport fin1 fin2 f

def sourceView (h : HonestProver K) (basis : PackBasis (sourceBase (K := K)))
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (w : h.Instance) (ch : Challenges K) (input : Inputs) (spare : Tape K F) : Option (View K CommitHandle Aux R1Bat × History) :=
  (observed (K := K) input).map (fun p =>
    (view h basis outputs x w ch (complete p.1 (padding spare)),p.2))

def simView (h : HonestProver K) (basis : PackBasis (sourceBase (K := K)))
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (ch : Challenges K) (input : Inputs) (spare : Tape K F) : Option (View K CommitHandle Aux R1Bat × History) :=
  (observed (K := K) input).map (fun p => (simE h.transport basis outputs x ch spare,p.2))


/-- Full scalar-count arrays remain paired with the hidden honest view. The
hypotheses are the existing P_R1/VR1 absorption guards, not trace agreement. -/
theorem source_count_absorption (h : HonestProver K) (basis : PackBasis (sourceBase (K := K)))
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (w : h.Instance) (ch : Challenges K) (hB : R0Z.K4.PackField basis)
    (hpub : PublicBase F x.1) (hs : R0Z.HonestValidity.BuilderSoundOn h basis x)
    (hP : P_R1 h.transport basis hB ch) (hV : VR1 h ch w) (hw : h.public w=x.1)
    (test : Option (View K CommitHandle Aux R1Bat × History) → ℚ) :
    mean (fun p : Inputs × Tape K F => test (sourceView h basis outputs x w ch p.1 p.2)) =
      mean (fun p : Inputs × Tape K F => test (simView h basis outputs x ch p.1 p.2)) := by
  rw [LawTransport.mean_product (f := fun p : Inputs × Tape K F =>
    test (sourceView h basis outputs x w ch p.1 p.2)),
    LawTransport.mean_product (f := fun p : Inputs × Tape K F =>
    test (simView h basis outputs x ch p.1 p.2))]
  have left : (fun input : Inputs => mean (fun spare : Tape K F =>
      test (sourceView h basis outputs x w ch input spare))) =
      (fun input => match observed (K := K) input with
       | none => test none
       | some (a,history) => mean (fun spare : Tape K F =>
          test (some (view h basis outputs x w ch (complete a (padding spare)),history)))) := by
    funext input
    cases ho : observed (K := K) input <;>
      simp only [sourceView,ho,Option.map_none,Option.map_some,mean_const']
  have right : (fun input : Inputs => mean (fun spare : Tape K F =>
      test (simView h basis outputs x ch input spare))) =
      (fun input => match observed (K := K) input with
       | none => test none
       | some (_,history) => mean (fun spare : Tape K F =>
          test (some (simE h.transport basis outputs x ch spare,history)))) := by
    funext input
    cases ho : observed (K := K) input <;>
      simp only [simView,ho,Option.map_none,Option.map_some,mean_const']
  rw [left,right]
  let realKernel (a : SourceTape K F) (history : History) := mean (fun spare : Tape K F =>
    test (some (view h basis outputs x w ch (complete a (padding spare)),history)))
  let idealKernel (_ : SourceTape K F) (history : History) := mean (fun spare : Tape K F =>
    test (some (simE h.transport basis outputs x ch spare,history)))
  have fibres : ∀ history a b,
      (Finset.univ.filter (fun input => observed (K := K) input = some (a,history))).card =
        (Finset.univ.filter (fun input => observed (K := K) input = some (b,history))).card := by
    intro history a b
    convert observed_fibres (K := K) a b history using 1 <;>
      apply congrArg Finset.card <;> ext input <;>
        simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  have means : ∀ history, mean (fun a => realKernel a history) = mean (fun a => idealKernel a history) := by
    intro history
    calc
      _ = mean (fun p : SourceTape K F × Tape K F =>
        test (some (view h basis outputs x w ch (complete p.1 (padding p.2)),history))) :=
          (LawTransport.mean_product _).symm
      _ = mean (fun t : Tape K F => test (some (view h basis outputs x w ch t,history))) :=
          complete_uniform (K := K) 
            (fun t => test (some (view h basis outputs x w ch t,history)))
      _ = mean (fun t : Tape K F => test (some (simE h.transport basis outputs x ch t,history))) :=
          LawTransport.mean_eq_of_equalLaws _ _ (fun v => test (some (v,history)))
            (hvzk_R1S h basis hB outputs x hpub hs w ch hP hV hw)
      _ = _ := (mean_const' _).symm

  have core := conditional_kernel (observed (K := K)) (by
    intro history a b
    convert fibres history a b using 1 <;>
      apply congrArg Finset.card <;> ext input <;>
        simp only [Finset.mem_filter,Finset.mem_univ,true_and]) realKernel idealKernel (test none) means
  dsimp only [realKernel,idealKernel] at core
  convert core using 1 <;>
    (apply mean_congr_instances; intro input; cases observed (K := K) input with
     | none => rfl
     | some pair => apply mean_congr_instances; intro spare; rfl)

#print axioms mean_congr_instances
#print axioms source_count_absorption
end R1Z.PV_L2_F3Absorption
