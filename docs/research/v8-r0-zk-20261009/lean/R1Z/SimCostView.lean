import R1Z.SimulatorR1
import R1Z.SimCostWriter

/-! Abstract stage assembly of the actual simE formula. Stage implementations
are data with proved value/work laws. This file supplies their composition,
not unproved concrete stage instances or arbitrary callback tariffs. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.SimCostView
open R0P R0Z.JointView R0Z.RefPayload R0Z.Shift R1Z.Batched R1Z.SimCostWriter
variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}
variable (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F)
  (outputs : Statement K CommitHandle → Challenges K → Aux) (x : Statement K CommitHandle)

/-- The five independent implementation obligations for the view. Uniform
sampling, predicate/retry and wire encoding belong to ideal preparation. -/
structure Stages (R M A S D : Nat) where
  reference : Stage (fun ch : Challenges K => refPayload (Bat := R1Bat) x.1 B ch) R
  mask : Stage (fun ct : Challenges K × Tape K F =>
    R0Z.D12.A (Bat := R1Bat) π B ct.1 (R0Z.Partition.equiv.symm ct.2)) M
  add : Stage (fun p : R0Z.HonestView.Payload K R1Bat × R0Z.HonestView.Payload K R1Bat => p.1+p.2) A
  shifted : Stage (fun cp : Challenges K × R0Z.HonestView.Payload K R1Bat =>
    shift x.1 B cp.1 cp.2) S
  metadata : Stage (R0Z.ZkStatement.metadata outputs x) D

variable {R M A S D : Nat}

def run (st : Stages π B outputs x R M A S D) (ch : Challenges K) (t : Tape K F) :
    Costed (View K CommitHandle Aux R1Bat) :=
  bind (st.reference.run ch) fun ref =>
  bind (st.mask.run (ch,t)) fun mask =>
  bind (st.add.run (ref,mask)) fun sum =>
  bind (st.shifted.run (ch,sum)) fun value =>
  bind (st.metadata.run ch) fun md => SimCostWriter.pure (md,value)

theorem run_erase (st : Stages π B outputs x R M A S D)
    (ch : Challenges K) (t : Tape K F) :
    (run π B outputs x st ch t).1 = simE (Bat := R1Bat) π B outputs x ch t := by
  simp only [run, erase_bind, SimCostWriter.pure, st.reference.erase, st.mask.erase,
    st.add.erase, st.shifted.erase, st.metadata.erase]
  rfl

theorem run_bound (st : Stages π B outputs x R M A S D)
    (ch : Challenges K) (t : Tape K F) :
    (run π B outputs x st ch t).2 ≤ R+M+A+S+D := by
  have hr := st.reference.bound ch
  have hm := st.mask.bound (ch,t)
  have ha := st.add.bound ((st.reference.run ch).1,(st.mask.run (ch,t)).1)
  have hs := st.shifted.bound (ch,(st.add.run ((st.reference.run ch).1,(st.mask.run (ch,t)).1)).1)
  have hd := st.metadata.bound ch
  simp only [run, cost_bind, SimCostWriter.pure]
  omega

#print axioms run_erase
#print axioms run_bound
end R1Z.SimCostView
