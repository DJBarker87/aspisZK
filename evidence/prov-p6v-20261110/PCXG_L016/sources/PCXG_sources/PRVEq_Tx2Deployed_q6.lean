-- PCVQ_ item (1): h18 and the deployed tx2 theorems with the Ext dependence made explicit (yDep) and every resume leaf related except the E decode link.
-- Hypothesis left: hE32 (frozen WideExact::from_le_bytes, as installed in op2, equals the checkpoint reader's decode_e_spec on 32-byte windows).
import Aeneas
import PRVEq_Tx2Deployed_q5
import PRVEq_Validate_q2
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
noncomputable section
namespace PCVQ_Tx2Deployed6
open VTop_Stages VTop_Stages.PRVFresh_VTop_l1 AspisR1 PCVN_Tx2Deployed PCVQ_Resumeq13 PCVQ_Tx2Deployedq5

/-- The E decode link: the op2 slot (the frozen wide parser behind the structural port) agrees with the checkpoint reader's decoder on every 32-byte window. -/
def E32 (d : VTop_Stages.Ops) : Prop :=
  ∀ b : Std.Array Std.U8 32#usize, d.op2 b.to_slice =
    (do let q ← OraclePortCkptAbi2Extracted.decode_e_spec b.to_slice
        ok (Option.map CheckpointBytes3Namespaces.fromE q))

section
variable (reserved : Bool) (d : VTop_Stages.Ops)

theorem leaf_e (hE : E32 d) {B : Type} (r : verifier.Reader)
    (K : core.result.Result aspis_core.field.wide_exact.WideExact VErr × verifier.Reader → Result B) :
    (verifier.Reader.e (xdep (yDep reserved d) d) r >>= K) =
      ((CheckpointBytes4Ops.ops reserved).readE r >>= fun p => K (phi p.1, p.2)) := by
  change (verifier.Reader.e (xdep (yDep reserved d) d) r >>= K) = (CheckpointBytes3Reader.readE r >>= fun p => K (phi p.1, p.2))
  unfold verifier.Reader.e CheckpointBytes3Reader.readE
  have hraw : verifier.Reader.raw 32#usize r = CheckpointBytes3Reader.raw 32#usize r := rfl
  rw [hraw]
  simp only [xdep, bind_assoc, bind_tc_ok, lift]
  congr 1; funext p
  rcases p with ⟨b, out⟩
  change ((do
      let o ← (xdep (yDep reserved d) d).aspis_core_field_wide_exact_WideExact_from_le_bytes b.to_slice
      let r ← core.option.Option.ok_or o AdapterRw.aspis_r1_cost_probe.verifier.Error.Checkpoint
      ok (r, out)) >>= K) = ((do
      let q ← OraclePortCkptAbi2Extracted.decode_e_spec b.to_slice
      ok (CheckpointBytes3Reader.optionE q, out)) >>= fun p => K (phi p.1, p.2))
  change ((do
      let o ← d.op2 b.to_slice
      let r ← core.option.Option.ok_or o AdapterRw.aspis_r1_cost_probe.verifier.Error.Checkpoint
      ok (r, out)) >>= K) = _
  rw [hE b]
  simp only [bind_assoc, bind_tc_ok]
  congr 1; funext q
  cases q <;> rfl

theorem leaves (hE : E32 d) : Leaves (xdep (yDep reserved d) d) (CheckpointBytes4Ops.ops reserved) where
  size := fun v => rfl
  tag := fun v => rfl
  final := fun v => rfl
  ne := fun {T U N} inst => rfl
  any := fun D it => leaf_any reserved d D it
  raw := fun n r => leaf_raw reserved n r
  k := fun {B} r K => leaf_k reserved d r K
  e := fun {B} r K => leaf_e reserved d hE r K
  validate := fun {B} q K => by
    rw [PCVQ_Validate2.validate_fresh q]
    simp only [bind_assoc, bind_tc_ok]
    congr 1; funext a
    cases a <;> rfl
  sem := fun {B} b a K => by
    simp only [xdep, yDep, bind_assoc, bind_tc_ok]
  weights := fun {B} b a w K => by
    simp only [xdep, yDep, bind_assoc, bind_tc_ok]
  zero := rfl
  filled := fun {H B} D n q K => leaf_filled reserved d D n q K

/-- h18, restated: the deployed op18 slot equals the fresh 4bb3b3f resume against the externals xdep (yDep ..) d, all variants and all inputs. -/
theorem h18 (hE : E32 d) :
    @Port4A_ReaderInstall.reader reserved = @verifier.resume (xdep (yDep reserved d) d) := by
  funext H D ck proof pub v hash
  have hs := resume_sim (xdep (yDep reserved d) d) (CheckpointBytes4Ops.ops reserved) (leaves reserved d hE)
    (fun v n h => Port4A_ReaderInstall.size_bound reserved v n h) D ck proof pub v hash
  unfold Sim at hs
  rw [hs]
  unfold Port4A_ReaderInstall.reader
  congr 1; funext out
  cases out <;> rfl
end

section
variable {F CE : Type} (inact : Slice Std.U8 → Result (Option aspis_core.field.wide_exact.WideExact))
  (mk : Option (verifier.Phase → Result Unit) → verifier.Phase → Result Unit) (reserved : Bool) (query : Port3_NativeQueryBody.Ops)
  (geo : Port3_NativeGeometryBody.Ops CE) (base : VTop_Stages.Ops)
  (finish : AspisR1Stage2.Stage2Finish.FinishOps F)

theorem h18_deployed (hE : E32 (Dep inact mk reserved query geo base finish)) :
    @(Dep inact mk reserved query geo base finish).op18 =
      @verifier.resume (xdep (yDep reserved (Dep inact mk reserved query geo base finish)) (Dep inact mk reserved query geo base finish)) := by
  rw [slot_op18]; exact h18 reserved _ hE

theorem deployed_tx2_common_q (hE : E32 (Dep inact mk reserved query geo base finish))
    {H : Type} (inst : aspis_core.digest.Digest32 H) (public_bytes proof checkpoint : Slice Std.U8) (hash : H)
    (obs : Option (verifier.Phase → Result Unit)) :
    verifier.candidate.tx2_common (xdep (yDep reserved (Dep inact mk reserved query geo base finish)) (Dep inact mk reserved query geo base finish))
        inst public_bytes proof checkpoint hash obs =
      VTop_Stages.verifier.candidate.tx2_common (Dep inact mk reserved query geo base finish) inst public_bytes proof checkpoint hash obs :=
  deployed_tx2_common inact mk reserved query geo base finish _ (h18_deployed inact mk reserved query geo base finish hE) inst public_bytes proof checkpoint hash obs

theorem deployed_tx2_authenticated_q (hE : E32 (Dep inact mk reserved query geo base finish))
    {H : Type} (inst : aspis_core.digest.Digest32 H) (public_bytes proof checkpoint : Slice Std.U8) (hash : H)
    (obs : Option (verifier.Phase → Result Unit)) :
    verifier.candidate.tx2_authenticated (xdep (yDep reserved (Dep inact mk reserved query geo base finish)) (Dep inact mk reserved query geo base finish))
        inst public_bytes proof checkpoint hash obs =
      VTop_Stages.verifier.candidate.tx2_authenticated (Dep inact mk reserved query geo base finish) inst public_bytes proof checkpoint hash obs :=
  deployed_tx2_authenticated inact mk reserved query geo base finish _ (h18_deployed inact mk reserved query geo base finish hE) inst public_bytes proof checkpoint hash obs
end

#print axioms leaf_e
#print axioms leaves
#print axioms h18
#print axioms h18_deployed
#print axioms deployed_tx2_common_q
#print axioms deployed_tx2_authenticated_q
end PCVQ_Tx2Deployed6
