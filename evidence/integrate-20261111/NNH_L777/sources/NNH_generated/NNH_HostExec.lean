import NNH_LiteralHost
import TAS_TopB
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_HostExec
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_ReturnedCheckpoint S2W_CommittedCheckpoint S2W_WrapperLaws
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open GExq_AccountExperiment NNH_HostCtx NNH_LiteralHost
variable {W Tx : Type} (L : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)

def post (i : FirstInputs Bool) (saved : alloc.vec.Vec U8) : Heap (Nat → Record) :=
 writeBracket i.entry.heap 2 0 0 (source (nativeBytes saved))
def ERec (fx : Fixed) (H : Bytes → State) : Prop :=
 let env := DGP_HostDigest.envInst H fx.pda fx.clock fx.reservation
 let m := NNH_Tx2Configuration.select (NNH_CorrectConfiguration.residual NNH_HostSeed.m0 env) env
 BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (fx.Q0+fx.Q1+2965)
  (eval H (NNH_RecordedCharge.recorder copy
   (IDa_Deployed.deployedConfiguration m fx.indexError fx.reservation)
   fx.indexError fx.reservation (DGP_HostDigest.hashvInst H) fx.a (fx.Q0+fx.Q1)))

def recSig : RSL.EVB.RecSig (S_host (Tx := Tx) L copy std) where
 Realizes := fun c =>
  (eval c.sha256 (NNH_StateNormalize.normalize c.fixed.a).first).2 = c.i ∧
  (eval c.sha256 ((NNH_StateNormalize.normalize c.fixed.a).second c.i c.world.saved
   (post c.i c.world.saved) true)).2 = c.j
 EventRec := fun c => ERec copy c.fixed c.sha256
 SelectsPair := fun c =>
  ARQ_Observer.select (configuration c) CPH_Program.verifier
   (eval c.sha256 (NNH_RecordedCharge.source copy (base c) c.fixed.indexError
    c.fixed.reservation (hashv c) c.fixed.a (c.fixed.Q0+c.fixed.Q1))).2 =
  P2P_NativeSelection.pair (sdk c) CPH_Program.verifier c.i.entry c.j.entry c.j.data c.j.slot

def exec : RSL.TASB.ExecB (S_host (Tx := Tx) L copy std) (recSig L copy std) where
 Fixed := Fixed
 World := World W Tx
 Oracle := Bytes → State
 In1 := FirstInputs Bool
 In2 := SecondInputs Bool
 first := fun fx H => NNH_StateNormalize.firstAt fx.a H
 second := fun fx w H i => NNH_StateNormalize.secondTop
  (eval H (fx.a.second i w.saved (post i w.saved) true)).2
 build := fun fx w H i j => ⟨fx,w,H,i,j⟩
 realizes_mk := by
  intro fx w H i j
  change ((eval H (NNH_StateNormalize.normalize fx.a).first).2 = i ∧
   (eval H ((NNH_StateNormalize.normalize fx.a).second i w.saved (post i w.saved) true)).2 = j) ↔ _
  rw [NNH_StateNormalize.first_eval,NNH_StateNormalize.second_eval]
  exact Iff.rfl
 exhibited_mk := fun _ _ _ _ _ => rfl
 QueriesF := fun fx => ∀ J K,
  (ARW_Induced.issued
   (AdapterRw.r1_pool_adapter.owned.stage1_owned
    (NNH_CorrectConfiguration.sdk NNH_HostSeed.m0
     (DGP_HostDigest.envInst J fx.pda fx.clock fx.reservation) fx.indexError fx.reservation))
   copy NNE_AbortIndicator.allocator CPH_Program.verifier
   (NNH_StateNormalize.normalize fx.a) K).length ≤ fx.Q0+fx.Q1
 queries_mk := fun _ _ H _ _ h => h H
 ERec := ERec copy
 eventRec_mk := fun _ _ _ _ _ => Iff.rfl
theorem recSelect : RSL.EVB.RecSelect (S_host (Tx := Tx) L copy std) (recSig L copy std) where
 selects := by
  intro c _ ext ac queries realizes
  rcases c with ⟨fx,w,H,i,j⟩
  change (eval H (NNH_StateNormalize.normalize fx.a).first).2 = i ∧
   (eval H ((NNH_StateNormalize.normalize fx.a).second i w.saved (post i w.saved) true)).2 = j at realizes
  rw [NNH_StateNormalize.first_eval,NNH_StateNormalize.second_eval] at realizes
  have hi : NNH_StateNormalize.firstAt fx.a H = i := realizes.1
  subst i
  have hj : NNH_StateNormalize.secondAt fx.a H w.saved
   (post (NNH_StateNormalize.firstAt fx.a H) w.saved) true = j := realizes.2
  subst j
  exact NNH_StateSelect.selects copy _ fx.indexError fx.reservation _ _ _ ext H H
   (DGP_HostDigest.p1 H) (DGP_HostDigest.syscall H) fx.a w.saved
   (post (NNH_StateNormalize.firstAt fx.a H) w.saved) ac fx.Q0 fx.Q1 queries

theorem environment_nonvacuous (c : Ctx W Tx) :
 (S_host L copy std).Exhibited c ∧ (S_host L copy std).EnvRep c (envOf c) :=
 ⟨rfl,NNH_HostEnv.environment_rep _ _ _ _⟩

#print axioms recSelect
#print axioms environment_nonvacuous
#print axioms recSig
#print axioms exec
end AspisR1.NNH_HostExec
end
