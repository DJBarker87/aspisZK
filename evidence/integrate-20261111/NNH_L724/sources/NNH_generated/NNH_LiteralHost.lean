import NNH_HostClaims
import NND_Carrier
import NNH_G1aEnv
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_LiteralHost
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_ReturnedCheckpoint S2W_CommittedCheckpoint S2W_WrapperLaws S2W_D189Consolidation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open NNH_HostCtx
variable {W Tx : Type}
variable (L : Library W (Nat → Record))
variable (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))

def runtime (c : Ctx W Tx) (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second) :=
 ARX_AdmittedRuntime.runtime (Tx := Tx) L copy NNE_AbortIndicator.allocator (base c)
  c.fixed.indexError c.fixed.reservation n1 n2 (hashv c) (NNH_StateNormalize.normalize c.fixed.a)
def bound (c : Ctx W Tx) (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second) : Prop :=
 F3T_RuntimeBound.failureModel (runtime L copy c n1 n2) ≤ F3T_Numeric.total (c.fixed.Q0+c.fixed.Q1) ∧
 (c.fixed.Q0+c.fixed.Q1 ≤ F3U_RangeEdges.maxQueries →
  F3T_RuntimeBound.failureModel (runtime L copy c n1 n2) ≤
   (c.fixed.Q0+c.fixed.Q1+1:Rat)*(1/(2:Rat)^100)) ∧
 (c.fixed.Q0+c.fixed.Q1=0 → F3U_Numeric.margin ≤
  1/(2:Rat)^100-F3T_RuntimeBound.failureModel (runtime L copy c n1 n2) ∧
  F3T_RuntimeBound.failureModel (runtime L copy c n1 n2) < 1/(2:Rat)^100)
def event (c : Ctx W Tx) (n1 : S2W_ExtractionBoundary.First) : Prop :=
 BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (c.fixed.Q0+c.fixed.Q1+2965)
  (eval c.sha256 (Hiq_RecordedJoint.program
   (F3X_Account.program (configuration c) (hashv c)
    (ARW_Induced.program n1 copy NNE_AbortIndicator.allocator CPH_Program.verifier
     (NNH_StateNormalize.normalize c.fixed.a))) F3X_Projection.project
   (fun _ => P2P_NativeSelection.pair (sdk c) CPH_Program.verifier
    c.i.entry c.j.entry c.j.data c.j.slot)))
/-- Internal seed only. Physical fields below replace the marked neutral seed
fields before S_host is exposed; no theorem consumes this seed signature. -/
def seed : RSL.TAS.Sig where
 Ctx := Ctx W Tx
 First := S2W_ExtractionBoundary.First
 Second := S2W_ExtractionBoundary.Second
 model1 := model1
 model2 := model2
 Exhibited := Exhibited
 Extraction := fun c n1 n2 => S2W_DigestExtraction.AeneasExtraction (sdk c) n1 n2 (hashv c)
 Accepted1 := fun _ _ => False
 Accepted2 := fun _ _ => False
 GameFrame := fun _ => False
 Recorded1 := fun _ _ _ => False
 Recorded2 := fun _ _ _ => False
 Game := fun _ _ _ => False
 mkGame := fun _ _ _ h => False.elim h
 Queries := fun c n1 => ∀ H,
  (ARW_Induced.issued n1 copy NNE_AbortIndicator.allocator CPH_Program.verifier
   (NNH_StateNormalize.normalize c.fixed.a) H).length ≤ c.fixed.Q0+c.fixed.Q1
 Concl := NNH_HostClaims.conclusion L copy
 Bound := bound L copy
 Event := event copy
 args1 := fun c => NNE_EntryArgs.args c.i.entry 3 CPH_Program.verifier c.i.data
 args2 := fun c => NNE_EntryArgs.args c.j.entry 7 CPH_Program.verifier c.j.data
 state1 := fun c => NNE_Entry.state c.i.entry 0
 state2 := fun c => NNE_Entry.state c.j.entry 0
 env1 := envOf
 env2 := envOf
 Out1 := fun c => NNE_PhysicalAccepted.Out1 c.world.saved
 Out2 := fun _ _ => True
 EnvRep := fun c => NNH_HostEnv.EnvRep (DGP_HostDigest.shaReply c.sha256)
  c.fixed.pda c.fixed.clock c.fixed.reservation
 env1_rep := fun c => NNH_HostEnv.environment_rep _ _ _ _
 env2_rep := fun c => NNH_HostEnv.environment_rep _ _ _ _
 TraceRep := fun _ _ => False
 Root0Native := fun c => NNH_Libraries.V0.Root0
  (S2W_ReturnedCheckpoint.nativeBytes (c.j.entry.buffers (c.j.entry.handles 6).1))
  (RSL.slice (S2W_ReturnedCheckpoint.nativeBytes (c.j.entry.buffers (c.j.entry.handles 0).1)) RSL.AFTERSTATE_BYTES RSL.PROOF_ACCOUNT_BYTES)
 readerHeader := NNH_G1aEnv.header
 ModelRet1 := fun _ _ _ => True
 ModelRet2 := fun _ _ _ => True

def hostRuntime : NNH_HostEnv.Runtime (Ctx W Tx) where
 sha := fun c => DGP_HostDigest.shaReply c.sha256
 pda := fun c => c.fixed.pda
 clock := fun c => c.fixed.clock
 reservation := fun c => c.fixed.reservation
abbrev envSig := NNH_HostEnv.install (seed (Tx := Tx) L copy) (hostRuntime (W := W) (Tx := Tx))

def data (std : S2W_TrustedStd.TrustedStd copy) : NNE_AcceptanceSig.Data (envSig (Tx := Tx) L copy) where
 err := NND_Carrier.error
 invalid := rfl
 native1 := id
 native2 := id
 e1 := fun c => c.i.entry
 e2 := fun c => c.j.entry
 program := fun _ => CPH_Program.verifier
 data1 := fun c => c.i.data
 data2 := fun c => c.j.data
 slot := fun c => c.j.slot
 saved := fun c => c.world.saved
 copy := copy
 std := std

def record : NNE_RecordSig.Data (envSig (Tx := Tx) L copy) where
 Tx := Tx
 p := fun c => c.world.p
 t := fun c => c.world.t
 u := fun c => c.world.u
 actions := fun c => c.world.actions

/-- Original runtime trust facts, retained at their selected entries.
They enter the actual-run frame, not the total arbitrary-input constructor. -/
def retained (c : Ctx W Tx) : Prop :=
 RuntimeEntrypointAdmission L c.i.entry c.world.w1 3 ∧
 RuntimeEntrypointAdmission L c.j.entry c.world.w2 7 ∧
 CPR_DataPersistence.TwoTransactionLaw (CPG_Projection.adjacent c.world.p)
  (CPG_Projection.ordinary c.world.p (Hist_Nonvacuity.key 0#u8))
  (CPG_Projection.before c.world.p) (CPG_Projection.tentative c.world.p)
  (CPG_Projection.success c.world.p) (CPG_Projection.loaded c.world.p)

def S_host (std : S2W_TrustedStd.TrustedStd copy) : RSL.TAS.Sig :=
 let S := NNE_RecordSig.physical (envSig (Tx := Tx) L copy) (data (Tx := Tx) L copy std) (record (Tx := Tx) L copy)
 {S with
  GameFrame := fun c => S.GameFrame c ∧ retained L c
  Game := fun c n1 n2 => S.Game c n1 n2 ∧ retained L c
  mkGame := fun c n1 n2 f r1 r2 => ⟨S.mkGame c n1 n2 f.1 r1 r2,f.2⟩}

def a0 (std : S2W_TrustedStd.TrustedStd copy) : RSL.TAS.A0_Digest (S_host (Tx := Tx) L copy std) where
 extraction := fun c _ => NNH_HostCtx.extraction c

theorem account_at (e : Entry) (n k : Nat) (hk : k < n)
 (p : S2W_ExtractionBoundary.Program) (bs : Slice U8) :
 (NNE_EntryArgs.args e n p bs).accounts[k]? = some (NNE_Entry.account e k) := by
 change ((List.range n).map (NNE_Entry.account e))[k]? = _
 rw [List.getElem?_map, List.getElem?_range hk]
 rfl

def r0 (std : S2W_TrustedStd.TrustedStd copy) :
 RSL.TAS.NNC_R0Rep (S_host (Tx := Tx) L copy std) NNH_Libraries.V0 where
 rep := by
  intro c a0 a6 h _ h0 h6 _ _
  have z := account_at c.j.entry 7 0 (by decide) CPH_Program.verifier c.j.data
  have s := account_at c.j.entry 7 6 (by decide) CPH_Program.verifier c.j.data
  have ez : a0 = NNE_Entry.account c.j.entry 0 := Option.some.inj (h0.symm.trans z)
  have es : a6 = NNE_Entry.account c.j.entry 6 := Option.some.inj (h6.symm.trans s)
  subst a0; subst a6
  exact h
#print axioms account_at
#print axioms S_host
#print axioms a0
#print axioms r0
end AspisR1.NNH_LiteralHost
end
