import NNH_HostSeed
import NNH_PreflightEnv
import NNH_StateSelect
import NNE_RecordSig
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_HostCtx
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
/-- Oracle-independent retained data. Dictionary/hashv/syscall are instantiated,
not retained binders. L/sdk/copy/std are parameters of the host family. -/
structure Fixed where
 pda : List RSL.Bytes → RSL.B32 → Option RSL.B32
 clock : Except RSL.ProgramError UInt64
 reservation : NP6_StdModel.Reservation
 indexError : NFN_NEW_GeometryDictionary.CE
 root : Array U8 32#usize
 length : U32
 prior : Program Bytes State Unit
 words : CanonicalCutEnrichedTranscript.Words
 D : LiteralByteProtocol.Decoder
 a : SCE_Experiment.Adversary Bool
 Q0 : Nat
 Q1 : Nat
/-- Unrestricted per-world retained data. Admission and persistence are
world predicates, so build does not require them for arbitrary input pairs. -/
structure World (W Tx : Type) where
 w1 : W
 w2 : W
 saved : alloc.vec.Vec U8
 post1 : Heap (Nat → Record)
 post2 : Heap (Nat → Record)
 p : CPG_Projection.Observations Tx Bool
 t : Tx
 u : Tx
 actions : List (CPP_BankState.Action Bool)
structure Ctx (W Tx : Type) where
 fixed : Fixed
 world : World W Tx
 sha256 : Bytes → State
 i : GExq_AccountExperiment.FirstInputs Bool
 j : GExq_AccountExperiment.SecondInputs Bool
abbrev envOf {W Tx : Type} (c : Ctx W Tx) : RSL.Env :=
 DGP_HostDigest.envInst c.sha256 c.fixed.pda c.fixed.clock c.fixed.reservation
abbrev missingLit {W Tx : Type} (c : Ctx W Tx) :=
 NNH_Tx2Configuration.select (NNH_CorrectConfiguration.residual NNH_HostSeed.m0 (envOf c)) (envOf c)
/-- The headline missing binder is substituted literally (ruling s).
It cannot be a Type-1 dictionary field of TAS's Type-valued Ctx. -/
abbrev missing {W Tx : Type} (c : Ctx W Tx) := missingLit c
def Exhibited {W Tx : Type} (c : Ctx W Tx) : Prop := (missing c) = missingLit c
abbrev base {W Tx : Type} (c : Ctx W Tx) :=
 IDa_Deployed.deployedConfiguration (missing c) c.fixed.indexError c.fixed.reservation
abbrev configuration {W Tx : Type} (c : Ctx W Tx) :=
 FIp_Install.configuration c.fixed.indexError (base c) c.fixed.reservation
abbrev sdk {W Tx : Type} (c : Ctx W Tx) := DrvC_Installation.sdk (configuration c)
abbrev model1 {W Tx : Type} (c : Ctx W Tx) : S2W_ExtractionBoundary.First :=
 AdapterRw.r1_pool_adapter.owned.stage1_owned (sdk c)
abbrev model2 {W Tx : Type} (c : Ctx W Tx) : S2W_ExtractionBoundary.Second :=
 AdapterRw.r1_pool_adapter.owned.stage2_owned (sdk c)
abbrev hashv {W Tx : Type} (c : Ctx W Tx) := DGP_HostDigest.hashvInst c.sha256

theorem exhibited {W Tx : Type} (c : Ctx W Tx) : Exhibited c := rfl

theorem env_unique {W Tx : Type} (c : Ctx W Tx) (env : RSL.Env)
 (h : NNH_HostEnv.EnvRep (DGP_HostDigest.shaReply c.sha256) c.fixed.pda
  c.fixed.clock c.fixed.reservation env) : env = envOf c :=
 NNH_PreflightEnv.unique _ _ _ _ env h

theorem extraction {W Tx : Type} (c : Ctx W Tx) :
 S2W_DigestExtraction.AeneasExtraction (sdk c) (model1 c) (model2 c) (hashv c) :=
 ⟨fun _ _ _ => rfl, fun _ _ _ _ => rfl,
  DGP_HostDigest.digestSource NNH_HostSeed.m0 c.sha256 c.fixed.pda c.fixed.clock
   c.fixed.reservation c.fixed.indexError⟩
#print axioms exhibited
#print axioms env_unique
#print axioms extraction
end AspisR1.NNH_HostCtx
end
