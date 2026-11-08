/-
NFB_NMFBHost: host spelling of the remaining NMF_B field and of each missing
obligation named in NFB_NMFB (host recipe).

NOT COMPILED LOCALLY: its imports (NNH_/NNC_/LIBB_/Aeneas) exist only in the
NNH build workspace on the build host.  Recipe: nfb_host_recipe.sh.  Until a
host receipt exists, nothing in this file is evidence; it pins statements.
Target not yet established.  No sorry, no axiom declaration.

Statements are against branch codex/cx-integrate-20261107 at e3630958583
(NNH run 5 final, S5 roots L803-L842).  Every `def ... : Prop` below is an
OBLIGATION, never a hypothesis of a final theorem.

Field.  `Remaining` is `RSL.NFB.Remaining` (= the type of
`RSL.EVB.NNC_NMFPrimeB.root0_or_rec`) at
  S := NNH_G1aEnv.sig (S_host L0 copy std),  I := NNH_064Install.install I0,
  g := NNH_G1aEnv.field _ I0 (so g.w = NNH_064WeakField.w, the w that
  NNH_HostNativeCuts.produce's `ref` uses),  R := recSig' (NNH_HostExec.recSig
  re-typed at the same Ctx).

Delivered pieces and how they enter (NFB_NMFB.Delivered):
  produce     NNH_HostNativeCuts.produce c post events ref accepted game, where
              `ok2 : ∃ s', (I.entry (args2 c) (state2 c) (env2 c)).exit = .ret (.ok (), s')`
              gives post := s' and events := (I.entry …).events, and
              `ref := weak (args2 c) (state2 c) (env2 c)` rewritten by Obs eta
              (`I.entry … = ⟨.ret (.ok (), s'), (I.entry …).events⟩`).  args2/state2/
              env2 at S_host are NNE_EntryArgs.args c.j.entry 7 …, NNE_Entry.state
              c.j.entry 0 and envOf c, all by rfl.  game at S_host is
              `Game ∧ retained`; produce consumes the whole conjunction.
  complete    record constructor of NNH_NMFPrime.Packet with A := the account
              program's output type, Ambient := Unit, X := Unit; fields exactly as
              in NNC_NMFB.root0_or_rec's call of NNC_RecRoot.root0_or_rec_collision
              (source := ARX_LocalCharge.bounded (ART_PartialAccount.account
              (configuration c) (hashv c) copy NNE_AbortIndicator.allocator
              CPH_Program.verifier (NNH_StateNormalize.normalize c.fixed.a))
              (c.fixed.Q0+c.fixed.Q1), project := ARQ_Observer.project,
              select := ARQ_Observer.select (configuration c) CPH_Program.verifier,
              budget := fun K => (VerifierCallBudget.firstReads_le_length _ _).trans
              (ARX_LocalCharge.budget _ _ K), H := c.sha256, ops := sdk c,
              id := CPH_Program.verifier, e1 := c.i.entry, e2 := c.j.entry,
              data2 := c.j.data, slot := c.j.slot, selects := the SelectsPair
              premise (definitionally recSig's SelectsPair, NNH_HostExec), the
              cut fields f s cuts origin writerRoot persisted writerHeader domain
              records events native, d := LIBB_PartitionEnv.digest (env2 c),
              hash := (), world := NNH_064Install.frame, oracle := M2e).
              Associated c p := the conjunction of those field equalities.
  alternative NNH_NMFPrime.alternative.
  eventImage  NNH_HostRecorderEvent.same (Iff.rfl) after rewriting by Associated.
-/
import NNH_HostNativeHeader
import NNH_HostRecorderEvent
import NNH_HostClockFinding
import NNH_NMFPrime
import NNH_G1aEnv
import NFB_NMFB
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFB_NMFBHost
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open MultiproofConeCanonical S2W_NativeConsolidation
open NNH_HostCtx NNH_LiteralHost NNH_Libraries
variable {W Tx : Type} (L0 : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)

/-- The host signature carrying the G1a reader header. -/
abbrev S (L0 : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy) : RSL.TAS.Sig :=
 NNH_G1aEnv.sig (S_host (Tx := Tx) L0 copy std)

/-- NNH_HostExec.recSig at the same context type. -/
def recSig' : RSL.EVB.RecSig (S (Tx := Tx) L0 copy std) where
 Realizes := (NNH_HostExec.recSig (Tx := Tx) L0 copy std).Realizes
 EventRec := (NNH_HostExec.recSig (Tx := Tx) L0 copy std).EventRec
 SelectsPair := (NNH_HostExec.recSig (Tx := Tx) L0 copy std).SelectsPair

/-- THE REMAINING NMF_B FIELD at the literal host. -/
abbrev Remaining (I0 : RSL.TAS.Impl L V0 VL) : Prop :=
 RSL.NFB.Remaining (S (Tx := Tx) L0 copy std) L D V0 VL P C (NNH_064Install.install I0)
  (NNH_G1aEnv.field _ I0) (recSig' (Tx := Tx) L0 copy std)

/-! ## M1 clock binding -/

/-- M1 is refuted at the CURRENT host (NNH_HostClockFinding, L798): with
env2 := envOf c the TX2 clock slot is fx.clock, independent of c.j.slot. -/
theorem M1_refuted (c : Ctx W Tx) :
 NNH_HostWeak241.clock (envOf (NNH_HostClockFinding.different c)) ≠
  (NNH_HostClockFinding.different c).j.slot := by
 intro h
 apply NNH_HostClockFinding.mismatch c
 rw [← h]
 exact (NNH_HostWeak241.clock_reply _).symm

/-- M1 correction: the TX2 environment carries the clock reply of the
selected slot (TAS Sig.env2 docstring; NNH_HostEnv.environment docstring
"TX2 supplies its actual clock reply").  Fixed.clock is removed. -/
def env2 (c : Ctx W Tx) : RSL.Env :=
 DGP_HostDigest.envInst c.sha256 c.fixed.pda
  (NND_Carrier.reply NND_Carrier.slot c.j.slot) c.fixed.reservation

/-- M1a: slot roundtrip at the corrected environment
(expected: `cases` on the slot reply, NND_Carrier.slot_back/error_back). -/
def M1a : Prop := ∀ c : Ctx W Tx, NNH_HostWeak241.clock (env2 c) = c.j.slot

/-- M1b: the literal missing instance does not read the clock, so cfg, sdk,
model1/2, E_rec (NNH_HostExec.ERec) and the recorder are unchanged when
`envOf` is replaced by `env2`.  Grep at e3630958583 finds no `.clock` read in
NNH_Tx2ModelSlots, NNH_Tx2SourceConfiguration, NNH_MRegistryOps,
NNH_LaneModel, NGL_CheckpointModel, LIB_Deployed; prove it by a factorisation
through (sha256, pda, reservation), NOT by whole-dictionary rfl (retired L559 shape). -/
def M1b : Prop :=
 ∀ (H : Bytes → State) (pda : List RSL.Bytes → RSL.B32 → Option RSL.B32)
  (k k' : Except RSL.ProgramError UInt64) (r : NP6_StdModel.Reservation),
  NNH_Tx2Configuration.select
   (NNH_CorrectConfiguration.residual NNH_HostSeed.m0 (DGP_HostDigest.envInst H pda k r))
   (DGP_HostDigest.envInst H pda k r) =
  NNH_Tx2Configuration.select
   (NNH_CorrectConfiguration.residual NNH_HostSeed.m0 (DGP_HostDigest.envInst H pda k' r))
   (DGP_HostDigest.envInst H pda k' r)

/-- M1c (signature): S_host.EnvRep c env := NNH_HostEnv.EnvRep
(DGP_HostDigest.shaReply c.sha256) c.fixed.pda (NND_Carrier.reply NND_Carrier.slot c.j.slot)
c.fixed.reservation env, env1 = env2 := env2.  M1d (rebuild, no new
mathematics): NNH_HostWeak241/HostNativeCuts/HostNativeHeader/HostExec/
HostRecorderEvent/LiteralHost.a0 restated at env2; their proofs are generic
in env except through `envOf c`, which M1b identifies. -/
def M1c (c : Ctx W Tx) (env : RSL.Env) : Prop :=
 NNH_HostEnv.EnvRep (DGP_HostDigest.shaReply c.sha256) c.fixed.pda
  (NND_Carrier.reply NND_Carrier.slot c.j.slot) c.fixed.reservation env

/-! ## M2 native records at the headline oracle -/

/-- M2: the SAME weak 064 native outcome, indexed by the partitioned oracle,
is a native outcome at the headline oracle H.  Sub-obligations:
 M2a returning C04 domain at the SAME outer064 occurrence without Root0
     (NNH_NativeOracleReply/Window take the closed child's domain);
 M2b aborting dependent windows (NativeOracleBatch.aborting is the loop level);
 M2c lift of NativeOracleDetail.transport through the occurrence list;
 M2d lift through common/native parent to NMN_064.Native.
Global oracle equality is NOT available and must not be asserted. -/
def M2 : Prop :=
 ∀ (H : Bytes → State) (pda : List RSL.Bytes → RSL.B32 → Option RSL.B32)
  (k : Except RSL.ProgramError UInt64) (r : NP6_StdModel.Reservation)
  (pub proof ck : Slice U8)
  (records : List (NLT_NativeInvocation.Occurrence
   (LIBB_PartitionEnv.H (DGP_HostDigest.envInst H pda k r))
   (LIBB_PartitionEnv.digest (DGP_HostDigest.envInst H pda k r)) ()))
  (events : List (NLW_Full064.Event Unit Unit)),
  NNC_064Weak.Domain (NLW_Full064.Args.mk
   (LIBB_PartitionEnv.digest (DGP_HostDigest.envInst H pda k r)) pub proof ck ()) →
  NMN_064.Native (LIBB_PartitionEnv.H (DGP_HostDigest.envInst H pda k r))
   ⟨⟨LIBB_PartitionEnv.digest (DGP_HostDigest.envInst H pda k r),pub,proof,ck,()⟩,
    NNH_064Install.frame⟩ (.common (.resolved (.ok (.Ok ())) records)) events →
  ∃ (records' : List (NLT_NativeInvocation.Occurrence H
     (LIBB_PartitionEnv.digest (DGP_HostDigest.envInst H pda k r)) ()))
   (events' : List (NLW_Full064.Event Unit Unit)),
   NMN_064.Native H
    ⟨⟨LIBB_PartitionEnv.digest (DGP_HostDigest.envInst H pda k r),pub,proof,ck,()⟩,
     NNH_064Install.frame⟩ (.common (.resolved (.ok (.Ok ())) records')) events'

/-- M2e: the partition digest obeys the oracle law at H (expected closable
by the digest half of NNH_HostOracle.partition_oracle's proof). -/
def M2e : Prop :=
 ∀ (H : Bytes → State) (pda : List RSL.Bytes → RSL.B32 → Option RSL.B32)
  (k : Except RSL.ProgramError UInt64) (r : NP6_StdModel.Reservation),
  CheckpointBytes5Inputs.Oracle
   (VTop_Checkpoint.digest (LIBB_PartitionEnv.digest (DGP_HostDigest.envInst H pda k r))) () H

/-! ## M3 root image -/

/-- M3: Root0 of the packet's SecondCut is S_host.Root0Native at the
selected entry.  Route: an NNH_WeakReaderCuts/NNC_SourceCuts version of
NNC_WeakR0Rep.at_entry, plus LIBB_V2Star.library.Root0 = NNC_ByteCarriers.Root0. -/
def M3 : Prop :=
 ∀ (c : Ctx W Tx) (f : FirstCut) (s : SecondCut),
  NNC_SourceCuts.Cuts (sdk c) c.i.entry.first (c.j.entry.second secondSizes)
   c.world.saved f s →
  NLP_InputDomain.Root0 s.checkpoint s.proof →
  (S_host (Tx := Tx) L0 copy std).Root0Native c

#print axioms M1_refuted
end AspisR1.NFB_NMFBHost
end
