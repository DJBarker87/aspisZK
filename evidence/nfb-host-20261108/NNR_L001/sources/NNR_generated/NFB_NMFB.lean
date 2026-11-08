/-
NFB_NMFB: the remaining NMF_B field, its exact statement, and the composition
of the merged S5 pieces up to four named missing obligations (stand-in level).

Target not yet established.  NMF_B is NOT delivered.  Core Lean plus
RSL_/TCK_/TAS_/TFM_/EVB_ only.  No sorry, no axiom declaration, no Root0
hypothesis, no hash-injectivity premise.

The remaining field is `RSL.EVB.NNC_NMFPrimeB S L D V0 VL P C I g R`, i.e.
`Remaining` below, at the literal host
  S := NNH_G1aEnv.sig (NNH_LiteralHost.S_host L copy std)  (readerHeader := header),
  I := NNH_064Install.install I0,  g := NNH_G1aEnv.field _ I0  (g.w = NNH_064WeakField.w),
  R := NNH_HostExec.recSig L copy std.
Its host spelling, and the host type of every missing lemma, are in
NFB_NMFBHost.lean (host recipe; not compiled locally).

`Shape` abstracts the host objects by the two indices the S5 pieces disagree
on: the oracle `h` that indexes the native 064 records, and the clock slot
`k` at which the TX2 origin fact is stated.

Delivered by merged S5/S6 pieces (`Delivered`), each naming its host term:
  produce     NNH_HostNativeCuts.produce: a cut packet with records at
              LIBB_PartitionEnv.H (env2 c) and origin at clock (env2 c);
  complete    the NNH_NMFPrime.Packet record constructor at oracle h, from a cut
              at slot c.j.slot, the SelectsPair premise and a digest oracle;
  alternative NNH_NMFPrime.alternative (via NNC_RecRoot.root0_or_rec_collision);
  eventImage  Iff.rfl, NNH_HostRecorderEvent.same (P4 at the host, L743).

Missing (`Missing`), exactly four obligations, none of them a hypothesis of
any final theorem:
  M1 clock      `NNH_HostWeak241.clock (S.env2 c) = c.j.slot`.  FALSE at the
                current literal host: NNH_HostClockFinding.admitted_environment
                (L798) exhibits Exhibited ∧ EnvRep ∧ clock ≠ slot.  It is a host
                signature correction, not a lemma to prove at the current host:
                env2 must carry the TX2 clock reply of the selected slot (the TAS
                Sig.env2 docstring and NNH_HostEnv.environment's docstring both
                say so).  Sub-obligations M1a-M1d in NFB_NMFBHost.lean.
  M2 lift       records/native transport from LIBB_PartitionEnv.H (env2 c) to
                c.sha256 at the SAME cut (f s cuts origin writerRoot writerHeader
                persisted domain are oracle-free and carried unchanged).
                Sub-obligations M2a-M2d (returning C04 domain at the same outer064
                occurrence without Root0; aborting dependent windows; occurrence
                list; outer NMN_064.Native outcome).  Pointwise inputs already
                compiled: NNH_NativeOracleSlots/Loop/Abort/Batch/Detail/Reply/
                Window (L834-L841).
  M2e oracle    CheckpointBytes5Inputs.Oracle (VTop_Checkpoint.digest
                (LIBB_PartitionEnv.digest (env2 c))) () c.sha256.  Expected to
                close by the second half of NNH_HostOracle.partition_oracle's
                proof (DGP_HostDigest.key_digest, flatten_parts, state roundtrip);
                LIBB_PartitionEnv.digest needs no repartition hypothesis.  Not
                compiled, so listed.
  M3 rootImage  NLP Root0 of the packet's SecondCut → S.Root0Native c.  Needs
                the TX2 half of the cut identified with c.j.entry's handle-0/6
                buffers (an NNH_WeakReaderCuts.Facts version of
                NNC_WeakR0Rep.at_entry) and V0.Root0 = NNC_ByteCarriers.Root0 on
                bytes (LIBB_V2Star.library).

`nmfB` composes these.  Only the four `Missing` fields stand between the merged
pieces and the TAS field; nothing else in NMF_B is open on this route.
-/
import TAS_TopB
set_option autoImplicit false

namespace RSL.NFB
open RSL.TAS RSL.TFM RSL.EVB
open TX2_241 (V2Lib)
open TX1_345 (S1Lib)

section NMFB
variable (S : Sig) (L : PoolLib) (D : DeployedIds) (V0 : V2Lib) (VL : VLib)
  (P : PreparedNew VL) (C : S1Lib VL) (I : Impl L V0 VL)

/-- The exact remaining field (the type of `NNC_NMFPrimeB.root0_or_rec`). -/
def Remaining (g : NNC_G1a S L V0 VL I) (R : RecSig S) : Prop :=
  ∀ c, S.Exhibited c →
    (∀ a s env, TX2_213.Ref L D (lib V0 (fun _ _ => True) g.w) (TX1_344.asStage1 VL P C)
      a s env (I.entry a s env)) →
    (∃ s', (I.entry (S.args2 c) (S.state2 c) (S.env2 c)).exit = .ret (.ok (), s')) →
    S.Accepted1 c (S.model1 c) →
    S.Game c (S.model1 c) (S.model2 c) →
    S.Extraction c (S.model1 c) (S.model2 c) →
    S.Queries c (S.model1 c) →
    R.SelectsPair c →
    S.Root0Native c ∨ R.EventRec c

theorem remaining_iff (g : NNC_G1a S L V0 VL I) (R : RecSig S) :
    Remaining S L D V0 VL P C I g R ↔ Nonempty (NNC_NMFPrimeB S L D V0 VL P C I g R) :=
  ⟨fun h => ⟨⟨h⟩⟩, fun ⟨n⟩ => n.root0_or_rec⟩

/-- Host objects, indexed by oracle and clock slot. -/
structure Shape where
  /-- `Bytes → State`. -/
  Oracle : Type
  /-- `S2W_ExtractionBoundary.Slot`. -/
  Slot : Type
  /-- `c.sha256` (the headline H of world c). -/
  sha : S.Ctx → Oracle
  /-- `LIBB_PartitionEnv.H (S.env2 c)`. -/
  envH : S.Ctx → Oracle
  /-- `c.j.slot` (the adversary's selected slot; used by SelectsPair/E_rec). -/
  slot : S.Ctx → Slot
  /-- `NNH_HostWeak241.clock (S.env2 c)` (the slot of the TX2 clock reply). -/
  clock2 : S.Ctx → Slot
  /-- `NNH_HostNativeCuts.Packet c`, with origin at slot `k` and native records at `h`. -/
  Cut : S.Ctx → Oracle → Slot → Type
  /-- `CheckpointBytes5Inputs.Oracle (VTop_Checkpoint.digest (LIBB_PartitionEnv.digest (S.env2 c))) () h`. -/
  DigestOracle : S.Ctx → Oracle → Prop
  /-- `{p : NNH_NMFPrime.Packet Unit Unit Unit // Associated c p ∧ p.H = h}`. -/
  Pkt : S.Ctx → Oracle → Type
  /-- `NLP_InputDomain.Root0 p.s.checkpoint p.s.proof`. -/
  root0 : ∀ {c h}, Pkt c h → Prop
  /-- `NNH_NMFPrime.charged p`. -/
  charged : ∀ {c h}, Pkt c h → Prop

variable {S L D V0 VL P C I}

/-- Delivered by merged S5/S6 pieces. -/
structure Delivered (Sh : Shape S) (g : NNC_G1a S L V0 VL I) (R : RecSig S) where
  /-- `NNH_HostNativeCuts.produce` after Obs eta on `ok2` (NFB_NMFBHost.produceTAS). -/
  produce : ∀ c, S.Exhibited c →
    (∀ a s env, TX2_213.Ref L D (lib V0 (fun _ _ => True) g.w) (TX1_344.asStage1 VL P C)
      a s env (I.entry a s env)) →
    (∃ s', (I.entry (S.args2 c) (S.state2 c) (S.env2 c)).exit = .ret (.ok (), s')) →
    S.Accepted1 c (S.model1 c) → S.Game c (S.model1 c) (S.model2 c) →
    Nonempty (Sh.Cut c (Sh.envH c) (Sh.clock2 c))
  /-- `NNH_NMFPrime.Packet` constructor: source := ARX_LocalCharge.bounded (account) (Q0+Q1),
  project := ARQ_Observer.project, select := ARQ_Observer.select cfg verifier,
  budget as in NNC_NMFB.root0_or_rec, selects := the SelectsPair premise (slot c.j.slot),
  d := LIBB_PartitionEnv.digest (env2 c), hash := (), world := NNH_064Install.frame. -/
  complete : ∀ c h, R.SelectsPair c → Sh.DigestOracle c h → Sh.Cut c h (Sh.slot c) → Sh.Pkt c h
  /-- `NNH_NMFPrime.alternative`. -/
  alternative : ∀ c h (p : Sh.Pkt c h), Sh.root0 p ∨ Sh.charged p
  /-- `Iff.rfl` through `NNH_HostRecorderEvent.same` once Associated fixes
  source/project/select/Q and `p.H = c.sha256`. -/
  eventImage : ∀ c (p : Sh.Pkt c (Sh.sha c)), Sh.charged p ↔ R.EventRec c

/-- The four missing obligations (see the header and NFB_NMFBHost.lean). -/
structure Missing (Sh : Shape S) where
  /-- M1: TX2 clock reply is the selected slot (host signature correction). -/
  clock : ∀ c, Sh.clock2 c = Sh.slot c
  /-- M2: native/records transport from `LIBB_PartitionEnv.H (env2 c)` to `c.sha256`. -/
  lift : ∀ c k, Sh.Cut c (Sh.envH c) k → Sh.Cut c (Sh.sha c) k
  /-- M2e: the partition digest's oracle law at `c.sha256`. -/
  oracle : ∀ c, Sh.DigestOracle c (Sh.sha c)
  /-- M3: packet Root0 is the native Root0 at the selected TX2 entry. -/
  rootImage : ∀ c (p : Sh.Pkt c (Sh.sha c)), Sh.root0 p → S.Root0Native c

/-- NMF_B from the merged pieces and the four missing obligations. -/
def nmfB {g : NNC_G1a S L V0 VL I} {R : RecSig S} (Sh : Shape S)
    (dl : Delivered (D := D) (P := P) (C := C) Sh g R) (ms : Missing Sh) : NNC_NMFPrimeB S L D V0 VL P C I g R where
  root0_or_rec := by
    intro c hx weak ok2 acc1 game _ _ sel
    obtain ⟨cut⟩ := dl.produce c hx weak ok2 acc1 game
    have cut' : Sh.Cut c (Sh.envH c) (Sh.slot c) := ms.clock c ▸ cut
    let p := dl.complete c (Sh.sha c) sel (ms.oracle c) (ms.lift c (Sh.slot c) cut')
    rcases dl.alternative c (Sh.sha c) p with root | ev
    · exact Or.inl (ms.rootImage c p root)
    · exact Or.inr ((dl.eventImage c p).mp ev)

theorem remaining_of {g : NNC_G1a S L V0 VL I} {R : RecSig S} (Sh : Shape S)
    (dl : Delivered (D := D) (P := P) (C := C) Sh g R) (ms : Missing Sh) : Remaining S L D V0 VL P C I g R :=
  (nmfB Sh dl ms).root0_or_rec

end NMFB

#print axioms remaining_iff
#print axioms nmfB
#print axioms remaining_of

end RSL.NFB
