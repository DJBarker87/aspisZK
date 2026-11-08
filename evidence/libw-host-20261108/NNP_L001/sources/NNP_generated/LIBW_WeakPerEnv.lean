import LIBB_V2Star
set_option autoImplicit false
noncomputable section
namespace LIBW_WeakPerEnv
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NLW_Full064
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-! TGB-1 correction (evidence/tx2-gap-audit-20261108/TGB_REPORT.md).

`LIBB_V2Star.weak H d hash world` registers `NNC_ObservedLaw.w H d hash world`
with ONE hash model `H` and digest oracle `d` for every `Env`.  The canonical
law `LIBB_Tx2Auth.law` (see `LIBB_Tx2Auth.native`) is read at
`LIBB_PartitionEnv.H env` and `LIBB_PartitionEnv.digest env`.  This module
registers the weak law per `Env` in exactly that shape.  The library `V0`
(`LIBB_V2Star.library`), its error carrier, printer, canonical Root0 and
canonical law are unchanged; Dom064 and every RowSpec are unchanged.

Two registrations are given.
* `wEnv world`: TGB-1's literal fix; the hash model and digest oracle are
  per Env, the caller-frame `world` is a parameter.
* `wAny Ambient`: the same law with the world existentially bound per
  observation, mirroring `LIBB_Tx2Auth.native`, which holds at EVERY world.
  `wEnv world` refines into `wAny Ambient` (`refines_any`).

Proved here: the registrations and their identities with `TCK.weaken`, the
pointwise identity with `NNC_ObservedLaw.w` specialised at each Env,
`WriteFree` for every argument, `Refines064` from a per-Env native
representation of the host `f064`, and the TAS `NNC_G1a` constructors.
NOT proved here: the host representation (`RepAt`) for the actual `f064`,
and the `okHeader` field.  `okHeader_of_oracle` derives it from a per-Env
`CheckpointBytes5Inputs.Oracle` at `LIBB_PartitionEnv.H env`; that premise
quantifies over all part lists, while `LIBB_PartitionEnv.H` always applies the
three-part C04 partition, so it is not expected to hold for an arbitrary Env
(see LIBW_REPORT.md).  Target not yet established. -/

/-- The V0 error carrier of the weak instance (= `verifier.Error`). -/
abbrev LibErr : Type := LIBB_V2Star.library.VErr

/-- TGB-1 fix: `NNC_ObservedLaw.w` read at the Env's own partitioned hash
model and digest oracle, `X = Unit`, exactly as `LIBB_Tx2Auth.native`. -/
def wEnv {Ambient : Type} (world : NLM_PacketTypes.World Ambient)
 (pub proof ck : RSL.Bytes) : RSL.Spec (Except LibErr Unit) :=
 fun env o => NNC_ObservedLaw.w (LIBB_PartitionEnv.H env) (LIBB_PartitionEnv.digest env) ()
  world pub proof ck env o

/-- World-free form: some caller frame of type `Ambient` per observation. -/
def wAny (Ambient : Type) (pub proof ck : RSL.Bytes) : RSL.Spec (Except LibErr Unit) :=
 fun env o => ∃ world : NLM_PacketTypes.World Ambient, wEnv world pub proof ck env o

/-! ## Registration on the SAME V0 -/

abbrev weakEnv {Ambient : Type} (world : NLM_PacketTypes.World Ambient) : RSL.TX2_241.V2Lib :=
 RSL.TAS.lib LIBB_V2Star.library (fun _ _ => True) (wEnv world)

abbrev weakAny (Ambient : Type) : RSL.TX2_241.V2Lib :=
 RSL.TAS.lib LIBB_V2Star.library (fun _ _ => True) (wAny Ambient)

theorem weakEnv_identity {Ambient : Type} (world : NLM_PacketTypes.World Ambient) :
 weakEnv world = RSL.TCK.weaken LIBB_V2Star.library (wEnv world) := rfl

theorem weakAny_identity (Ambient : Type) :
 weakAny Ambient = RSL.TCK.weaken LIBB_V2Star.library (wAny Ambient) := rfl

theorem weakEnv_exact {Ambient : Type} (world : NLM_PacketTypes.World Ambient) :
 (weakEnv world).tx2auth = wEnv world := rfl

theorem weakAny_exact (Ambient : Type) : (weakAny Ambient).tx2auth = wAny Ambient := rfl

theorem weakEnv_same_error {Ambient : Type} (world : NLM_PacketTypes.World Ambient) :
 (weakEnv world).VErr = LIBB_V2Star.library.VErr ∧
 (weakEnv world).debug = LIBB_V2Star.library.debug := ⟨rfl, rfl⟩

theorem weakAny_same_error (Ambient : Type) :
 (weakAny Ambient).VErr = LIBB_V2Star.library.VErr ∧
 (weakAny Ambient).debug = LIBB_V2Star.library.debug := ⟨rfl, rfl⟩

/-- The registered law IS `NNC_ObservedLaw.w` specialised at each Env. -/
theorem weakEnv_specialised {Ambient : Type} (world : NLM_PacketTypes.World Ambient)
 (pub proof ck : RSL.Bytes) (env : RSL.Env) :
 (weakEnv world).tx2auth pub proof ck env =
 NNC_ObservedLaw.w (LIBB_PartitionEnv.H env) (LIBB_PartitionEnv.digest env) () world
  pub proof ck env := rfl

/-- The canonical instance is untouched by this registration. -/
theorem canonical_unchanged :
 RSL.TAS.lib LIBB_V2Star.library LIBB_V2Star.library.Root0 LIBB_V2Star.library.tx2auth =
 LIBB_V2Star.library := rfl

/-! ## WriteFree (consumed by G2, NMV_.g2) -/

theorem writeFree {Ambient : Type} (world : NLM_PacketTypes.World Ambient)
 (pub proof ck : RSL.Bytes) : RSL.TAS.WriteFree (wEnv world pub proof ck) := by
 intro env o source c b
 exact (NNC_ObservedLaw.writeFree (LIBB_PartitionEnv.H env) (LIBB_PartitionEnv.digest env) ()
  world pub proof ck) env o source c b

theorem writeFree_any (Ambient : Type) (pub proof ck : RSL.Bytes) :
 RSL.TAS.WriteFree (wAny Ambient pub proof ck) := by
 intro env o source c b
 obtain ⟨world, h⟩ := source
 exact writeFree world pub proof ck env o h c b

/-! ## Refines064 from a per-Env native representation -/

/-- Per-Env association of one host observation with the native observer:
the native 064 run at the Env's OWN `H`/`digest` (the same carriers as
`LIBB_Tx2Auth.native`), its complete digest trace, and the observation
equal to the rendered exit and events.  This is the representation the host
interpreter must install for actual `I.f064`; it is not proved here. -/
def RepAt {Ambient : Type} (world : NLM_PacketTypes.World Ambient)
 (f064 : RSL.Bytes → RSL.Bytes → RSL.Bytes → RSL.Env → RSL.Obs (Except LibErr Unit))
 (pub proof ck : RSL.Bytes) (env : RSL.Env) : Prop :=
 ∃ (pu pr cp : Slice U8),
  NNC_ByteCarriers.host pu.val = pub ∧ NNC_ByteCarriers.host pr.val = proof ∧
  NNC_ByteCarriers.host cp.val = ck ∧
  ∃ (outcome : NLW_Full064.End (LIBB_PartitionEnv.H env)
      (⟨LIBB_PartitionEnv.digest env, pu, pr, cp, ()⟩ : NLW_Full064.Args Unit))
    (events : List (NLW_Full064.Event Ambient Unit)) (trace : NNC_DigestTrace.Trace),
   NMN_064.Native (LIBB_PartitionEnv.H env)
     ⟨⟨LIBB_PartitionEnv.digest env, pu, pr, cp, ()⟩, world⟩ outcome events ∧
   NNC_ObservedWeak.TraceOf outcome trace ∧
   f064 pub proof ck env =
    ⟨NNC_WeakSpec.exit (LIBB_PartitionEnv.H env) _ outcome, NNC_DigestTrace.render trace⟩

/-- Fixed caller frame, per-Env hash model: on the three extents. -/
def HostRep {Ambient : Type} (world : NLM_PacketTypes.World Ambient)
 (f064 : RSL.Bytes → RSL.Bytes → RSL.Bytes → RSL.Env → RSL.Obs (Except LibErr Unit)) : Prop :=
 ∀ pub proof ck env, proof.length = 57607 → ck.length = 1768 → pub.length ≤ 1880 →
  RepAt world f064 pub proof ck env

/-- World chosen per call (the actual caller frame of that invocation). -/
def HostRepAny (Ambient : Type)
 (f064 : RSL.Bytes → RSL.Bytes → RSL.Bytes → RSL.Env → RSL.Obs (Except LibErr Unit)) : Prop :=
 ∀ pub proof ck env, proof.length = 57607 → ck.length = 1768 → pub.length ≤ 1880 →
  ∃ world : NLM_PacketTypes.World Ambient, RepAt world f064 pub proof ck env

theorem law_of_rep {Ambient : Type} (world : NLM_PacketTypes.World Ambient)
 (f064 : RSL.Bytes → RSL.Bytes → RSL.Bytes → RSL.Env → RSL.Obs (Except LibErr Unit))
 (pub proof ck : RSL.Bytes) (env : RSL.Env) (rep : RepAt world f064 pub proof ck env) :
 wEnv world pub proof ck env (f064 pub proof ck env) := by
 obtain ⟨pu, pr, cp, hpu, hpr, hcp, outcome, events, trace, native, source, same⟩ := rep
 exact ⟨pu, pr, cp, hpu, hpr, hcp, ⟨outcome, events, trace, native, source, same⟩⟩

/-- G1b side condition at the per-Env law, for every Env. -/
theorem refines {Ambient : Type} (world : NLM_PacketTypes.World Ambient)
 (f064 : RSL.Bytes → RSL.Bytes → RSL.Bytes → RSL.Env → RSL.Obs (Except LibErr Unit))
 (rep : HostRep world f064) :
 RSL.TAS.Refines064 LIBB_V2Star.library f064 (fun _ _ => True) (wEnv world) := by
 intro x env domain
 obtain ⟨hp, hc, hu, _⟩ := domain
 exact law_of_rep world f064 x.1 x.2.1 x.2.2 env (rep x.1 x.2.1 x.2.2 env hp hc hu)

theorem refines_any_of_rep (Ambient : Type)
 (f064 : RSL.Bytes → RSL.Bytes → RSL.Bytes → RSL.Env → RSL.Obs (Except LibErr Unit))
 (rep : HostRepAny Ambient f064) :
 RSL.TAS.Refines064 LIBB_V2Star.library f064 (fun _ _ => True) (wAny Ambient) := by
 intro x env domain
 obtain ⟨hp, hc, hu, _⟩ := domain
 obtain ⟨world, hat⟩ := rep x.1 x.2.1 x.2.2 env hp hc hu
 exact ⟨world, law_of_rep world f064 x.1 x.2.1 x.2.2 env hat⟩

/-- A fixed-world refinement transports to the world-free law. -/
theorem refines_any {Ambient : Type} (world : NLM_PacketTypes.World Ambient)
 (f064 : RSL.Bytes → RSL.Bytes → RSL.Bytes → RSL.Env → RSL.Obs (Except LibErr Unit))
 (r : RSL.TAS.Refines064 LIBB_V2Star.library f064 (fun _ _ => True) (wEnv world)) :
 RSL.TAS.Refines064 LIBB_V2Star.library f064 (fun _ _ => True) (wAny Ambient) := by
 intro x env domain
 obtain ⟨hp, hc, hu, _⟩ := domain
 exact ⟨world, r x env ⟨hp, hc, hu, trivial⟩⟩

/-! ## Accepted header (TAS okHeader), conditional on a per-Env Oracle -/

/-- Per-Env ROM/carrier premise of `NNC_ObservedLaw.accepted_header`.
Stated, not discharged; see the module docstring. -/
def OracleEnv : Prop :=
 ∀ env : RSL.Env, CheckpointBytes5Inputs.Oracle
  (VTop_Checkpoint.digest (LIBB_PartitionEnv.digest env)) () (LIBB_PartitionEnv.H env)

theorem okHeader_of_oracle {Ambient : Type} (world : NLM_PacketTypes.World Ambient)
 (oracle : OracleEnv) (pub proof ck : RSL.Bytes) (env : RSL.Env) (o : RSL.Obs (Except LibErr Unit))
 (domain : RSL.TX2_241.Dom064 (weakEnv world) (pub, proof, ck))
 (observed : wEnv world pub proof ck env o) (ok : o.exit = .ret (.ok ())) :
 NLW_ReaderHeader.decode (NNC_ByteCarriers.protocol ck) =
 some (LIBB_PartitionEnv.H env (NNC_ByteCarriers.protocol proof),
   LIBB_PartitionEnv.H env (NNC_ByteCarriers.protocol pub)) := by
 obtain ⟨hp, hc, hu, _⟩ := domain
 exact NNC_ObservedLaw.accepted_header (LIBB_PartitionEnv.H env) (LIBB_PartitionEnv.digest env) ()
  world pub proof ck hp hc hu (oracle env) env o observed ok

theorem okHeader_of_oracle_any (Ambient : Type)
 (oracle : OracleEnv) (pub proof ck : RSL.Bytes) (env : RSL.Env) (o : RSL.Obs (Except LibErr Unit))
 (domain : RSL.TX2_241.Dom064 (weakAny Ambient) (pub, proof, ck))
 (observed : wAny Ambient pub proof ck env o) (ok : o.exit = .ret (.ok ())) :
 NLW_ReaderHeader.decode (NNC_ByteCarriers.protocol ck) =
 some (LIBB_PartitionEnv.H env (NNC_ByteCarriers.protocol proof),
   LIBB_PartitionEnv.H env (NNC_ByteCarriers.protocol pub)) := by
 obtain ⟨hp, hc, hu, _⟩ := domain
 obtain ⟨world, h⟩ := observed
 exact okHeader_of_oracle world oracle pub proof ck env o ⟨hp, hc, hu, trivial⟩ h ok

/-! ## TAS G1a constructors on V0 = LIBB_V2Star.library -/

/-- Exact `NNC_G1a` at the per-Env law.  `rep` and `okHeader` remain host
obligations; nothing else is assumed. -/
def assemble {Ambient : Type} (S : RSL.TAS.Sig) (L : RSL.PoolLib) (VL : RSL.VLib)
 (I : RSL.TAS.Impl L LIBB_V2Star.library VL) (world : NLM_PacketTypes.World Ambient)
 (rep : HostRep world I.f064)
 (okHeader : ∀ pub pr ck env o, RSL.TX2_241.Dom064 (weakEnv world) (pub, pr, ck) →
   wEnv world pub pr ck env o → o.exit = .ret (.ok ()) → S.readerHeader env pub pr ck) :
 RSL.TAS.NNC_G1a S L LIBB_V2Star.library VL I where
 w := wEnv world
 weak := refines world I.f064 rep
 writeFree := writeFree world
 okHeader := okHeader

/-- Exact `NNC_G1a` at the world-free law. -/
def assembleAny (Ambient : Type) (S : RSL.TAS.Sig) (L : RSL.PoolLib) (VL : RSL.VLib)
 (I : RSL.TAS.Impl L LIBB_V2Star.library VL)
 (rep : HostRepAny Ambient I.f064)
 (okHeader : ∀ pub pr ck env o, RSL.TX2_241.Dom064 (weakAny Ambient) (pub, pr, ck) →
   wAny Ambient pub pr ck env o → o.exit = .ret (.ok ()) → S.readerHeader env pub pr ck) :
 RSL.TAS.NNC_G1a S L LIBB_V2Star.library VL I where
 w := wAny Ambient
 weak := refines_any_of_rep Ambient I.f064 rep
 writeFree := writeFree_any Ambient
 okHeader := okHeader

/-- `okHeader` from the per-Env Oracle and a per-Env header representation. -/
theorem okHeader_field {Ambient : Type} (S : RSL.TAS.Sig) (world : NLM_PacketTypes.World Ambient)
 (oracle : OracleEnv)
 (headerRep : ∀ env pub proof ck,
   NLW_ReaderHeader.decode (NNC_ByteCarriers.protocol ck) =
    some (LIBB_PartitionEnv.H env (NNC_ByteCarriers.protocol proof),
      LIBB_PartitionEnv.H env (NNC_ByteCarriers.protocol pub)) →
   S.readerHeader env pub proof ck) :
 ∀ pub pr ck env (o : RSL.Obs (Except LibErr Unit)), RSL.TX2_241.Dom064 (weakEnv world) (pub, pr, ck) →
   wEnv world pub pr ck env o → o.exit = .ret (.ok ()) → S.readerHeader env pub pr ck :=
 fun pub pr ck env o domain observed ok =>
  headerRep env pub pr ck (okHeader_of_oracle world oracle pub pr ck env o domain observed ok)

#print axioms weakEnv_identity
#print axioms weakAny_identity
#print axioms weakEnv_exact
#print axioms weakAny_exact
#print axioms weakEnv_same_error
#print axioms weakAny_same_error
#print axioms weakEnv_specialised
#print axioms canonical_unchanged
#print axioms writeFree
#print axioms writeFree_any
#print axioms law_of_rep
#print axioms refines
#print axioms refines_any_of_rep
#print axioms refines_any
#print axioms okHeader_of_oracle
#print axioms okHeader_of_oracle_any
#print axioms assemble
#print axioms assembleAny
#print axioms okHeader_field
end LIBW_WeakPerEnv
end
