import TAS_FinalB
set_option autoImplicit false
noncomputable section
/-! Run 7 (G0 FINAL) statement audit and non-vacuity (TAS_WIRING item 8).
Non-vacuity proved here is DEFINITIONAL: at the context built from an arbitrary
recorded world (worldOf), the top's GameFrame, Game, TraceRep, Out1 and Out2 are,
by Iff.rfl, the recorded physical predicates (CPG projection, CPH game, runtime
trace, carrier-image write facts), NOT the seed's False fields; Out1 is inhabited;
Exhibited, EnvRep and Realizes hold at every world. It does NOT construct an
inhabitant of Runs from an actual accepted deployed transaction pair. -/
namespace AspisR1.NNH8_NonVacuity
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open RSL RSL.TAS RSL.TASB NNH_Libraries
variable {W Tx : Type} (L0 : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)

/-- A World from arbitrary recorded data: admissions witnesses, saved bytes,
heaps, the recorded projection p with tx1/tx2 indices t/u, and the actions. -/
def worldOf (w1 w2 : W) (saved : alloc.vec.Vec U8) (post1 post2 : Heap (Nat → Record))
 (p : CPG_Projection.Observations Tx Bool) (t u : Tx) (actions : List (CPP_BankState.Action Bool)) :
 NOC_Run5bCtx.World W Tx := ⟨w1,w2,saved,post1,post2,p,t,u,actions⟩

theorem world_recorded (fx : NOC_Run5bCtx.Fixed) (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State)
 (w1 w2 : W) (saved : alloc.vec.Vec U8) (post1 post2 : Heap (Nat → Record))
 (p : CPG_Projection.Observations Tx Bool) (t u : Tx) (actions : List (CPP_BankState.Action Bool)) :
 let c := ctxB (NNH8_Exec.exec (Tx := Tx) L0 copy std) fx (worldOf w1 w2 saved post1 post2 p t u actions) H
 c.world.p = p ∧ c.world.t = t ∧ c.world.u = u ∧ c.world.saved = saved ∧ c.world.actions = actions ∧
 c.sha256 = H ∧ c.fixed = fx := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem frame_recorded (c : NOC_Run5bCtx.Ctx W Tx) :
 (NOC_Run5bHost.S_host (Tx := Tx) L0 copy std).GameFrame c ↔
 (((c.world.p.next c.world.t c.world.u ∧ c.i.entry = CPG_Projection.entry c.world.p c.world.t ∧
    c.j.entry = CPG_Projection.entry c.world.p c.world.u) ∧
   ((((c.world.p.layout c.world.t).handles 2).1 = ((c.world.p.layout c.world.u).handles 6).1 ∧
     CPS_PhysicalKey.key c.i.entry 2 = CPS_PhysicalKey.key c.j.entry 6 ∧
     ((c.world.p.layout c.world.t).handles 2).1 ∉ c.world.p.intervening c.world.t c.world.u) ∧
   CPG_Projection.success c.world.p c.world.t = true ∧
   c.world.p.copied c.world.t = c.world.saved ∧ c.world.p.actions c.world.t = c.world.actions)) ∧
  NOC_Run5bHost.retained L0 c) := Iff.rfl

theorem game_recorded (c : NOC_Run5bCtx.Ctx W Tx) (n1 : S2W_ExtractionBoundary.First)
 (n2 : S2W_ExtractionBoundary.Second) :
 (NOC_Run5bHost.S_host (Tx := Tx) L0 copy std).Game c n1 n2 ↔
 (CPH_Game.DeployedPairExecution c.world.p c.world.t c.world.u c.i.entry c.j.entry
  c.world.saved c.world.actions n1 n2 copy NNE_AbortIndicator.allocator CPH_Program.verifier ∧
  NOC_Run5bHost.retained L0 c) := Iff.rfl

theorem trace_recorded (c : NOC_Run5bCtx.Ctx W Tx) (I : RSL.TAS.Impl L V0 VL) :
 (NOC_Run5bHost.S_host (Tx := Tx) L0 copy std).TraceRep c I.entry ↔
 (NNH_RuntimeTrace.Trace (NOC_Run5bHost.envSig (Tx := Tx) L0 copy) (NOC_Run5bHost.data (Tx := Tx) L0 copy std) c I.entry
   (NNH_RecordSig.before1 (NOC_Run5bHost.envSig (Tx := Tx) L0 copy) (NOC_Run5bHost.data (Tx := Tx) L0 copy std)
    (NOC_Run5bHost.record (Tx := Tx) L0 copy) c) c.world.actions
   (c.world.p.parentTentative c.world.t) (c.world.p.physicalEvents c.world.t) ∧
  NNH_RuntimeTrace.Trace (NOC_Run5bHost.envSig (Tx := Tx) L0 copy) (NOC_Run5bHost.data (Tx := Tx) L0 copy std) c I.entry
   (NNH_RecordSig.before2 (NOC_Run5bHost.envSig (Tx := Tx) L0 copy) (NOC_Run5bHost.record (Tx := Tx) L0 copy) c)
   (c.world.p.actions c.world.u) (c.world.p.parentTentative c.world.u) (c.world.p.physicalEvents c.world.u)) := Iff.rfl

theorem out1_recorded (c : NOC_Run5bCtx.Ctx W Tx) (o : RSL.Obs (Except RSL.ProgramError Unit × RSL.SdkState)) :
 (NOC_Run5bHost.S_host (Tx := Tx) L0 copy std).Out1 c o ↔ NNE_PhysicalAccepted.Out1 c.world.saved o := Iff.rfl

theorem out2_true (c : NOC_Run5bCtx.Ctx W Tx) (o : RSL.Obs (Except RSL.ProgramError Unit × RSL.SdkState)) :
 (NOC_Run5bHost.S_host (Tx := Tx) L0 copy std).Out2 c o := trivial

/-- Out1 is not False: any observation without write events satisfies it. -/
theorem out1_inhabited (c : NOC_Run5bCtx.Ctx W Tx) (o : RSL.Obs (Except RSL.ProgramError Unit × RSL.SdkState))
 (h : o.events = []) : (NOC_Run5bHost.S_host (Tx := Tx) L0 copy std).Out1 c o := by
 intro cell bs hm
 rw [h] at hm
 cases hm

/-- Exhibited, EnvRep and Realizes hold at the actual context for EVERY world. -/
theorem total (fx : NOC_Run5bCtx.Fixed) (w : NOC_Run5bCtx.World W Tx)
 (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State) :
 let c := ctxB (NNH8_Exec.exec (Tx := Tx) L0 copy std) fx w H
 (NOC_Run5bHost.S_host (Tx := Tx) L0 copy std).Exhibited c ∧
 (NOC_Run5bHost.S_host (Tx := Tx) L0 copy std).EnvRep c ((NOC_Run5bHost.S_host (Tx := Tx) L0 copy std).env2 c) ∧
 (NNH8_Exec.recSig (Tx := Tx) L0 copy std).Realizes c :=
 ⟨rfl,NNH_HostEnv.environment_rep _ _ _ _,realizes_by_construction (NNH8_Exec.exec (Tx := Tx) L0 copy std) fx w H⟩

/-- Statement items: exhibited_mk / eventRec_mk are rfl / Iff.rfl; queries_mk is h H. -/
example : (NNH8_Exec.exec (Tx := Tx) L0 copy std).exhibited_mk = fun _ _ _ _ _ => rfl := rfl
example : (NNH8_Exec.exec (Tx := Tx) L0 copy std).eventRec_mk = fun _ _ _ _ _ => Iff.rfl := rfl
example : (NNH8_Exec.exec (Tx := Tx) L0 copy std).queries_mk = fun _ _ H _ _ h => h H := rfl
end AspisR1.NNH8_NonVacuity
end
set_option pp.all true
set_option pp.proofs false
#check @AspisR1.RPx_Deployed.deployed
#check @AspisR1.TAS_FinalB.deployed_splitB
#check @AspisR1.TAS_FinalB.deployed_charge
#check @AspisR1.TAS_FinalB.fail_sub_rec
#check @AspisR1.NNH8_DeployedOuter
set_option pp.all false
set_option pp.proofs true
#print AspisR1.NNH8_Exec.exec
#print AspisR1.NNH8_Exec.recSig
#print axioms AspisR1.TAS_FinalB.deployed_splitB
#print axioms AspisR1.TAS_FinalB.deployed_charge
#print axioms AspisR1.TAS_FinalB.fail_sub_rec
#print axioms AspisR1.NNH8_DeployedOuter
#print axioms AspisR1.NNH8_NonVacuity.world_recorded
#print axioms AspisR1.NNH8_NonVacuity.frame_recorded
#print axioms AspisR1.NNH8_NonVacuity.game_recorded
#print axioms AspisR1.NNH8_NonVacuity.trace_recorded
#print axioms AspisR1.NNH8_NonVacuity.out1_recorded
#print axioms AspisR1.NNH8_NonVacuity.out1_inhabited
#print axioms AspisR1.NNH8_NonVacuity.total
