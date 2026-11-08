-- NNH-prefixed weak-Err adaptation of the corresponding NNE module.
import NNE_RecordSig
import NNH_RuntimeTrace
import RPz7_CPH_Game
set_option autoImplicit false
noncomputable section
namespace NNH_RecordSig
open Aeneas Aeneas.Std AspisR1 S2Trust S2W_D189Entry S2W_D189Wrappers
open Hist_Store CPP_BankState CPG_Projection
open RSL RSL.TAS NNE_Observed

abbrev Data := NNE_RecordSig.Data

def before1 (S : Sig) (d : NNH_AcceptanceSig.Data S) (r : Data S) (c : S.Ctx) : Bank :=
 CPR_SourceBank.afterCopy (cached ((r.p c).bank (r.t c)))
   (((r.p c).layout (r.t c)).handles 2).1 (d.saved c)
def before2 (S : Sig) (r : Data S) (c : S.Ctx) : Bank := cached ((r.p c).bank (r.u c))

/-- Exactly game (a),(b),(c) and the two non-trace equalities of (d). -/
def GameFrame (S : Sig) (d : NNH_AcceptanceSig.Data S) (r : Data S) (c : S.Ctx) : Prop :=
 ((r.p c).next (r.t c) (r.u c) ∧ d.e1 c = CPG_Projection.entry (r.p c) (r.t c) ∧
   d.e2 c = CPG_Projection.entry (r.p c) (r.u c)) ∧
 ((((r.p c).layout (r.t c)).handles 2).1 = (((r.p c).layout (r.u c)).handles 6).1 ∧
   CPS_PhysicalKey.key (d.e1 c) 2 = CPS_PhysicalKey.key (d.e2 c) 6 ∧
   (((r.p c).layout (r.t c)).handles 2).1 ∉ (r.p c).intervening (r.t c) (r.u c)) ∧
 CPG_Projection.success (r.p c) (r.t c) = true ∧
 (r.p c).copied (r.t c) = d.saved c ∧ (r.p c).actions (r.t c) = r.actions c

/-- The final physical stand-ins. Recorded1/2 are the literal CPG Executes
terms; Game is the literal CPH game, not a substitute conjunction. -/
def physical (S : Sig) (d : NNH_AcceptanceSig.Data S) (r : Data S) : Sig :=
 { NNH_AcceptanceSig.physical S d with
   GameFrame := GameFrame S d r
   Recorded1 := fun c n1 n2 => CPG_RuntimeTrace.Executes (d.native1 n1) (d.native2 n2) d.copy
     NNE_AbortIndicator.allocator (d.program c) (before1 S d r c) (r.actions c)
     ((r.p c).parentTentative (r.t c)) ((r.p c).physicalEvents (r.t c))
   Recorded2 := fun c n1 n2 => CPG_RuntimeTrace.Executes (d.native1 n1) (d.native2 n2) d.copy
     NNE_AbortIndicator.allocator (d.program c) (before2 S r c) ((r.p c).actions (r.u c))
     ((r.p c).parentTentative (r.u c)) ((r.p c).physicalEvents (r.u c))
   Game := fun c n1 n2 => CPH_Game.DeployedPairExecution (r.p c) (r.t c) (r.u c)
     (d.e1 c) (d.e2 c) (d.saved c) (r.actions c) (d.native1 n1) (d.native2 n2)
     d.copy NNE_AbortIndicator.allocator (d.program c)
   mkGame := fun _ _ _ f h1 h2 => ⟨f.1,f.2.1,f.2.2.1,⟨⟨f.2.2.2.1,f.2.2.2.2,h1⟩,h2⟩⟩
   TraceRep := fun c f =>
     NNH_RuntimeTrace.Trace S d c f (before1 S d r c) (r.actions c)
       ((r.p c).parentTentative (r.t c)) ((r.p c).physicalEvents (r.t c)) ∧
     NNH_RuntimeTrace.Trace S d c f (before2 S r c) ((r.p c).actions (r.u c))
       ((r.p c).parentTentative (r.u c)) ((r.p c).physicalEvents (r.u c)) }

def a3 (S : Sig) (d : NNH_AcceptanceSig.Data S) (r : Data S)
 (V : VLib) (P : PreparedNew V) (C : TX1_345.S1Lib V) : NNE_A3 (physical S d r) V P C where
 accepted1 := fun c o a1 => (NNH_AcceptanceSig.a3 S d V P C).accepted1 c o ⟨a1.stage1⟩

def a4 (S : Sig) (d : NNH_AcceptanceSig.Data S) (r : Data S)
 (L : PoolLib) (D : DeployedIds) (V : TX2_241.V2Lib) : NNE_A4 (physical S d r) L D V where
 accepted2 := fun c o a2 => (NNH_AcceptanceSig.a4 S d L D V).accepted2 c o ⟨a2.stage2⟩

def a5 (S : Sig) (d : NNH_AcceptanceSig.Data S) (r : Data S)
 (L : PoolLib) (V0 : TX2_241.V2Lib) (V : VLib) (P : PreparedNew V)
 (C : TX1_345.S1Lib V) (I : Impl L V0 V) : NNE_A5 (physical S d r) L V0 V P C I where
 recorded := by
  intro c a1 hx h1 g2 reject trace
  exact ⟨NNH_RuntimeTrace.executes S d V P C c ⟨a1.stage1⟩ hx I.entry h1 g2 reject trace.1,
    NNH_RuntimeTrace.executes S d V P C c ⟨a1.stage1⟩ hx I.entry h1 g2 reject trace.2⟩

#print axioms a3
#print axioms a4
#print axioms a5
#print axioms physical
end NNH_RecordSig
end
