import NNE_PhysicalAccepted
import TAS_Interfaces
set_option autoImplicit false
noncomputable section
namespace NNE_AcceptanceSig
open Aeneas Aeneas.Std Result AspisR1 S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_ReturnedCheckpoint S2W_CommittedCheckpoint S2W_WrapperLaws
open RSL RSL.TAS
/-- Concrete physical binder choices. Other headline fields are supplied by
 the host Sig. All allocator states/finals are definitionally true. -/
structure Data (S : Sig) where
 err : NNE_PhysicalAccepted.PE → ProgramError
 invalid : err .InvalidAccountData = .invalidAccountData
 native1 : S.First → S2W_ExtractionBoundary.First
 native2 : S.Second → S2W_ExtractionBoundary.Second
 e1 : S.Ctx → Entry
 e2 : S.Ctx → Entry
 program : S.Ctx → S2W_ExtractionBoundary.Program
 data1 : S.Ctx → Slice U8
 data2 : S.Ctx → Slice U8
 slot : S.Ctx → S2W_ExtractionBoundary.Slot
 saved : S.Ctx → alloc.vec.Vec U8
 copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record)
 std : S2W_TrustedStd.TrustedStd copy

/-- These are definitions of the host stand-ins, not hypotheses about success.
Out1 selects the saved bytes from write events. A1/A2 retain the actual owned
call equations at the same carrier arguments. -/
def physical (S : Sig) (d : Data S) : Sig :=
 { S with
   args1 := fun c => NNE_EntryArgs.args (d.e1 c) 3 (d.program c) (d.data1 c)
   args2 := fun c => NNE_EntryArgs.args (d.e2 c) 7 (d.program c) (d.data2 c)
   state1 := fun c => NNE_Entry.state (d.e1 c) 0
   state2 := fun c => NNE_Entry.state (d.e2 c) 0
   Accepted1 := fun c n => first (d.native1 n) d.copy NNE_AbortIndicator.allocator
     (d.e1 c) (d.program c) (d.data1 c) true = ok (.Ok (d.saved c,
      writeBracket (d.e1 c).heap 2 0 0 (source (nativeBytes (d.saved c))),true))
   Accepted2 := fun c n => second (d.native2 n) NNE_AbortIndicator.allocator
     (d.e2 c) (d.program c) (d.data2 c) (d.slot c) true = ok (.Ok ((d.e2 c).heap,true))
   Out1 := fun c o => NNE_PhysicalAccepted.Out1 (d.saved c) o
   Out2 := fun _ _ => True
   ModelRet1 := fun c a r => ∀ e p data,
     a = NNE_PhysicalAccepted.child1 d.err e p data →
     (∀ saved, r = .ok (nativeBytes saved) →
       d.native1 (S.model1 c) p e.first data = ok (.Ok saved)) ∧
     (∀ error, r = .error error → ∃ pe,
       d.native1 (S.model1 c) p e.first data = ok (.Err pe))
   ModelRet2 := fun c a r =>
     a = NNE_PhysicalAccepted.child2 d.err (d.e2 c) (d.program c) (d.data2 c) (S.env2 c).clock →
     r = .ok () →
     d.native2 (S.model2 c) (d.program c) ((d.e2 c).second secondSizes)
       (d.data2 c) (d.slot c) = ok (.Ok ()) }

def a3 (S : Sig) (d : Data S) (V : VLib) (P : PreparedNew V) (C : TX1_345.S1Lib V) :
 NNE_A3 (physical S d) V P C where
 accepted1 := by
  intro c o a1 hx ref ok1 out
  obtain ⟨post,hpost⟩ := ok1
  cases o with
  | mk exit es =>
   dsimp only at hpost
   subst exit
   apply NNE_PhysicalAccepted.first V P C d.err d.invalid
     (d.native1 (S.model1 c)) d.copy d.std (d.e1 c) (d.program c) (d.data1 c)
     (S.env1 c) (d.saved c) post es ref out
   intro es' hc
   exact a1.stage1 c _ _ _ _ hx (S.env1_rep c) hc rfl (d.e1 c) (d.program c) (d.data1 c) rfl |>.1 (d.saved c) rfl

def a4 (S : Sig) (d : Data S) (L : PoolLib) (D : DeployedIds) (V : TX2_241.V2Lib) :
 NNE_A4 (physical S d) L D V where
 accepted2 := by
  intro c o a2 hx ref ok2 _
  obtain ⟨post,hpost⟩ := ok2
  cases o with
  | mk exit es =>
   dsimp only at hpost
   subst exit
   apply NNE_PhysicalAccepted.second L D V d.err d.invalid (d.native2 (S.model2 c))
     (d.e2 c) (d.program c) (d.data2 c) (d.slot c) (S.env2 c) post es ref
   intro es' hc
   exact a2.stage2 c _ _ _ _ hx (S.env2_rep c) hc rfl rfl rfl
#print axioms a3
#print axioms a4
end NNE_AcceptanceSig
end
