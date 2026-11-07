import PV_THR2_RunF170Prefix
import PV_THR2_RunKeyFieldLoad
import PV_THR2_RunF170DynamicPrefix
import PV_THR2_RunEntryReply
set_option autoImplicit false
namespace PV_FN_THREAD_f170
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine

/-- LocalKey and callback supplied at this function's own call entry. This
names caller-owned root storage, not a successful intermediate read or reply. -/
def EntryPre (s : Store Data) (a ka kl : Nat) (callback : Data) (b : Bool) : Prop :=
  s.cells ⟨a,1,[]⟩ = some (PV_STX2_TypedReferences.reference ⟨ka,kl,[]⟩ .null) ∧
  s.cells ⟨a,2,[]⟩ = some callback ∧
  s.cells ⟨ka,kl,[]⟩ = some (PV_THR2_KeyInitConstruct.key b) ∧ ka ≠ a

def beforeDynamic (s : Store Data) (a : Nat) (b : Bool) :=
  PV_THR2_F170DynamicPrefix.prepared
    (write (PV_THR2_RunF170Prefix.prepared s a) ⟨a,8,[]⟩
      (some (PV_THR2_KeyValues.castToken b).2)) a

def arg : Data := PV_THR2_KeyValues.pack PV_THR2_F170DynamicPrefix.kind []

/-- Derived entry-key read after the source's local-only prologue. -/
theorem keyRead {W : Type} (base : Carrier W Data) (s : Store Data)
    (a ka kl : Nat) (callback : Data) (b : Bool)
    (pre : EntryPre s a ka kl callback b) :
    readAddress (PV_THR2_EntryDynamic.carrier base b)
      (PV_THR2_RunF170Prefix.prepared s a) ⟨ka,kl,[]⟩ =
        some (PV_THR2_KeyInitConstruct.key b) := by
  have ne : ∀ i, (⟨ka,kl,[]⟩ : Address) ≠ ⟨a,i,[]⟩ :=
    fun i h => pre.2.2.2 (congrArg Address.activation h)
  simp only [readAddress,readFields,PV_THR2_RunF170Prefix.prepared,write,ne,if_false,pre.2.2.1]
  rfl

/-- The key-field and Option construction fragments are consumed by name at
this local entry. No theorem beginning at F0 occurs in this proof. -/
theorem toDynamic {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a ka kl : Nat) (callback : Data) (b : Bool)
    (parents : List Frame) (w : W) (pre : EntryPre s a ka kl callback b) :
    PV_THR2_Execution.advance (PV_THR2_EntryDynamic.carrier base b) ctl programs handler ((10+1)+2)
      ⟨.running ⟨{activation := a,remaining := PV_THR2_F170.live.body},parents,s⟩,w,[]⟩ =
    ⟨.running ⟨{activation := a,remaining := PV_THR2_F170.live.body.drop 13},parents,
      beforeDynamic s a b⟩,w,[]⟩ := by
  have bound : (PV_THR2_RunF170Prefix.prepared s a).cells ⟨a,1,[]⟩ =
      some (PV_STX2_TypedReferences.reference ⟨ka,kl,[]⟩ .null) := by
    simpa [PV_THR2_RunF170Prefix.prepared,write] using pre.1
  have prologue := PV_THR2_RunF170Prefix.prologue
    (PV_STX2_TypedReferences.carrier (PV_THR2_FunctionValues.base (PV_THR2_KeyInstall.carrier base b)))
    ctl programs handler s a parents w
  change PV_THR2_Execution.advance (PV_THR2_EntryDynamic.carrier base b) ctl programs handler 10
    ⟨.running ⟨{activation := a,remaining := PV_THR2_F170.live.body},parents,s⟩,w,[]⟩ = _ at prologue
  rw [PV_THR2_Execution.advance_add,PV_THR2_Execution.advance_add,prologue]
  have load := PV_THR2_RunKeyFieldLoad.load (PV_THR2_FunctionValues.base (PV_THR2_KeyInstall.carrier base b))
    ctl programs handler (PV_THR2_RunF170Prefix.prepared s a) a ⟨ka,kl,[]⟩
    (PV_THR2_KeyInitConstruct.key b) (PV_THR2_KeyValues.castToken b).2 parents w bound
    (keyRead base s a ka kl callback b pre) (PV_THR2_KeyInstall.field base b)
  change PV_THR2_Execution.advance (PV_THR2_EntryDynamic.carrier base b) ctl programs handler 1
    ⟨.running ⟨{activation := a,remaining := PV_THR2_F170.live.body.drop 10},parents,
      PV_THR2_RunF170Prefix.prepared s a⟩,w,[]⟩ = _ at load
  rw [load]
  exact PV_THR2_RunF170DynamicPrefix.prepare _ ctl programs handler _ a parents w rfl

/-- Both dynamic operands come from actual source writes, not a ready premise. -/
theorem dynamicCells (s : Store Data) (a : Nat) (b : Bool) :
    (beforeDynamic s a b).cells ⟨a,8,[]⟩ = some (PV_THR2_KeyValues.castToken b).2 ∧
    (beforeDynamic s a b).cells ⟨a,9,[]⟩ = some arg := by
  simp [beforeDynamic,PV_THR2_F170DynamicPrefix.prepared,arg,write]

/-- The actual own-entry run issues its selected TLS child at8039. -/
theorem request {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a ka kl : Nat) (callback : Data) (b : Bool)
    (parents : List Frame) (w : W) (pre : EntryPre s a ka kl callback b) :
    PV_THR2_Execution.advance (PV_THR2_EntryDynamic.carrier base b) ctl programs handler (((10+1)+2)+1)
      ⟨.running ⟨{activation := a,remaining := PV_THR2_F170.live.body},parents,s⟩,w,[]⟩ =
    ⟨.running ⟨PV_THR2_DynamicIssue.waitingFrame (beforeDynamic s a b) a
      (PV_THR2_KeyValues.castToken b).2 arg,parents,
      PV_THR2_DynamicIssue.issued (beforeDynamic s a b) a arg⟩,w,[]⟩ := by
  rw [PV_THR2_Execution.advance_add,toDynamic base ctl programs handler s a ka kl callback b parents w pre]
  simp only [PV_THR2_Execution.advance]
  rw [PV_THR2_ExecutionBoundary.dynamic _ _ _ _ _ _ _ _ _ _ _ (by rfl)]
  exact PV_THR2_DynamicIssue.issue _ _ _ _ _ a parents _ _ w
    (dynamicCells s a b).1 (dynamicCells s a b).2

/-- Full arbitrary answer at the first LEAF boundary. This is a prefix only;
the 277/278/279/callback and error/drop return branches remain to compose. -/
theorem fullReply {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a ka kl : Nat) (callback : Data) (b : Bool)
    (parents : List Frame) (w : W) (pre : EntryPre s a ka kl callback b) :
    PV_THR2_Execution.advance (PV_THR2_EntryDynamic.carrier base b) ctl
      (PV_THR2_RunEntryDynamic.table programs) handler ((((10+1)+2)+1)+1)
      ⟨.running ⟨{activation := a,remaining := PV_THR2_F170.live.body},parents,s⟩,w,[]⟩ =
    PV_THR2_OffPathReply.delivered (PV_THR2_EntryDynamic.carrier base b)
      (beforeDynamic s a b) a parents arg b
      (handler (.child (PV_THR2_KeyValues.castToken b).2 (beforeDynamic s a b).nextActivation [arg]) w) := by
  rw [PV_THR2_Execution.advance_add,request base ctl _ handler s a ka kl callback b parents w pre]
  simp only [PV_THR2_Execution.advance]
  rw [PV_THR2_ExecutionBoundary.full_reply _ _ _ _ _ _ _ _ 7 _ w rfl rfl rfl rfl
    (PV_THR2_RunEntryDynamic.children programs b)]
  rfl

#print axioms keyRead
#print axioms toDynamic
#print axioms dynamicCells
#print axioms request
#print axioms fullReply
end PV_FN_THREAD_f170
