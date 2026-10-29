import R1Z.PV_RDB2F_SoftOuter
namespace R1Z.PV_RDB2F_NativeShaFrame
open Aeneas Aeneas.Std Result PV_RDB2E_ShaHandles
set_option autoImplicit false
/-- Deployed sha2 0.10.9 and generic-array 0.14.7 source fields. Padding/PhantomData
carry no initialized bytes; compiler layout preservation remains V370. -/
structure GenericArray (T : Type) (n : Usize) where
  data : Array T n
structure Sha256VarCore where
  state : Array U32 8#usize
  block_len : U64
structure BlockBuffer where
  buffer : GenericArray U8 64#usize
  pos : U8
structure Native where
  core : Sha256VarCore
  buffer : BlockBuffer
  out : GenericArray U8 32#usize

def associate (native : Native) : Frame :=
  ⟨⟨native.core.state,native.core.block_len⟩,native.buffer.buffer.data,native.buffer.pos,native.out.data⟩
def restore (frame : Frame) : Native :=
  ⟨⟨frame.core.state,frame.core.block_len⟩,⟨⟨frame.buffer⟩,frame.pos⟩,⟨frame.output⟩⟩

theorem all_native_fields (native : Native) : restore (associate native)=native := by
  cases native with | mk core buffer out => cases core; cases buffer; cases out; rfl

theorem all_model_fields (frame : Frame) : associate (restore frame)=frame := by
  cases frame with | mk core buffer pos output => cases core; rfl

/-- Three disjoint mutable loans keep all current fields, including the count. -/
theorem simultaneous_restore (native : Native) (state : State)
    (buffer : Array U8 64#usize) (out : Array U8 32#usize) :
    restore (putOutput (putBuffer (putState (associate native) state) buffer) out)=
      ⟨⟨state,native.core.block_len⟩,⟨⟨buffer⟩,native.buffer.pos⟩,⟨out⟩⟩ := rfl

def softwareFinalize (native : Native) (valid : (position (associate native)).val<64) : Result Native := do
  let current ← finalize PV_RDB2F_ConcreteSoft.software (associate native) valid
  ok (restore current)

theorem software_all_fields (native : Native) (valid : (position (associate native)).val<64) :
    (do let after ← softwareFinalize native valid;ok (forget (associate after)))=
      PV_RDB2D_SHAState.completeState PV_RDB2F_ConcreteSoft.software
        (associate native).core (associate native).buffer (position (associate native)) := by
  simp only [softwareFinalize,bind_assoc_eq,bind_tc_ok,all_model_fields]
  exact PV_RDB2F_ConcreteSoft.all_fields (associate native) valid

#print axioms all_native_fields
#print axioms all_model_fields
#print axioms simultaneous_restore
#print axioms software_all_fields
end R1Z.PV_RDB2F_NativeShaFrame
