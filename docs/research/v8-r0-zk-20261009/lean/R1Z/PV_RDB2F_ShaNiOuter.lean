import R1Z.PV_RDB2F_ShaNi
import R1Z.PV_RDB2F_NativeShaFrame
namespace R1Z.PV_RDB2F_ShaNi
open Aeneas Aeneas.Std Result
set_option autoImplicit false
/-- Local normalized abef/cdgh stay in the loop; state is stored only at return. -/
def hardwareLoop (intr : Intrinsics) : List Block → State → Result State
  | [],state => ok state
  | block::tail,state => do
      let words ← intr.load block
      let after ← wordBlock intr state words
      hardwareLoop intr tail after

def digestBlocks (intr : Intrinsics) (state : State) (input : List Block) : Result State := do
  let packed ← intr.pack state
  let after ← hardwareLoop intr input packed
  intr.unpack after

theorem loop_refinement (intr : Intrinsics) (h : SHA_NI_IntrinsicsSemantics intr)
    (input : List Block) (state : State) :
    hardwareLoop intr input state=PV_RDB2F_SoftOuter.blocks input state := by
  induction input generalizing state with
  | nil => rfl
  | cons block tail ih =>
    simp only [hardwareLoop,PV_RDB2F_SoftOuter.blocks,h.load,word_block_semantics intr h]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro words hw
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro next hn
    exact ih next

theorem digest_blocks_refinement (intr : Intrinsics) (h : SHA_NI_IntrinsicsSemantics intr)
    (state : State) (input : List Block) :
    digestBlocks intr state input=PV_RDB2F_SoftOuter.compress state input := by
  simp only [digestBlocks,h.pack,bind_tc_ok,loop_refinement intr h,
    PV_RDB2F_SoftOuter.compress]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro after ha
  exact h.unpack after

def oneBlock (intr : Intrinsics) (state : State) (bytes : List U8) : Result State :=
  if h : bytes.length=64 then digestBlocks intr state [⟨bytes,h⟩] else fail .panic

theorem one_block_refinement (intr : Intrinsics) (h : SHA_NI_IntrinsicsSemantics intr) :
    oneBlock intr=PV_RDB2F_ConcreteSoft.software := by
  funext state bytes
  unfold oneBlock PV_RDB2F_ConcreteSoft.software
  split
  · rw [digest_blocks_refinement intr h]
    simp only [PV_RDB2F_SoftOuter.compress,PV_RDB2F_SoftOuter.blocks,bind_assoc_eq,bind_tc_ok]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro words hw
    cases PV_CBL_FallbackBlock.sha_fallback_reference.extracted_block state words <;> rfl
  · rfl

/-- Software is unconditional. The other reachable branch is conditional on the
single named instruction-semantics hypothesis, pending owner item 3. -/
theorem conditional_dispatch (intr : Intrinsics) (h : SHA_NI_IntrinsicsSemantics intr)
    (backend : PV_RDB2E_Dispatch.Backend) (frame : PV_RDB2E_ShaHandles.Frame)
    (valid : (PV_RDB2E_ShaHandles.position frame).val<64) :
    (do let after ← PV_RDB2E_ShaHandles.finalize
          (PV_RDB2E_Dispatch.select backend PV_RDB2F_ConcreteSoft.software (oneBlock intr)) frame valid
        ok (PV_RDB2E_ShaHandles.forget after))=
      PV_RDB2D_SHAState.completeState PV_RDB2F_ConcreteSoft.software frame.core frame.buffer
        (PV_RDB2E_ShaHandles.position frame) := by
  rw [one_block_refinement intr h]
  cases backend <;> exact PV_RDB2F_ConcreteSoft.all_fields frame valid

#print axioms loop_refinement
#print axioms digest_blocks_refinement
#print axioms one_block_refinement
#print axioms conditional_dispatch
end R1Z.PV_RDB2F_ShaNi
