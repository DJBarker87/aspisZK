import NHF_Prefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHF_HeapPrefix
open Aeneas Aeneas.Std Result
/-- Both actual reservation outcomes; no allocator-success premise. The
successful content is symbolic replicate, never kernel-normalized bytewise. -/
theorem outcome (reserved : Bool) :
 if reserved then ∃ logical : alloc.vec.Vec U8,
   OraclePortStdAllocation.filled 14759#usize 0#u8 reserved=ok (.ok logical) ∧
   logical.val.length=14759
 else OraclePortStdAllocation.filled 14759#usize 0#u8 reserved=
   ok (.error .allocation) := by
 rw [OraclePortStdAllocation.filled_exact]
 cases reserved <;> simp only [Bool.false_eq_true,↓reduceIte,OraclePortStdAllocation.filledSpec]
 exact ⟨_,rfl,by simp only [List.length_replicate,UScalar.ofNatCore_val_eq]⟩
/-- An observed successful owned heap reply establishes the next stage domain;
its size and the reservation outcome are consequences of the full callee law. -/
theorem success_domain (reserved : Bool) (logical : alloc.vec.Vec U8)
 (run : OraclePortStdAllocation.filled 14759#usize 0#u8 reserved=ok (.ok logical)) :
 reserved=true ∧ logical.val.length=14759 := by
 rw [OraclePortStdAllocation.filled_exact] at run
 cases reserved with
 | false=>cases run
 | true=>
  have same : (⟨List.replicate 14759 0#u8,by simp only [List.length_replicate];scalar_tac⟩ : alloc.vec.Vec U8)=logical := by
   exact Except.ok.inj (Result.ok.inj run)
  exact ⟨rfl,by rw [←same];simp only [List.length_replicate]⟩
/-- No continuation, mutable-state update or observer event is introduced on
allocation rejection. Runtime allocation/Drop realization stays retained. -/
theorem rejection_frame {State Event : Type} (state : State) :
 (do let result←OraclePortStdAllocation.filled 14759#usize 0#u8 false
     ok (result,state,([] : List Event)))=
 ok (.error .allocation,state,([] : List Event)) := by
 rw [OraclePortStdAllocation.filled_exact]
 rfl
#print axioms outcome
#print axioms success_domain
#print axioms rejection_frame
end AspisR1.NHF_HeapPrefix
end
