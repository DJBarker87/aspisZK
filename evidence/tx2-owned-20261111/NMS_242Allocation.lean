import NMS_Owned242
set_option autoImplicit false
namespace NMS_242Allocation
open Aeneas Aeneas.Std AdapterRw NMS_OwnedPackets NMS_RowSpec242

theorem scan_fresh (inputs : List Nat) (auth : Auth) :
 NMS_Fresh.next (inputs ++ auth.owners) ∉ inputs := by
 intro member
 exact NMS_Fresh.fresh _ (List.mem_append.mpr (.inl member))

theorem statement_fresh (inputs : List Nat) (auth : Auth) (candidate : Box Candidate) :
 NMS_Fresh.next (inputs ++ auth.owners ++ [candidate.owner]) ∉ inputs ∧
 NMS_Fresh.next (inputs ++ auth.owners ++ [candidate.owner]) ∉ auth.owners ∧
 NMS_Fresh.next (inputs ++ auth.owners ++ [candidate.owner]) ≠ candidate.owner := by
 constructor
 · intro member
   exact NMS_Fresh.fresh _ (List.mem_append.mpr (.inl (List.mem_append.mpr (.inl member))))
 constructor
 · intro member
   exact NMS_Fresh.fresh _ (List.mem_append.mpr (.inl (List.mem_append.mpr (.inr member))))
 · intro same
   apply NMS_Fresh.fresh (inputs ++ auth.owners ++ [candidate.owner])
   rw [same]
   exact List.mem_append.mpr (.inr (List.mem_singleton.mpr rfl))

/-- The rich scanner event keeps its newly allocated candidate owner even on
an arbitrary successful typed payload; abort/rejection do not invent one. -/
theorem scan_events {Ambient : Type} (ops : Ops) (inputs : List Nat) (auth : Auth) (bytes : Slice U8) :
 ∀ e ∈ (NMS_Owned242.scan (Ambient := Ambient) ops inputs auth bytes).events,
 e.Owners inputs := by
 cases h : ops.op51 bytes with
 | ok reply =>
  cases reply with
  | Ok scanned =>
   simpa only [NMS_Owned242.scan,h,mapReply,NJU_Log.record,List.mem_cons,List.not_mem_nil,
    or_false,forall_eq,Event.Owners] using (scan_fresh inputs auth)
  | Err error => simp only [NMS_Owned242.scan,h,mapReply,NJU_Log.record,List.mem_cons,
    List.not_mem_nil,or_false,forall_eq,Event.Owners]
 | fail error => simp only [NMS_Owned242.scan,h,mapReply,NJU_Log.record,List.mem_cons,
    List.not_mem_nil,or_false,forall_eq,Event.Owners]
 | div => simp only [NMS_Owned242.scan,h,mapReply,NJU_Log.record,List.mem_cons,
    List.not_mem_nil,or_false,forall_eq,Event.Owners]

#print axioms scan_fresh
#print axioms statement_fresh
#print axioms scan_events
end NMS_242Allocation
