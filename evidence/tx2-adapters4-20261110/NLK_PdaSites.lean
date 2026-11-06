import NLK_PdaDomains
set_option autoImplicit false
namespace NLK_PdaSites
open NLK_PdaDomains
/-- Native fixed-array keys give32 bytes without a caller precondition. -/
theorem registry1_ready (key : Fin 32 → UInt8) (bump : UInt8) :
    Domain [registry1,List.ofFn key,[bump]] := by
  apply registry_domain
  · rw [registry1_length]; omega
  · simp only [List.length_ofFn]

theorem registry2_ready (key : Fin 32 → UInt8) (bump : UInt8) :
    Domain [registry2,List.ofFn key,[bump]] := by
  apply registry_domain
  · rw [registry2_length]; omega
  · simp only [List.length_ofFn]

theorem entry1_ready (key profile release : Fin 32 → UInt8) (bump : UInt8) :
    Domain [entry1,List.ofFn key,List.ofFn profile,List.ofFn release,[bump]] := by
  apply entry_domain
  · rw [entry1_length]; omega
  · simp only [List.length_ofFn]
  · simp only [List.length_ofFn]
  · simp only [List.length_ofFn]

theorem entry2_ready (key profile release : Fin 32 → UInt8) (bump : UInt8) :
    Domain [entry2,List.ofFn key,List.ofFn profile,List.ofFn release,[bump]] := by
  apply entry_domain
  · rw [entry2_length]; omega
  · simp only [List.length_ofFn]
  · simp only [List.length_ofFn]
  · simp only [List.length_ofFn]

theorem programdata_ready (key : Fin 32 → UInt8) (bump : UInt8) :
    Domain [List.ofFn key,[bump]] :=
  programdata_domain _ _ (by simp only [List.length_ofFn])

/--233's master PDA has the same3-descriptor shape; the actual tag is pinned. -/
theorem master_ready (mint : Fin 32 → UInt8) (bump : UInt8) :
    Domain [master,List.ofFn mint,[bump]] := by
  apply registry_domain
  · rw [master_length]; omega
  · simp only [List.length_ofFn]

theorem checkpoint_ready (key : Fin 32 → UInt8) (sequence : Fin 8 → UInt8) (bump : UInt8) :
    Domain [checkpoint,List.ofFn key,List.ofFn sequence,[bump]] := by
  constructor
  · simp only [List.length_cons,List.length_nil]; omega
  · intro seed member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h|h|h|h
    · rw [h,checkpoint_length]; omega
    · simp only [h,List.length_ofFn]; omega
    · simp only [h,List.length_ofFn]; omega
    · simp only [h,List.length_cons,List.length_nil]; omega

theorem lane_ready (key : Fin 32 → UInt8) (output bump : UInt8) :
    Domain [lane,List.ofFn key,[output],[bump]] := by
  constructor
  · simp only [List.length_cons,List.length_nil]; omega
  · intro seed member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h|h|h|h
    · rw [h,lane_length]; omega
    · simp only [h,List.length_ofFn]; omega
    · simp only [h,List.length_cons,List.length_nil]; omega
    · simp only [h,List.length_cons,List.length_nil]; omega

#print axioms registry1_ready
#print axioms registry2_ready
#print axioms entry1_ready
#print axioms entry2_ready
#print axioms programdata_ready
#print axioms master_ready
#print axioms checkpoint_ready
#print axioms lane_ready
end NLK_PdaSites
