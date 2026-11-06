import NLK_ParentFold
set_option autoImplicit false
namespace NLK_PdaDomains
def registry1 : List UInt8 := [97,115,112,105,115,45,118,101,114,105,102,105,101,114,45,114,101,103,105,115,116,114,121,45,118,49]
theorem registry1_length : registry1.length=26 := rfl
#print axioms registry1_length
def registry2 : List UInt8 := [97,115,112,105,115,45,118,101,114,105,102,105,101,114,45,114,101,103,105,115,116,114,121,45,118,50]
theorem registry2_length : registry2.length=26 := rfl
#print axioms registry2_length
def entry1 : List UInt8 := [97,115,112,105,115,45,118,101,114,105,102,105,101,114,45,101,110,116,114,121,45,118,49]
theorem entry1_length : entry1.length=23 := rfl
#print axioms entry1_length
def entry2 : List UInt8 := [97,115,112,105,115,45,118,101,114,105,102,105,101,114,45,101,110,116,114,121,45,118,50]
theorem entry2_length : entry2.length=23 := rfl
#print axioms entry2_length
def master : List UInt8 := [97,115,112,105,115,45,112,97,105,114,45,102,111,114,101,115,116,45,109,97,115,116,101,114,45,118,49]
theorem master_length : master.length=27 := rfl
#print axioms master_length
def checkpoint : List UInt8 := [97,115,112,105,115,45,112,97,105,114,45,102,111,114,101,115,116,45,99,104,101,99,107,112,111,105,110,116,45,118,49]
theorem checkpoint_length : checkpoint.length=31 := rfl
#print axioms checkpoint_length
def lane : List UInt8 := [97,115,112,105,115,45,112,97,105,114,45,102,111,114,101,115,116,45,108,97,110,101,45,118,49]
theorem lane_length : lane.length=25 := rfl
#print axioms lane_length

def Domain (seeds : List (List UInt8)) : Prop :=
 seeds.length≤16 ∧ ∀ seed, seed∈seeds → seed.length≤32

theorem registry_domain (tag key : List UInt8) (bump : UInt8)
    (ht : tag.length≤32) (hk : key.length=32) :
    Domain [tag,key,[bump]] := by
  constructor
  · simp only [List.length_cons,List.length_nil]; omega
  · intro seed member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h|h|h
    · simpa only [h] using ht
    · simp only [h,hk]; omega
    · simp only [h,List.length_cons,List.length_nil]; omega

theorem entry_domain (tag key profile release : List UInt8) (bump : UInt8)
    (ht : tag.length≤32) (hk : key.length=32)
    (hp : profile.length=32) (hr : release.length=32) :
    Domain [tag,key,profile,release,[bump]] := by
  constructor
  · simp only [List.length_cons,List.length_nil]; omega
  · intro seed member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h|h|h|h|h
    · simpa only [h] using ht
    · simp only [h,hk]; omega
    · simp only [h,hp]; omega
    · simp only [h,hr]; omega
    · simp only [h,List.length_cons,List.length_nil]; omega

theorem programdata_domain (key : List UInt8) (bump : UInt8) (hk : key.length=32) :
    Domain [key,[bump]] := by
  constructor
  · simp only [List.length_cons,List.length_nil]; omega
  · intro seed member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h|h
    · simp only [h,hk]; omega
    · simp only [h,List.length_cons,List.length_nil]; omega

#print axioms registry_domain
#print axioms entry_domain
#print axioms programdata_domain
end NLK_PdaDomains
