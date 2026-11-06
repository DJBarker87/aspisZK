from pathlib import Path
E=Path(__file__).resolve().parent
names={'registry1':b'aspis-verifier-registry-v1','registry2':b'aspis-verifier-registry-v2','entry1':b'aspis-verifier-entry-v1','entry2':b'aspis-verifier-entry-v2','master':b'aspis-pair-forest-master-v1','checkpoint':b'aspis-pair-forest-checkpoint-v1','lane':b'aspis-pair-forest-lane-v1'}
s='import NLK_ParentFold\nset_option autoImplicit false\nnamespace NLK_PdaDomains\n'
for n,b in names.items():
 s+=f'def {n} : List UInt8 := ['+','.join(str(x) for x in b)+']\n'
 s+=f'theorem {n}_length : {n}.length={len(b)} := rfl\n#print axioms {n}_length\n'
s+='''
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
'''
(E/'NLK_PdaDomains.lean').write_text(s)
