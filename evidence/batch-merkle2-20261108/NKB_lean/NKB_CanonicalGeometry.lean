import NKB_ScanWindows
set_option autoImplicit false
namespace NKB_CanonicalGeometry

def Matrix (word : Nat→Prop) : Prop :=
 (∀ s,s<4→∀ l,l<26→word (s*120+l*4)) ∧
 (∀ s,s<4→∀ w,w<4→word (s*120+104+w*4)) ∧
 (∀ s,s<4→∀ l,l<2→∀ w,w<4→word (480+s*32+l*16+w*4))

/-- The emitted scalar/K iteration geometry covers each word of [0,608)
exactly within its native caller bounds, with no field-canonicality premise. -/
theorem cover (j : Nat) (bound : j<152) :
 (∃ s l,s<4 ∧ l<26 ∧ j*4=s*120+l*4) ∨
 (∃ s w,s<4 ∧ w<4 ∧ j*4=s*120+104+w*4) ∨
 (∃ s l w,s<4 ∧ l<2 ∧ w<4 ∧ j*4=480+s*32+l*16+w*4) := by
 by_cases first : j<120
 · by_cases scalar : j%30<26
   · exact Or.inl ⟨j/30,j%30,by omega,scalar,by omega⟩
   · exact Or.inr (Or.inl ⟨j/30,j%30-26,by omega,by omega,by omega⟩)
 · exact Or.inr (Or.inr ⟨(j-120)/8,((j-120)%8)/4,(j-120)%4,
     by omega,by omega,by omega,by omega⟩)

/-- Regrouping the source's interleaved M31/K reads changes no accepted or
rejected word. This lemma is independent of source-step Result transport. -/
theorem contiguous (word : Nat→Prop) : Matrix word ↔ ∀ j,j<152→word (j*4) := by
 constructor
 · rintro ⟨scalar,c1,c2⟩ j bound
   rcases cover j bound with ⟨s,l,hs,hl,same⟩|⟨s,w,hs,hw,same⟩|⟨s,l,w,hs,hl,hw,same⟩
   · rw [same];exact scalar s hs l hl
   · rw [same];exact c1 s hs w hw
   · rw [same];exact c2 s hs l hl w hw
 · intro all
   refine ⟨?_,?_,?_⟩
   · intro s hs l hl
     have h:=all (s*30+l) (by omega)
     simpa only [Nat.add_mul,Nat.mul_assoc,show 30*4=120 from rfl] using h
   · intro s hs w hw
     have h:=all (s*30+26+w) (by omega)
     simpa only [Nat.add_mul,Nat.mul_assoc,show 30*4=120 from rfl,show 26*4=104 from rfl] using h
   · intro s hs l hl w hw
     have h:=all (120+s*8+l*4+w) (by omega)
     simpa only [Nat.add_mul,Nat.mul_assoc,show 120*4=480 from rfl,show 8*4=32 from rfl,show 4*4=16 from rfl] using h

/-- Salts [608,672) and [800,832) stay outside every source field read. -/
theorem salts (s l w : Nat) (slot : s<4) (lane : l<2) (word : w<4) :
 480+s*32+l*16+w*4+4≤608 ∧ 608≤672 ∧ 800≤832 := by omega

#print axioms cover
#print axioms contiguous
#print axioms salts
end NKB_CanonicalGeometry
