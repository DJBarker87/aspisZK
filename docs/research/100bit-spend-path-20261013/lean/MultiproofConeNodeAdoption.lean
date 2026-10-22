import MultiproofConeNodeIteration

set_option autoImplicit false
namespace AspisR1.MultiproofConeNodeAdoption
open Aeneas Aeneas.Std Result MultiproofConeRef
open MultiproofConeNodeDomain MultiproofConeNodeIteration MultiproofConeLevelIteration

/-- Bounded source level obtained by one-node iteration. The production loop
factoring and the local certificate remain the named P6 source boundary. -/
def level (source : Step) (s : reference.Scratch) : Result reference.Level :=
  rows source s.n.val s 0#usize 0#usize

theorem level_eq {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (total : HashTotal D hash) (physical : Slice U8) (source : Step)
    (node_certificate : ∀ s i w, RowDomain physical s i w → i.val < s.n.val →
      source s i w=reference.binary_step D hash s physical i w)
    (s : reference.Scratch) (domain : Domain physical s) :
    level source s=reference.level_rows D hash s physical 0#usize 0#usize := by
  have rowDomain : RowDomain physical s 0#usize 0#usize :=
    ⟨domain.1,domain.2.1,by simp,by simp,domain.2.2⟩
  exact (rows_congr D hash total physical source node_certificate s.n.val s _ _ rowDomain).trans
    (rows_eq_extracted D hash total physical s.n.val s _ _ rowDomain (by simp)).symm

/-- The previous level-preservation premise is derived, not retained. -/
theorem level_preserves {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (total : HashTotal D hash) (physical : Slice U8) (source : Step)
    (node_certificate : ∀ s i w, RowDomain physical s i w → i.val < s.n.val →
      source s i w=reference.binary_step D hash s physical i w)
    (s : reference.Scratch) (domain : Domain physical s) (next : reference.Scratch)
    (success : level source s=ok (.Done next)) : Domain physical next := by
  rw [level_eq D hash total physical source node_certificate s domain] at success
  exact level_preserve D hash total physical s next domain success

/-- Height-18 adoption from local node equality; no complete-level equality
or level-domain-preservation assumption remains. This is full Result/state
identity to the extracted reference, and does not assert model-log identity. -/
theorem eighteen_eq {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (total : HashTotal D hash) (physical : Slice U8) (source : Step)
    (node_certificate : ∀ s i w, RowDomain physical s i w → i.val < s.n.val →
      source s i w=reference.binary_step D hash s physical i w)
    (s : reference.Scratch) (domain : Domain physical s) :
    iterate (level source) 18 s=reference.levels D hash s physical 18#u32 := by
  rw [levels_eq_iteration D hash physical 18#u32 (by decide) s]
  exact iterate_congr_on (Domain physical) (level source) _
    (level_eq D hash total physical source node_certificate)
    (level_preserves D hash total physical source node_certificate) 18 s domain

/-- Coordinate certificates quantify independently over every index and byte;
this kernel lemma supplies whole-array equality rather than a selected-byte
postcondition being treated as an entire contract by a caller stub. -/
theorem array_ext {α : Type} {n : Usize} (a b : Array α n)
    (coordinates : ∀ j (ha : j<a.val.length) (hb : j<b.val.length),
      a.val[j]=b.val[j]) : a=b := by
  apply Subtype.ext
  apply List.ext_getElem
  · exact a.property.trans b.property.symm
  · exact coordinates

theorem scratch_ext (a b : reference.Scratch) (n : a.n=b.n) (cursor : a.«at»=b.«at»)
    (indices : a.idx=b.idx) (digests : ∀ j (ha : j<a.val.val.length) (hb : j<b.val.val.length),
      (a.val.val[j]).val=(b.val.val[j]).val) : a=b := by
  have values : a.val=b.val := array_ext _ _ (fun j ha hb => Subtype.ext (digests j ha hb))
  cases a;cases b;simp_all

#print axioms level_eq
#print axioms level_preserves
#print axioms eighteen_eq
#print axioms array_ext
#print axioms scratch_ext
end AspisR1.MultiproofConeNodeAdoption
