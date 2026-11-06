import NKR_SumFinishData
import NJL_EndpointLookup
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_SumLookupCertificate
open NKR_SumFinishData

/-- The additional metadata assertions ALREADY proved by
NJL_endpoint_lookup_cut(NJL_control.rs.txt,lines107..114):the exactgc/pc
values equal the source-key scans at the genuine endpoint group/local/pattern.
This is an(ai)(5) reviewed native cut,not any execution/field endpoint.
The main certificate must pin/revalidate that existing native pair. -/
def Cut (index : Fin 136) (consumer : Bool) : Prop :=
 NJL_EndpointLookup.gc index consumer=NJL_EndpointLookup.scanFrom
  (NJL_EndpointLookup.group index consumer,NJL_EndpointLookup.column index consumer) NJL_EndpointLookup.groupKeys 0 ∧
 NJL_EndpointLookup.pc index consumer=NJL_EndpointLookup.scanFrom
  (NJL_EndpointLookup.group index consumer,(NJL_EndpointLookup.endpoint index consumer).pattern.val,
   NJL_EndpointLookup.column index consumer) NJL_EndpointLookup.patternKeys 0

theorem scan_found {A : Type} [DecidableEq A] (key : A) (xs : List A) (start : Nat)
 (bounded : start+xs.length≤255) (found : NJL_EndpointLookup.scanFrom key xs start<255) :
 ∃ (i : Fin xs.length),NJL_EndpointLookup.scanFrom key xs start=start+i.val ∧ xs[i.val]=key := by
 induction xs generalizing start with
 | nil => simp only [NJL_EndpointLookup.scanFrom] at found;omega
 | cons x xs ih =>
  by_cases same : key=x
  · refine ⟨⟨0,by simp⟩,?_,?_⟩
    · simp only [NJL_EndpointLookup.scanFrom,if_pos same,Nat.add_zero]
    · exact same.symm
  · have tailFound : NJL_EndpointLookup.scanFrom key xs (start+1)<255 := by
     simpa only [NJL_EndpointLookup.scanFrom,if_neg same] using found
    obtain ⟨i,scan,read⟩ := ih (start+1) (by simp only [List.length_cons] at bounded;omega) tailFound
    refine ⟨⟨i.val+1,by have:=i.isLt;simp only [List.length_cons];omega⟩,?_,?_⟩
    · simp only [NJL_EndpointLookup.scanFrom,if_neg same,scan]
      omega
    · simpa only [List.getElem_cons_succ] using read

def patternGroup : Fin 43 → Fin 4 := ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,3,3,3,3,3]

theorem group_length : NJL_EndpointLookup.groupKeys.length=30 := by decide
theorem pattern_length : NJL_EndpointLookup.patternKeys.length=43 := by decide

theorem group_key (c : Fin 30) : NJL_EndpointLookup.groupKeys[c.val]'(by rw [group_length];exact c.isLt)=
 ((group c).val,(low c).val) := by fin_cases c <;> rfl

theorem pattern_key (c : Fin 43) : NJL_EndpointLookup.patternKeys[c.val]'(by rw [pattern_length];exact c.isLt)=
 ((patternGroup c).val,(NJB_PatternReference.pattern (pOut c)).val,(pLow c).val) := by fin_cases c <;> rfl

theorem column_mod (index : Fin 136) (consumer : Bool) :
 NJL_EndpointLookup.column index consumer=NJL_EndpointLookup.row index consumer%16 := by
 exact Nat.and_two_pow_sub_one_eq_mod (NJL_EndpointLookup.row index consumer) 4

/-- A symbolic scan proof derives exact endpoint-key associations without
normalizing the136-link registry or inventing a new native assertion. -/
theorem keys (index : Fin 136) (consumer : Bool) (bounds : NJL_EndpointLookup.Cut index consumer)
 (cut : Cut index consumer) :
 ((group (NJL_EndpointLookup.groupIndex index consumer bounds)).val,
  (low (NJL_EndpointLookup.groupIndex index consumer bounds)).val)=
 (NJL_EndpointLookup.group index consumer,NJL_EndpointLookup.column index consumer) ∧
 ((patternGroup (NJL_EndpointLookup.patternIndex index consumer bounds)).val,
  (NJB_PatternReference.pattern (pOut (NJL_EndpointLookup.patternIndex index consumer bounds))).val,
  (pLow (NJL_EndpointLookup.patternIndex index consumer bounds)).val)=
 (NJL_EndpointLookup.group index consumer,(NJL_EndpointLookup.endpoint index consumer).pattern.val,
  NJL_EndpointLookup.column index consumer) := by
 obtain ⟨g,hg,vg⟩ := scan_found
  (NJL_EndpointLookup.group index consumer,NJL_EndpointLookup.column index consumer)
  NJL_EndpointLookup.groupKeys 0 (by rw [group_length];decide) (by rw [←cut.1];have:=bounds.2.1;omega)
 obtain ⟨p,hp,vp⟩ := scan_found
  (NJL_EndpointLookup.group index consumer,(NJL_EndpointLookup.endpoint index consumer).pattern.val,NJL_EndpointLookup.column index consumer)
  NJL_EndpointLookup.patternKeys 0 (by rw [pattern_length];decide) (by rw [←cut.2];have:=bounds.2.2;omega)
 have gi : g.val=NJL_EndpointLookup.gc index consumer := by rw [cut.1,hg];omega
 have pi : p.val=NJL_EndpointLookup.pc index consumer := by rw [cut.2,hp];omega
 constructor
 · have v := vg
   have eq : g.val=(NJL_EndpointLookup.groupIndex index consumer bounds).val := gi
   rw [eq,group_key] at v
   exact v
 · have v := vp
   have eq : p.val=(NJL_EndpointLookup.patternIndex index consumer bounds).val := pi
   rw [eq,pattern_key] at v
   exact v

#print axioms scan_found
#print axioms group_length
#print axioms pattern_length
#print axioms group_key
#print axioms pattern_key
#print axioms column_mod
#print axioms keys
end AspisR1.NKR_SumLookupCertificate
end
