import XSg_PhaseNat
import XRu_PushTransport
import XSe_PowerDomain
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSg_RowPhase
abbrev Row := XRu_RowShape.Row
def Bound (t : Nat) (row : Row) : Prop :=
 ∀ x∈row.val,x.val<2^34+(t%4)*(2^31-2)^2
/-- Canonical source limbs supply the exact emitted scalar domain. -/
theorem safe (row : Row) (q : aspis_core.field.QM31) (basis : U32) (t : Nat)
 (canon : XRp_PowersQAdd.CanonicalQ q) (bm : basis.val<2^31-1) (phase : Bound t row) :
 ∀ j raw, j.val<4 → Array.index_usize row j=ok raw →
 raw.val+(S7Kani2OwnedRow.limb (XRu_PushTransport.power q) j).val*basis.val<2^64 := by
 intro j raw hj hread
 obtain ⟨x,hx,hval⟩ := WP.spec_imp_exists (Array.index_usize_spec row j (by simpa only [Array.length,row.property] using hj))
 cases Result.ok.inj (hx.symm.trans hread)
 have member : raw∈row.val := by rw [hval]; exact List.getElem_mem _
 have hc : (S7Kani2OwnedRow.limb (XRu_PushTransport.power q) j).val<2^31-1 := by
  rcases canon with ⟨⟨ha,hb⟩,⟨hc,hd⟩⟩
  unfold S7Kani2OwnedRow.limb XRu_PushTransport.power
  split <;> (first | exact ha | split <;> (first | exact hb | split <;> assumption))
 exact S7OwnedP6ScalarProof.phase_bound raw _ basis (t%4) (Nat.mod_lt _ (by decide)) hc bm (phase raw member)
/-- The complete emitted four-limb update preserves the next periodic phase. -/
theorem source (row out : Row) (q : aspis_core.field.QM31) (basis : U32) (terms : Usize)
 (canon : XRp_PowersQAdd.CanonicalQ q) (bm : basis.val<2^31-1)
 (phase : Bound terms.val row)
 (run : verifier.update_residue_row row q basis ((terms &&& 3#usize)=3#usize)=ok out) :
 Bound (terms.val+1) out := by
 obtain ⟨a,b,c,d,shape⟩ := XRu_RowShape.cells row
 subst row
 let x : Fin 4 → U64 := fun j => if j=0 then a else if j=1 then b else if j=2 then c else d
 have shaped : S7Kani2OwnedRowRefinement.makeRow x=Array.make 4#usize [a,b,c,d] := by rfl
 have xp : ∀ j, (x j).val<2^34+(terms.val%4)*(2^31-2)^2 := by
  intro j; fin_cases j <;> apply phase <;> simp [x,Array.make]
 obtain ⟨y,hy,hval⟩ := S7Kani2OwnedRowRefinement.literal_row_refines_model x
  (XRu_PushTransport.power q) basis terms.val (XSe_PowerDomain.source q canon) bm xp
 have eq := XRu_RowBoth.source (Array.make 4#usize [a,b,c,d]) q basis
  ((terms &&& 3#usize)=3#usize) (safe _ q basis terms.val canon bm phase)
 rw [shaped] at hy
 simp only [S7Kani2OwnedPushModel.phase_flag] at eq run
 have same := Result.ok.inj ((eq.trans hy).symm.trans run)
 rw [←same]
 intro z hz
 simp only [S7Kani2OwnedRowRefinement.makeRow,Array.make,List.mem_cons,List.not_mem_nil,or_false] at hz
 have yp : ∀ j, (y j).val<2^34+((terms.val+1)%4)*(2^31-2)^2 := by
  intro j; rw [hval]; exact XSg_PhaseNat.source _ _ _ _ (XSe_PowerDomain.source q canon j) bm (xp j)
 rcases hz with rfl|rfl|rfl|rfl <;> exact yp _
#print axioms safe
#print axioms source
end XSg_RowPhase
