import NGA_SmallResult
import RPv_AspisR1_PoseidonPreparedKaratsubaValue
set_option autoImplicit false
namespace NGA_Converter
open Aeneas Aeneas.Std Result NGA_Cell
abbrev M := AspisV8R15.ExactTowerBase.M31Exact
abbrev C := AspisV8R15.ExactTowerBase.CM31Exact
abbrev Q := AspisV8R15.ExactTowerBase.QM31Exact
abbrev State := Cell → M

def row (s : State) (i : Fin 3) : C := ⟨s (i,0)-s (i,1),s (i,2)-s (i,0)-s (i,1)⟩
def interpret (s : State) : Q := ⟨row s 0+(⟨2,1⟩ : C)*row s 1,row s 2-row s 0-row s 1⟩
def decode (s : Sums) : State := fun d => ((get s d).val : M)

theorem value (s : Sums) : ∃ out,
 NGA_SmallResult.convert s=ok out ∧ NGA_Cache.Canonical out ∧
 AspisR1.PoseidonPreparedKaratsubaValue.decodeQM out=interpret (decode s) := by
 obtain ⟨r0,r1,r2,a00,a01,a02,a10,a11,a12,a20,a21,a22,m0,m1,m2,out,
   hr0,hr1,hr2,h00,h01,h02,h10,h11,h12,h20,h21,h22,
   _,_,_,_,_,_,ho,hc,_,_,_,hv⟩ := AspisR1.PoseidonPreparedKaratsubaValue.converter_value s
 have er0 : r0=at3 s 0 := Result.ok.inj (hr0.symm.trans (NGA_Cell.index _ s 0))
 subst r0
 have er1 : r1=at3 s 1 := Result.ok.inj (hr1.symm.trans (NGA_Cell.index _ s 1))
 subst r1
 have er2 : r2=at3 s 2 := Result.ok.inj (hr2.symm.trans (NGA_Cell.index _ s 2))
 subst r2
 have e00 : a00=get s (0,0) := Result.ok.inj (h00.symm.trans (NGA_Cell.index _ (at3 s 0) 0))
 subst a00
 have e01 : a01=get s (0,1) := Result.ok.inj (h01.symm.trans (NGA_Cell.index _ (at3 s 0) 1))
 subst a01
 have e02 : a02=get s (0,2) := Result.ok.inj (h02.symm.trans (NGA_Cell.index _ (at3 s 0) 2))
 subst a02
 have e10 : a10=get s (1,0) := Result.ok.inj (h10.symm.trans (NGA_Cell.index _ (at3 s 1) 0))
 subst a10
 have e11 : a11=get s (1,1) := Result.ok.inj (h11.symm.trans (NGA_Cell.index _ (at3 s 1) 1))
 subst a11
 have e12 : a12=get s (1,2) := Result.ok.inj (h12.symm.trans (NGA_Cell.index _ (at3 s 1) 2))
 subst a12
 have e20 : a20=get s (2,0) := Result.ok.inj (h20.symm.trans (NGA_Cell.index _ (at3 s 2) 0))
 subst a20
 have e21 : a21=get s (2,1) := Result.ok.inj (h21.symm.trans (NGA_Cell.index _ (at3 s 2) 1))
 subst a21
 have e22 : a22=get s (2,2) := Result.ok.inj (h22.symm.trans (NGA_Cell.index _ (at3 s 2) 2))
 subst a22
 refine ⟨out,ho,hc,?_⟩
 exact hv

#print axioms value
end NGA_Converter
