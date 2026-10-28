import NDO_JGv_FlushMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGv_LimbEquality
open Aeneas Aeneas.Std Result
abbrev K := SAQ_WideABI.K

theorem residue (x : U32) (n : Nat) (canonical : x.val<2147483647) (small : n<2147483647)
    (same : (x.val : JGv_QueryRows.F)=(n : JGv_QueryRows.F)) : x.val=n := by
  have hv := congrArg ZMod.val same
  simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt canonical,Nat.mod_eq_of_lt small] using hv
#print axioms residue

theorem source (q r : K) (qcanon : Port3_FlushInstall.Canonical q)
    (rcanon : Port3_FlushInstall.Canonical r)
    (same : ∀ k : Fin 4,((JGv_FlushMeaning.limb q k).val : JGv_QueryRows.F)=
      ((JGv_FlushMeaning.limb r k).val : JGv_QueryRows.F)) : q=r := by
  have h0 := residue q.c0.a r.c0.a.val qcanon.1 rcanon.1 (same ⟨0,by decide⟩)
  have h1 := residue q.c0.b r.c0.b.val qcanon.2.1 rcanon.2.1 (same ⟨1,by decide⟩)
  have h2 := residue q.c1.a r.c1.a.val qcanon.2.2.1 rcanon.2.2.1 (same ⟨2,by decide⟩)
  have h3 := residue q.c1.b r.c1.b.val qcanon.2.2.2 rcanon.2.2.2 (same ⟨3,by decide⟩)
  have e0 := UScalar.eq_of_val_eq h0
  have e1 := UScalar.eq_of_val_eq h1
  have e2 := UScalar.eq_of_val_eq h2
  have e3 := UScalar.eq_of_val_eq h3
  rcases q with ⟨⟨qa,qb⟩,⟨qc,qd⟩⟩
  rcases r with ⟨⟨ra,rb⟩,⟨rc,rd⟩⟩
  cases e0;cases e1;cases e2;cases e3;rfl
#print axioms source
end AspisR1.JGv_LimbEquality
end
