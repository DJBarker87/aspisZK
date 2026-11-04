import NFQ_COMBINED_IMPORT
set_option autoImplicit false
namespace NFQ_Linear
open Aeneas Aeneas.Std Result
open AspisR1.ExtractedMaskTowerAdd
abbrev C := AspisR1SelectedMaskProbe.field.CM31

theorem source (x : C) (canonical : CanonicalCM x) :
    ∃ z : C, AspisR1SelectedMaskProbe.state_only_hiding.cm31_mul_r x=ok z ∧
      CanonicalCM z ∧
      z.a.val=(((x.a.val+x.a.val)%2147483647)+2147483647-x.b.val)%2147483647 ∧
      z.b.val=(x.a.val+((x.b.val+x.b.val)%2147483647))%2147483647 := by
  obtain ⟨aa,ra,va,ca⟩ := AspisR1.ExtractedMaskM31AddSub.current_add_mod x.a x.a canonical.1 canonical.1
  obtain ⟨bb,rb,vb,cb⟩ := AspisR1.ExtractedMaskM31AddSub.current_add_mod x.b x.b canonical.2 canonical.2
  obtain ⟨a,sa,pa,ac⟩ := AspisR1.ExtractedMaskM31AddSub.current_sub_mod aa x.b ca canonical.2
  obtain ⟨b,sb,pb,bc⟩ := AspisR1.ExtractedMaskM31AddSub.current_add_mod x.a bb canonical.1 cb
  refine ⟨⟨a,b⟩,?_,⟨ac,bc⟩,?_,?_⟩
  · simp only [AspisR1SelectedMaskProbe.state_only_hiding.cm31_mul_r,
      AspisR1SelectedMaskProbe.field.M31.double,ra,rb,sa,sb,
      AspisR1SelectedMaskProbe.field.CM31.new,bind_tc_ok]
  · simpa only [va] using pa
  · simpa only [vb] using pb
#print axioms source
end NFQ_Linear
