import NGA_ChannelAlgebra
set_option autoImplicit false
namespace NGA_CacheValues
open Aeneas Aeneas.Std Result AspisR1SelectedMaskProbe NGA_Cell NGA_Converter
abbrev Qm := NGA_Cache.Q

theorem source (x : Qm) (hx : NGA_Cache.Canonical x) (cache : NGA_Cache.Cache)
 (run : NGA_Cache.prelude x=ok cache) (d : Cell) :
 ((get cache d).val : M)=NGA_ChannelAlgebra.channels x d := by
 obtain ⟨s,hs,hsc,vs0,vs1⟩ := AspisR1.ExtractedMaskTowerAdd.current_cm_add_mod x.c0 x.c1 hx.1 hx.2
 obtain ⟨a,ha,va,_⟩ := AspisR1.ExtractedMaskM31AddSub.current_add_mod x.c0.a x.c0.b hx.1.1 hx.1.2
 obtain ⟨b,hb,vb,_⟩ := AspisR1.ExtractedMaskM31AddSub.current_add_mod x.c1.a x.c1.b hx.2.1 hx.2.2
 obtain ⟨c,hc,vc,_⟩ := AspisR1.ExtractedMaskM31AddSub.current_add_mod s.a s.b hsc.1 hsc.2
 simp only [NGA_Cache.prelude,hs,ha,hb,hc,bind_tc_ok] at run
 cases Result.ok.inj run
 rcases d with ⟨i,j⟩
 fin_cases i <;> fin_cases j <;>
   simp [get,at3,NGA_ChannelAlgebra.channels,NGA_ChannelAlgebra.component,
     NGA_ChannelAlgebra.decodeQ,AspisR1.ExtractedMaskQM31Exact.decode,
     va,vb,vc,vs0,vs1,ZMod.natCast_mod,Nat.cast_add]

#print axioms source
end NGA_CacheValues
