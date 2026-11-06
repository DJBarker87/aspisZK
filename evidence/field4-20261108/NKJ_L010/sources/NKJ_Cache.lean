import NKJ_Wrap32
import NGA_CacheDomain
set_option autoImplicit false
namespace NKJ_Cache
open Aeneas Aeneas.Std Result AspisR1SelectedMaskProbe
abbrev Q := NGA_Cache.Q

def words (q : Q) : Array U32 4#usize := Array.make 4#usize [q.c0.a,q.c0.b,q.c1.a,q.c1.b]

theorem source (q : Q) (hq : NGA_Cache.Canonical q) :
 NKJ_Extracted.field.NKJ_reference.NKJ_channels (words q)=NGA_Cache.prelude q := by
 obtain ⟨a,ha,_,ca⟩ := AspisR1.ExtractedMaskM31AddSub.current_add_mod q.c0.a q.c1.a hq.1.1 hq.2.1
 obtain ⟨b,hb,_,cb⟩ := AspisR1.ExtractedMaskM31AddSub.current_add_mod q.c0.b q.c1.b hq.1.2 hq.2.2
 obtain ⟨c,hc,_,_⟩ := AspisR1.ExtractedMaskM31AddSub.current_add_mod q.c0.a q.c0.b hq.1.1 hq.1.2
 obtain ⟨d,hd,_,_⟩ := AspisR1.ExtractedMaskM31AddSub.current_add_mod q.c1.a q.c1.b hq.2.1 hq.2.2
 obtain ⟨e,he,_,_⟩ := AspisR1.ExtractedMaskM31AddSub.current_add_mod a b ca cb
 have hs : field.CM31.add q.c0 q.c1=ok ⟨a,b⟩ := by
  simp only [field.CM31.add,ha,hb,bind_tc_ok]
 have na := (NKJ_Wrap32.add q.c0.a q.c1.a hq.1.1 hq.2.1).trans ha
 have nb := (NKJ_Wrap32.add q.c0.b q.c1.b hq.1.2 hq.2.2).trans hb
 have nc := (NKJ_Wrap32.add q.c0.a q.c0.b hq.1.1 hq.1.2).trans hc
 have nd := (NKJ_Wrap32.add q.c1.a q.c1.b hq.2.1 hq.2.2).trans hd
 have ne := (NKJ_Wrap32.add a b ca cb).trans he
 simp [NKJ_Extracted.field.NKJ_reference.NKJ_channels,words,Array.index_usize,
   Array.make,na,nb,nc,nd,ne,NGA_Cache.prelude,hs,hc,hd,he]
#print axioms source
end NKJ_Cache
