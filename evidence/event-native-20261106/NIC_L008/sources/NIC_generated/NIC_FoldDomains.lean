import NFS_FoldInstall
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIC_FoldDomains
open Aeneas Aeneas.Std Result AspisR1CurrentWide
open AspisR1CurrentWide.Proof

/-- Intermediates are obtained from total source execution on the exact caller
domain, never from a supplied successful fold or arbitrary intermediate states. -/
theorem circle (alpha a b c d : E) (ix iy lx ly lz : U32)
 (domain : NEI_CircleDomains.Domain alpha (Array.make 4#usize [a,b,c,d])) :
 ∃ out, ∃ cut : FIp_CircleCuts.Cuts alpha a b c d ix iy out,
 FIp_CircleSource.circle alpha (Array.make 4#usize [a,b,c,d])
   (Array.make 5#usize [ix,iy,lx,ly,lz])=ok out ∧
 NEI_CircleDomains.Intermediates cut := by
 obtain ⟨out,source,_⟩ := NEI_CircleDomains.total alpha
   (Array.make 4#usize [a,b,c,d]) (Array.make 5#usize [ix,iy,lx,ly,lz]) domain
 obtain ⟨cut⟩ := FIp_CircleCuts.cuts alpha a b c d out ix iy lx ly lz source
 refine ⟨out,cut,source,NEI_CircleDomains.same_site_domains alpha a b c d out ix iy cut ?_ ?_ ?_ ?_⟩
 · exact domain.2 a (by simp [Array.make])
 · exact domain.2 b (by simp [Array.make])
 · exact domain.2 c (by simp [Array.make])
 · exact domain.2 d (by simp [Array.make])

theorem line (alpha a b c d : E) (ix iy lx ly lz : U32)
 (domain : NEI_LineDomains.Domain alpha (Array.make 4#usize [a,b,c,d])) :
 ∃ out, ∃ cut : SAQ_LineSource.Cuts alpha a b c d lx ly lz out,
 SAQ_LineSource.line alpha (Array.make 4#usize [a,b,c,d])
   (Array.make 5#usize [ix,iy,lx,ly,lz])=ok out ∧
 NEI_LineDomains.Intermediates cut := by
 obtain ⟨out,cohort,_⟩ := NEI_LineDomains.total alpha
   (Array.make 4#usize [a,b,c,d]) (Array.make 5#usize [ix,iy,lx,ly,lz]) domain
 have source := (NEG_FoldAssociation.line alpha
   (Array.make 4#usize [a,b,c,d]) (Array.make 5#usize [ix,iy,lx,ly,lz])).symm.trans cohort
 obtain ⟨cut⟩ := SAQ_LineSource.cuts alpha a b c d out ix iy lx ly lz source
 refine ⟨out,cut,source,NEI_LineDomains.same_site_domains alpha a b c d out lx ly lz cut domain.1 ?_ ?_ ?_ ?_⟩
 · exact domain.2 a (by simp [Array.make])
 · exact domain.2 b (by simp [Array.make])
 · exact domain.2 c (by simp [Array.make])
 · exact domain.2 d (by simp [Array.make])

#print axioms circle
#print axioms line
end AspisR1.NIC_FoldDomains
