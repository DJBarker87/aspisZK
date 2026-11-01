import NEI_LineDomains
import NEB_PureFrame
import SAQ_LineJoin
set_option autoImplicit false
noncomputable section
namespace NEI_LineCertificate
open Aeneas Aeneas.Std Result AspisR1 AspisR1CurrentWide AspisR1CurrentWide.Proof
open SAQ_LineSource

/-- Reconstruct the complete emitted Result from the same ordered call cuts. -/
theorem reconstruct (alpha a b c d out : E) (ix iy lx ly lz : U32)
    (cut : Cuts alpha a b c d lx ly lz out) :
    NEG_FoldsTypes.line_fold_with_inverses alpha
      (Array.make 4#usize [a,b,c,d])
      (Array.make 5#usize [ix,iy,lx,ly,lz]) = ok out := by
  rw [NEG_FoldAssociation.line]
  have ia0 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 0#usize=ok a := rfl
  have ia1 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 1#usize=ok b := rfl
  have ia2 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 2#usize=ok c := rfl
  have ia3 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 3#usize=ok d := rfl
  have ii2 : Array.index_usize (Array.make 5#usize [ix,iy,lx,ly,lz]) 2#usize=ok lx := rfl
  have ii3 : Array.index_usize (Array.make 5#usize [ix,iy,lx,ly,lz]) 3#usize=ok ly := rfl
  have ii4 : Array.index_usize (Array.make 5#usize [ix,iy,lx,ly,lz]) 4#usize=ok lz := rfl
  simp only [SAQ_LineSource.line,ia0,ia1,ia2,ia3,ii2,ii3,ii4,
    cut.Hwe,cut.Hwe1,cut.Hwe2,cut.Hh0,cut.Hwe3,cut.Hwe4,cut.Hm,cut.Hh2,cut.Hwe5,cut.Hm1,cut.Hc0,cut.Hwe6,cut.Hm2,cut.Hc1,cut.Hwe7,cut.Hh1,cut.Hwe8,cut.Hm3,cut.Hh3,cut.Hwe9,cut.Hwe10,cut.Hwe11,cut.Hwe12,cut.Hwe13,cut.Hout,bind_tc_ok]

theorem same_execution {S Event : Type} (state : S)
    (alpha a b c d : E) (ix iy lx ly lz : U32)
    (hAlpha : CanonicalWide alpha) (ha : CanonicalWide a) (hb : CanonicalWide b)
    (hc : CanonicalWide c) (hd : CanonicalWide d) :
    ∃ out, ∃ cut : Cuts alpha a b c d lx ly lz out,
      NEI_LineDomains.Intermediates cut ∧
      NEG_FoldsTypes.line_fold_with_inverses alpha
        (Array.make 4#usize [a,b,c,d])
        (Array.make 5#usize [ix,iy,lx,ly,lz])=ok out ∧
      NEB_PureFrame.run (Event:=Event) state
        (NEG_FoldsTypes.line_fold_with_inverses alpha
          (Array.make 4#usize [a,b,c,d])
          (Array.make 5#usize [ix,iy,lx,ly,lz]))=ok (out,state,[]) ∧
      CanonicalWide out ∧ decodeWide out =
        R1ZCircleFoldMathV1.sourceLineFold (decodeWide alpha)
          (values4 (decodeWide a) (decodeWide b) (decodeWide c) (decodeWide d))
          (decodeBase lx) (decodeBase ly) (decodeBase lz) := by
  obtain ⟨out,run,canonical⟩ := JFn_LineTotal.source alpha a b c d ix iy lx ly lz
    hAlpha ha hb hc hd
  obtain ⟨cut⟩ := SAQ_LineSource.cuts alpha a b c d out ix iy lx ly lz run
  have emitted := reconstruct alpha a b c d out ix iy lx ly lz cut
  exact ⟨out,cut,NEI_LineDomains.same_site_domains alpha a b c d out lx ly lz
    cut hAlpha ha hb hc hd,emitted,NEB_PureFrame.successful state _ _ emitted,
    canonical,(SAQ_LineJoin.on_cuts alpha a b c d out lx ly lz cut).2⟩

#print axioms reconstruct
#print axioms same_execution
end NEI_LineCertificate
end
