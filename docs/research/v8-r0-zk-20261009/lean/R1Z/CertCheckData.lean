import R1Z.CertCheckTop
import R1Z.CertData

/-! D49.4 C3: the extracted checker's success as `DataOK` on its flat data.

`toData pb c` reads the Aeneas `Pub`/`Cert` vectors as functions (`gs` values,
`gi` indices); `check_data` : `check pb c = ok true → DataOK (toData pb c)`.
This is the only module that sees both the Aeneas types and `CertData`; the
composition with `p_r1_of_checks` (`CertCheckSound`) depends on `CertData` only. -/

set_option autoImplicit false

namespace R1Z.CertCheck
open Aeneas Aeneas.Std Result R1CertCheck R1Z.CertData

/-- The flat data of an extracted `Pub`/`Cert` pair. -/
def toData (pb : Pub) (c : Cert) : CData where
  rw := pb.rw.val
  bw := pb.bw.val
  nq := pb.nq.val
  m := c.m.val
  mg := c.mg.val
  r := c.r.val
  k := c.k.val
  q := pb.q.val
  nl := pb.nl.val
  os := pb.os.val
  gw := pb.gw.val
  N := (sl pb.lane).val.length
  NG := (sl pb.glane).val.length
  lstLen := (sl c.lst).val.length
  tagLen := (sl c.tag).val.length
  a9 := gs (sl pb.a9)
  hinv := gs (sl c.hinv)
  lane := gi (sl pb.lane)
  wl := gi (sl pb.wl)
  own := gs (sl pb.own)
  round := gs (sl pb.round)
  tq := gs (sl pb.tq)
  ej := gi (sl c.ej)
  es := gi (sl c.es)
  epo := gi (sl c.epo)
  eco := gi (sl c.eco)
  pidx := gi (sl c.pidx)
  coef := gs (sl c.coef)
  rho := gs (sl c.rho)
  y := gs (sl c.y)
  rel := gs (sl pb.rel)
  u := gs (sl c.u)
  e := gs (sl c.e)
  lst := gi (sl c.lst)
  tag := gi (sl c.tag)
  glane := gi (sl pb.glane)
  gwl := gi (sl pb.gwl)
  gown := gs (sl pb.gown)
  ground := gs (sl pb.ground)
  gbat := gs (sl pb.gbat)
  gej := gi (sl c.gej)
  ges := gi (sl c.ges)
  gepo := gi (sl c.gepo)
  geco := gi (sl c.geco)
  gpidx := gi (sl c.gpidx)
  gcoef := gs (sl c.gcoef)
  beta := gs (sl c.beta)
  yg := gs (sl c.yg)
  nm := gs (sl c.nm)
  lw := gi (sl pb.lw)
  loff := gi (sl pb.loff)
  lo := gs (sl pb.lo)
  lu := gs (sl c.lu)
  lid := gs (sl c.lid)

theorem entOK_F {ej es epo eco idx coef lane wl z1 z2 g out : Slice U32} {s1 s2 n2 sg ng e : ℕ}
    (h : EntOK ej es epo eco idx coef lane wl z1 s1 z2 s2 n2 g sg ng out zeroS e) :
    EntOKF (gi ej) (gi es) (gi epo) (gi eco) (gi idx) (gs coef) (gi lane) (gi wl) lane.val.length
      (gs z1) s1 (gs z2) s2 n2 (gs g) sg ng (gs out) e := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, fun i hi => (h3 i hi).trans zeroS_gs, fun i hi => (h4 i hi).trans zeroS_gs, h5⟩

/-- **`check pb c = ok true` gives `DataOK (toData pb c)`.** -/
theorem check_data {pb : Pub} {c : Cert} (h : check pb c = ok true) : DataOK (toData pb c) := by
  obtain ⟨hH, hq, hL, ⟨hE, hP⟩, ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩⟩ := check_spec h
  exact ⟨hH, hq, hL, ⟨fun e he => entOK_F (hE e he), hP⟩,
    ⟨b1, b2, b3, b4, b5, b6, b7, fun e he => entOK_F (b8 e he), b9, b10⟩⟩

#print axioms entOK_F
#print axioms check_data

end R1Z.CertCheck
