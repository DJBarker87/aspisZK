import R1Z.ProverCommitOpeningModel53
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OpeningImages54
open Aeneas Aeneas.Std Result
open ProverCommitPrimitive47 ProverCommitSubfieldOps47 ProverCommitWideOps48
open ProverCommitValueRange47 (embed)
open ProverCommitSuccessorPoint49 (decoded)
open AspisR1.ExtractedCurrentQM31Exact (decode)

structure Data where
  c : Nat → Nat → Old.Q
  p : Nat → Old.Q
  x0 y0 x1 y1 : Old.Q
  g k a b : Raw
  ch : R0Z.HonestView.Challenges Exact

def Coefficients (d : Data) : Prop := ∀ l, l<29 → ∀ j, j<1024 → Canonical (d.c l j)
structure Sample (d : Data) : Prop where
  hp : ∀ i, i<10 → Canonical (d.p i)
  hx0 : Canonical d.x0
  hy0 : Canonical d.y0
  hx1 : Canonical d.x1
  hy1 : Canonical d.y1
  hg : canonical d.g
  hk : canonical d.k
  ha : canonical d.a
  hb : canonical d.b
  point : (fun i => embed (decoded d.p i))=R0Z.HonestView.alpha d.ch
  z0x : embed (decode d.x0)=(d.ch.circle 0).1.1
  z0y : embed (decode d.y0)=(d.ch.circle 0).1.2
  z1x : embed (decode d.x1)=(d.ch.circle 1).1.1
  z1y : embed (decode d.y1)=(d.ch.circle 1).1.2
  gamma : value d.g=d.ch.opening 0
  kappa : value d.k=d.ch.opening 1
  alpha0 : value d.a=d.ch.opening 2
  alpha1 : value d.b=d.ch.opening 3

def round0 (d : Data) := ProverCommitOpeningBytes49.modelStream 7
  (fun i => R0Z.HonestView.BatchedLayer.read (Bat:=Batched.R1Bat) AspisR1.rowEquiv d.ch
    (ProverCommitGammaCoefficients53.wideTrace d.c) (.round0 i))
def round1 (d : Data) := ProverCommitOpeningBytes49.modelStream 7
  (fun i => R0Z.HonestView.BatchedLayer.read (Bat:=Batched.R1Bat) AspisR1.rowEquiv d.ch
    (ProverCommitGammaCoefficients53.wideTrace d.c) (.round1 i))
def finalBytes (d : Data) := ProverCommitOpeningBytes49.modelStream 64
  (fun i => R0Z.HonestView.BatchedLayer.read (Bat:=Batched.R1Bat) AspisR1.rowEquiv d.ch
    (ProverCommitGammaCoefficients53.wideTrace d.c) (.final i))

def Images (d : Data) (hc : Coefficients d) : Prop :=
  ∃ (c0 q1 c1 fin : Nat → Raw) (hc0 : ∀ i, i<7 → canonical (c0 i))
    (hc1 : ∀ i, i<7 → canonical (c1 i)) (hcf : ∀ i, i<64 → canonical (fin i)),
    ProverCommitOpeningModel53.run d.c hc (ProverCommitQArray48.array 10#usize d.p)
      (ProverCommitNativeQ48.source d.x0) (ProverCommitNativeQ48.source d.y0)
      (ProverCommitNativeQ48.source d.x1) (ProverCommitNativeQ48.source d.y1)
      (source d.g) (source d.k) (source d.a) (source d.b)=
      ok (List.ofFn (fun i : Fin 7 => source (c0 i.val)),sourceArray 256#usize q1,
        List.ofFn (fun i : Fin 7 => source (c1 i.val)),sourceArray 64#usize fin) ∧
    ProverCommitOpeningBytes49.stream 7 c0 hc0=round0 d ∧
    ProverCommitOpeningBytes49.stream 7 c1 hc1=round1 d ∧
    ProverCommitOpeningBytes49.stream 64 fin hcf=finalBytes d

theorem complete (d : Data) (hc : Coefficients d) (s : Sample d) : Images d hc :=
  ProverCommitOpeningModel53.exact_images d.c hc d.p s.hp d.x0 d.y0 d.x1 d.y1
    s.hx0 s.hy0 s.hx1 s.hy1 d.g d.k d.a d.b s.hg s.hk s.ha s.hb d.ch
    s.point s.z0x s.z0y s.z1x s.z1y s.gamma s.kappa s.alpha0 s.alpha1
#print axioms Coefficients
#print axioms round0
#print axioms round1
#print axioms finalBytes
#print axioms Images
#print axioms complete
end R1Z.PV_RunJoin_OpeningImages54
