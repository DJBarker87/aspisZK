import NDO_JHd_RequestWindow
import NDO_JFs_PaymentReads
import NDO_JFs_PaymentDigests
import NDO_JFs_PaymentHeader
set_option autoImplicit false
namespace AspisR1.JHd_RequestSegments
open Aeneas Aeneas.Std Result
open JHd_RequestWindow
theorem w0 : (window 104 8 (by decide)).val=JFu_PublicMeta07.bytes := by rfl
#print axioms w0
theorem w1 : (window 112 32 (by decide)).val=JFs_Cell04.bytes := by rfl
#print axioms w1
theorem w2 : (window 144 32 (by decide)).val=JFs_Cell05.bytes := by rfl
#print axioms w2
theorem w3 : (window 176 8 (by decide)).val=JFs_Cell06.bytes := by rfl
#print axioms w3
theorem w4 : (window 184 32 (by decide)).val=JFu_PublicDigest43.bytes := by rfl
#print axioms w4
theorem w5 : (window 216 32 (by decide)).val=JFu_PublicDigest44.bytes := by rfl
#print axioms w5
theorem w6 : (window 248 4 (by decide)).val=JFs_Cell07.bytes := by rfl
#print axioms w6
theorem w7 : (window 252 4 (by decide)).val=JFu_PublicMeta08.bytes := by rfl
#print axioms w7
theorem w8 : (window 256 32 (by decide)).val=JFu_PublicDigest45.bytes := by rfl
#print axioms w8
theorem w9 : (window 288 32 (by decide)).val=JFu_PublicDigest46.bytes := by rfl
#print axioms w9
theorem split (xs : List U8) (off : Nat) :
    (xs.drop off).take 216 =
    (xs.drop off).take 8 ++ (xs.drop (off+8)).take 32 ++
    (xs.drop (off+40)).take 32 ++ (xs.drop (off+72)).take 8 ++
    (xs.drop (off+80)).take 32 ++ (xs.drop (off+112)).take 32 ++
    (xs.drop (off+144)).take 4 ++ (xs.drop (off+148)).take 4 ++
    (xs.drop (off+152)).take 32 ++ (xs.drop (off+184)).take 32 := by
  have cut (ys : List U8) (a b : Nat) : ys.take (a+b)=ys.take a ++ (ys.drop a).take b :=
    List.take_add
  rw [show 216=184+32 from rfl,cut,show 184=152+32 from rfl,cut,
    show 152=148+4 from rfl,cut,show 148=144+4 from rfl,cut,
    show 144=112+32 from rfl,cut,show 112=80+32 from rfl,cut,
    show 80=72+8 from rfl,cut,show 72=40+32 from rfl,cut,
    show 40=8+32 from rfl,cut]
  simp only [List.drop_drop]
#print axioms split

attribute [local irreducible] JFx_NativeBytes.publicInput JHb_DataRequest.bytes

theorem payment : window 104 216 (by decide)=JFu_PublicRange.payment := by
  apply Subtype.ext
  dsimp only [window,JFu_PublicRange.payment,JFu_PublicRange.segment]
  rw [split,split]
  simp only [Nat.reduceAdd]
  have h0:=w0;have h1:=w1;have h2:=w2;have h3:=w3;have h4:=w4
  have h5:=w5;have h6:=w6;have h7:=w7;have h8:=w8;have h9:=w9
  dsimp only [window] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  rw [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,
    JFu_PublicMeta07.selected,JFs_Cell04.selected,JFs_Cell05.selected,JFs_Cell06.selected,
    JFu_PublicDigest43.selected,JFu_PublicDigest44.selected,JFs_Cell07.selected,
    JFu_PublicMeta08.selected,JFu_PublicDigest45.selected,JFu_PublicDigest46.selected]
#print axioms payment
end AspisR1.JHd_RequestSegments
