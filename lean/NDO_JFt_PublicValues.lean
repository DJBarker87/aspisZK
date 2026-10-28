import NDO_JFt_Digest00
import NDO_JFt_Digest01
import NDO_JFt_Digest02
import NDO_JFt_Digest03
import NDO_JFt_Digest04
import NDO_JFt_Digest05
import NDO_JFt_Digest06
import NDO_JFt_Digest07
import NDO_JFt_Digest08
import NDO_JFt_Digest09
import NDO_JFt_Digest10
import NDO_JFt_Digest11
import NDO_JFt_Digest12
import NDO_JFt_Digest13
import NDO_JFt_Digest14
import NDO_JFt_Digest15
import NDO_JFt_Digest16
import NDO_JFt_Digest17
import NDO_JFt_Digest18
import NDO_JFt_Digest19
import NDO_JFt_Digest20
import NDO_JFt_Digest21
import NDO_JFt_Digest22
import NDO_JFt_Digest23
import NDO_JFt_Digest24
import NDO_JFt_Digest25
import NDO_JFt_Digest26
import NDO_JFt_Digest27
import NDO_JFt_Digest28
import NDO_JFt_Digest29
import NDO_JFt_Digest30
import NDO_JFt_Digest31
import NDO_JFt_Digest32
import NDO_JFt_Digest33
import NDO_JFt_Digest34
import NDO_JFt_Digest35
import NDO_JFt_Digest36
import NDO_JFt_Digest37
import NDO_JFt_Digest38
import NDO_JFt_Digest39
import NDO_JFt_Digest40
import NDO_JFt_Digest41
import NDO_JFt_Digest42
import NDO_JFt_Digest43
import NDO_JFt_Digest44
import NDO_JFt_Digest45
import NDO_JFt_Digest46
set_option autoImplicit false
namespace AspisR1.JFt_PublicValues
open Aeneas Aeneas.Std Result

structure Cell where
  offset : Nat
  bound : offset+32≤1880
  value : Array U32 8#usize

def cells : List Cell := [
  ⟨112,by decide,JFt_Digest00.value⟩,
  ⟨304,by decide,JFt_Digest01.value⟩,
  ⟨336,by decide,JFt_Digest02.value⟩,
  ⟨368,by decide,JFt_Digest03.value⟩,
  ⟨400,by decide,JFt_Digest04.value⟩,
  ⟨432,by decide,JFt_Digest05.value⟩,
  ⟨464,by decide,JFt_Digest06.value⟩,
  ⟨496,by decide,JFt_Digest07.value⟩,
  ⟨528,by decide,JFt_Digest08.value⟩,
  ⟨560,by decide,JFt_Digest09.value⟩,
  ⟨592,by decide,JFt_Digest10.value⟩,
  ⟨624,by decide,JFt_Digest11.value⟩,
  ⟨656,by decide,JFt_Digest12.value⟩,
  ⟨688,by decide,JFt_Digest13.value⟩,
  ⟨720,by decide,JFt_Digest14.value⟩,
  ⟨752,by decide,JFt_Digest15.value⟩,
  ⟨784,by decide,JFt_Digest16.value⟩,
  ⟨816,by decide,JFt_Digest17.value⟩,
  ⟨848,by decide,JFt_Digest18.value⟩,
  ⟨880,by decide,JFt_Digest19.value⟩,
  ⟨912,by decide,JFt_Digest20.value⟩,
  ⟨944,by decide,JFt_Digest21.value⟩,
  ⟨992,by decide,JFt_Digest22.value⟩,
  ⟨1024,by decide,JFt_Digest23.value⟩,
  ⟨1056,by decide,JFt_Digest24.value⟩,
  ⟨1088,by decide,JFt_Digest25.value⟩,
  ⟨1120,by decide,JFt_Digest26.value⟩,
  ⟨1152,by decide,JFt_Digest27.value⟩,
  ⟨1184,by decide,JFt_Digest28.value⟩,
  ⟨1216,by decide,JFt_Digest29.value⟩,
  ⟨1248,by decide,JFt_Digest30.value⟩,
  ⟨1280,by decide,JFt_Digest31.value⟩,
  ⟨1312,by decide,JFt_Digest32.value⟩,
  ⟨1344,by decide,JFt_Digest33.value⟩,
  ⟨1376,by decide,JFt_Digest34.value⟩,
  ⟨1408,by decide,JFt_Digest35.value⟩,
  ⟨1440,by decide,JFt_Digest36.value⟩,
  ⟨1472,by decide,JFt_Digest37.value⟩,
  ⟨1504,by decide,JFt_Digest38.value⟩,
  ⟨1536,by decide,JFt_Digest39.value⟩,
  ⟨1568,by decide,JFt_Digest40.value⟩,
  ⟨1600,by decide,JFt_Digest41.value⟩,
  ⟨1632,by decide,JFt_Digest42.value⟩,
  ⟨1744,by decide,JFt_Digest43.value⟩,
  ⟨1776,by decide,JFt_Digest44.value⟩,
  ⟨1816,by decide,JFt_Digest45.value⟩,
  ⟨1848,by decide,JFt_Digest46.value⟩]

/-- All47 exact returned digest values on the SAME retained public1880. -/
theorem source : ∀ c ∈ cells,AspisS6NativeSnapshotReadDigest.read_digest
    (JFu_PublicRange.segment c.offset 32 c.bound)=ok (.Ok c.value) := by
  intro c member
  simp only [cells,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41 | h42 | h43 | h44 | h45 | h46
  · subst c;exact JFt_Digest00.source
  · subst c;exact JFt_Digest01.source
  · subst c;exact JFt_Digest02.source
  · subst c;exact JFt_Digest03.source
  · subst c;exact JFt_Digest04.source
  · subst c;exact JFt_Digest05.source
  · subst c;exact JFt_Digest06.source
  · subst c;exact JFt_Digest07.source
  · subst c;exact JFt_Digest08.source
  · subst c;exact JFt_Digest09.source
  · subst c;exact JFt_Digest10.source
  · subst c;exact JFt_Digest11.source
  · subst c;exact JFt_Digest12.source
  · subst c;exact JFt_Digest13.source
  · subst c;exact JFt_Digest14.source
  · subst c;exact JFt_Digest15.source
  · subst c;exact JFt_Digest16.source
  · subst c;exact JFt_Digest17.source
  · subst c;exact JFt_Digest18.source
  · subst c;exact JFt_Digest19.source
  · subst c;exact JFt_Digest20.source
  · subst c;exact JFt_Digest21.source
  · subst c;exact JFt_Digest22.source
  · subst c;exact JFt_Digest23.source
  · subst c;exact JFt_Digest24.source
  · subst c;exact JFt_Digest25.source
  · subst c;exact JFt_Digest26.source
  · subst c;exact JFt_Digest27.source
  · subst c;exact JFt_Digest28.source
  · subst c;exact JFt_Digest29.source
  · subst c;exact JFt_Digest30.source
  · subst c;exact JFt_Digest31.source
  · subst c;exact JFt_Digest32.source
  · subst c;exact JFt_Digest33.source
  · subst c;exact JFt_Digest34.source
  · subst c;exact JFt_Digest35.source
  · subst c;exact JFt_Digest36.source
  · subst c;exact JFt_Digest37.source
  · subst c;exact JFt_Digest38.source
  · subst c;exact JFt_Digest39.source
  · subst c;exact JFt_Digest40.source
  · subst c;exact JFt_Digest41.source
  · subst c;exact JFt_Digest42.source
  · subst c;exact JFt_Digest43.source
  · subst c;exact JFt_Digest44.source
  · subst c;exact JFt_Digest45.source
  · subst c;exact JFt_Digest46.source

#print axioms source
end AspisR1.JFt_PublicValues
