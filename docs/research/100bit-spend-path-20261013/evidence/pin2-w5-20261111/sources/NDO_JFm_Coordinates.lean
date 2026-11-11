import RPz7_ExtractedDigest32SamplerTransport
set_option autoImplicit false
namespace AspisR1.JFm_Coordinates
open Aeneas Aeneas.Std AspisR1PublicPreparation

def coordinates (q : aspis_core.field.QM31) : List Nat :=
  ExtractedQM31SamplerCorrect.coordinates (SamplerTransport.toOld q)

theorem injective : Function.Injective coordinates := by
  intro x y h
  cases x with
  | mk x0 x1 =>
    cases x0 with
    | mk a b =>
      cases x1 with
      | mk c d =>
        cases y with
        | mk y0 y1 =>
          cases y0 with
          | mk e f =>
            cases y1 with
            | mk g k =>
              change [a.val,b.val,c.val,d.val]=[e.val,f.val,g.val,k.val] at h
              simp only [List.cons.injEq,and_true] at h
              obtain ⟨ha,hb,hc,hd⟩ := h
              have h0 := UScalar.eq_of_val_eq ha
              have h1 := UScalar.eq_of_val_eq hb
              have h2 := UScalar.eq_of_val_eq hc
              have h3 := UScalar.eq_of_val_eq hd
              cases h0;cases h1;cases h2;cases h3
              rfl

def value00 : aspis_core.field.QM31 := ⟨⟨1526197484#u32,972223295#u32⟩,⟨1344894819#u32,1842842573#u32⟩⟩
def value01 : aspis_core.field.QM31 := ⟨⟨713036309#u32,46106111#u32⟩,⟨1431766303#u32,661598978#u32⟩⟩
def value02 : aspis_core.field.QM31 := ⟨⟨1499295713#u32,2070051249#u32⟩,⟨627130303#u32,1539438952#u32⟩⟩
def value03 : aspis_core.field.QM31 := ⟨⟨288528412#u32,2035777531#u32⟩,⟨158764610#u32,1232573205#u32⟩⟩
def value04 : aspis_core.field.QM31 := ⟨⟨1046294508#u32,1448892072#u32⟩,⟨1102861377#u32,204937514#u32⟩⟩
def value05 : aspis_core.field.QM31 := ⟨⟨1655381728#u32,1014758532#u32⟩,⟨998812813#u32,878722461#u32⟩⟩
def value06 : aspis_core.field.QM31 := ⟨⟨1645800952#u32,549188968#u32⟩,⟨1826604674#u32,1137282727#u32⟩⟩
def value07 : aspis_core.field.QM31 := ⟨⟨157361889#u32,1247702199#u32⟩,⟨800788836#u32,661970985#u32⟩⟩
def value08 : aspis_core.field.QM31 := ⟨⟨921303514#u32,147937276#u32⟩,⟨985891919#u32,1544264165#u32⟩⟩
def value09 : aspis_core.field.QM31 := ⟨⟨2059264910#u32,1957417717#u32⟩,⟨179235502#u32,178141392#u32⟩⟩
def value10 : aspis_core.field.QM31 := ⟨⟨1698716691#u32,1654608267#u32⟩,⟨1457767269#u32,858578321#u32⟩⟩
def value11 : aspis_core.field.QM31 := ⟨⟨1414149343#u32,1981583981#u32⟩,⟨1443632258#u32,1090729933#u32⟩⟩
def value12 : aspis_core.field.QM31 := ⟨⟨1652904113#u32,1201873115#u32⟩,⟨103187561#u32,1392689894#u32⟩⟩
def value13 : aspis_core.field.QM31 := ⟨⟨1379543090#u32,1345077044#u32⟩,⟨707204589#u32,1308473596#u32⟩⟩
def value14 : aspis_core.field.QM31 := ⟨⟨1791020237#u32,1433715521#u32⟩,⟨1642392171#u32,850501075#u32⟩⟩
def value15 : aspis_core.field.QM31 := ⟨⟨481946492#u32,959095368#u32⟩,⟨2134045306#u32,1739942601#u32⟩⟩
def value16 : aspis_core.field.QM31 := ⟨⟨1938229017#u32,474903281#u32⟩,⟨2119643323#u32,1456121415#u32⟩⟩
def value17 : aspis_core.field.QM31 := ⟨⟨1817229702#u32,1607494202#u32⟩,⟨2141385593#u32,540773558#u32⟩⟩
def value18 : aspis_core.field.QM31 := ⟨⟨1777472067#u32,823612886#u32⟩,⟨769288371#u32,68548007#u32⟩⟩
def value19 : aspis_core.field.QM31 := ⟨⟨763754670#u32,31463458#u32⟩,⟨1727849165#u32,1028580563#u32⟩⟩
def value20 : aspis_core.field.QM31 := ⟨⟨1976533199#u32,2142788478#u32⟩,⟨1835806328#u32,1950703221#u32⟩⟩
def value21 : aspis_core.field.QM31 := ⟨⟨270702945#u32,1582130923#u32⟩,⟨1873897156#u32,1411904894#u32⟩⟩
def value22 : aspis_core.field.QM31 := ⟨⟨562817633#u32,1940768295#u32⟩,⟨892660560#u32,287439637#u32⟩⟩
def value23 : aspis_core.field.QM31 := ⟨⟨124721160#u32,1463026064#u32⟩,⟨316880895#u32,1559203092#u32⟩⟩
def value24 : aspis_core.field.QM31 := ⟨⟨1088201115#u32,1292966428#u32⟩,⟨495022806#u32,1713251341#u32⟩⟩
#print axioms injective
end AspisR1.JFm_Coordinates
