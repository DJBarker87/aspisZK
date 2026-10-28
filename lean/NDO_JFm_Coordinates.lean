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

def value00 : aspis_core.field.QM31 := ⟨⟨399501241#u32,284689285#u32⟩,⟨1852519329#u32,449773828#u32⟩⟩
def value01 : aspis_core.field.QM31 := ⟨⟨941725965#u32,710616451#u32⟩,⟨1814298802#u32,371706036#u32⟩⟩
def value02 : aspis_core.field.QM31 := ⟨⟨695778276#u32,681646639#u32⟩,⟨602326251#u32,1549567804#u32⟩⟩
def value03 : aspis_core.field.QM31 := ⟨⟨1476684925#u32,1863380722#u32⟩,⟨884825803#u32,833738140#u32⟩⟩
def value04 : aspis_core.field.QM31 := ⟨⟨1060986669#u32,633890405#u32⟩,⟨1909299272#u32,1189471034#u32⟩⟩
def value05 : aspis_core.field.QM31 := ⟨⟨1386874782#u32,910452727#u32⟩,⟨1915687885#u32,910141168#u32⟩⟩
def value06 : aspis_core.field.QM31 := ⟨⟨267896954#u32,635634473#u32⟩,⟨964486531#u32,55894934#u32⟩⟩
def value07 : aspis_core.field.QM31 := ⟨⟨232401293#u32,2112766299#u32⟩,⟨726128746#u32,1494283384#u32⟩⟩
def value08 : aspis_core.field.QM31 := ⟨⟨433552158#u32,532435962#u32⟩,⟨386199075#u32,662257941#u32⟩⟩
def value09 : aspis_core.field.QM31 := ⟨⟨638972043#u32,1545507045#u32⟩,⟨641752070#u32,1628235249#u32⟩⟩
def value10 : aspis_core.field.QM31 := ⟨⟨1898954622#u32,1275684462#u32⟩,⟨1553589096#u32,1176189881#u32⟩⟩
def value11 : aspis_core.field.QM31 := ⟨⟨2043002114#u32,1961778236#u32⟩,⟨1779778182#u32,778096594#u32⟩⟩
def value12 : aspis_core.field.QM31 := ⟨⟨1472540754#u32,162642227#u32⟩,⟨278504786#u32,689714075#u32⟩⟩
def value13 : aspis_core.field.QM31 := ⟨⟨614390089#u32,1065832687#u32⟩,⟨1348373272#u32,1851595171#u32⟩⟩
def value14 : aspis_core.field.QM31 := ⟨⟨1518895880#u32,1177859893#u32⟩,⟨464691262#u32,913595700#u32⟩⟩
def value15 : aspis_core.field.QM31 := ⟨⟨705343446#u32,1948609717#u32⟩,⟨871005084#u32,203308705#u32⟩⟩
def value16 : aspis_core.field.QM31 := ⟨⟨528783666#u32,1672539309#u32⟩,⟨1274387717#u32,552414171#u32⟩⟩
def value17 : aspis_core.field.QM31 := ⟨⟨1657509587#u32,287924440#u32⟩,⟨1819227394#u32,1192254731#u32⟩⟩
def value18 : aspis_core.field.QM31 := ⟨⟨1142413086#u32,2006134641#u32⟩,⟨1686703278#u32,2011383024#u32⟩⟩
def value19 : aspis_core.field.QM31 := ⟨⟨1106424694#u32,342809735#u32⟩,⟨1036886578#u32,305075687#u32⟩⟩
def value20 : aspis_core.field.QM31 := ⟨⟨810819047#u32,1156380883#u32⟩,⟨768810467#u32,1018558903#u32⟩⟩
def value21 : aspis_core.field.QM31 := ⟨⟨1410683225#u32,375596669#u32⟩,⟨973261870#u32,122086709#u32⟩⟩
def value22 : aspis_core.field.QM31 := ⟨⟨2023864416#u32,983081232#u32⟩,⟨187881185#u32,1338388013#u32⟩⟩
def value23 : aspis_core.field.QM31 := ⟨⟨454398981#u32,504493626#u32⟩,⟨2008082900#u32,1252680230#u32⟩⟩
def value24 : aspis_core.field.QM31 := ⟨⟨2030227143#u32,1410410828#u32⟩,⟨1902035786#u32,62756635#u32⟩⟩
#print axioms injective
end AspisR1.JFm_Coordinates
