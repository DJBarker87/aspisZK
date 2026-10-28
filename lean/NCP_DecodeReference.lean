import NCP_DecodeCase0
import NCP_DecodeCase1
import NCP_DecodeCase2
import NCP_DecodeCase3
import NCP_DecodeCase4
import NCP_DecodeCase5
import NCP_DecodeCase6
import NCP_DecodeCase7
import NCP_DecodeCase8
import NCP_ModelDischarge
set_option autoImplicit false
noncomputable section
namespace NCP_DecodeReference
open Aeneas Aeneas.Std Result NBP_DecodeWord

theorem reference_model (b : Array U8 32#usize) :
    reference b = ok (NBP_DigestDecode.decoded b) := by
  by_cases h0 : word b 0 >= P
  · simpa [NBP_DigestDecode.decoded,h0] using NCP_DecodeCase0.result b  h0
  ·
    by_cases h1 : word b 1 >= P
    · simpa [NBP_DigestDecode.decoded,h0,h1] using NCP_DecodeCase1.result b (lt_of_not_ge h0) h1
    ·
      by_cases h2 : word b 2 >= P
      · simpa [NBP_DigestDecode.decoded,h0,h1,h2] using NCP_DecodeCase2.result b (lt_of_not_ge h0) (lt_of_not_ge h1) h2
      ·
        by_cases h3 : word b 3 >= P
        · simpa [NBP_DigestDecode.decoded,h0,h1,h2,h3] using NCP_DecodeCase3.result b (lt_of_not_ge h0) (lt_of_not_ge h1) (lt_of_not_ge h2) h3
        ·
          by_cases h4 : word b 4 >= P
          · simpa [NBP_DigestDecode.decoded,h0,h1,h2,h3,h4] using NCP_DecodeCase4.result b (lt_of_not_ge h0) (lt_of_not_ge h1) (lt_of_not_ge h2) (lt_of_not_ge h3) h4
          ·
            by_cases h5 : word b 5 >= P
            · simpa [NBP_DigestDecode.decoded,h0,h1,h2,h3,h4,h5] using NCP_DecodeCase5.result b (lt_of_not_ge h0) (lt_of_not_ge h1) (lt_of_not_ge h2) (lt_of_not_ge h3) (lt_of_not_ge h4) h5
            ·
              by_cases h6 : word b 6 >= P
              · simpa [NBP_DigestDecode.decoded,h0,h1,h2,h3,h4,h5,h6] using NCP_DecodeCase6.result b (lt_of_not_ge h0) (lt_of_not_ge h1) (lt_of_not_ge h2) (lt_of_not_ge h3) (lt_of_not_ge h4) (lt_of_not_ge h5) h6
              ·
                by_cases h7 : word b 7 >= P
                · simpa [NBP_DigestDecode.decoded,h0,h1,h2,h3,h4,h5,h6,h7] using NCP_DecodeCase7.result b (lt_of_not_ge h0) (lt_of_not_ge h1) (lt_of_not_ge h2) (lt_of_not_ge h3) (lt_of_not_ge h4) (lt_of_not_ge h5) (lt_of_not_ge h6) h7
                ·
                  simpa [NBP_DigestDecode.decoded,h0,h1,h2,h3,h4,h5,h6,h7] using NCP_DecodeCase8.result b (lt_of_not_ge h0) (lt_of_not_ge h1) (lt_of_not_ge h2) (lt_of_not_ge h3) (lt_of_not_ge h4) (lt_of_not_ge h5) (lt_of_not_ge h6) (lt_of_not_ge h7)

theorem reference_source : NBN_AfterDecodeTypes.NBN_Dep_DigestDecode reference := by
  intro b
  rw [reference_model]
  exact (NBP_DigestDecode.result b).symm

#print axioms reference_model
#print axioms reference_source
end NCP_DecodeReference
