import NDO_JGc_TX2_ByteAppend
import NDO_JGc_TX2_HashBytes
import NDO_JGe_View
import NDO_JGh_TX2_M1Root
import NDO_JHe_SHARealization
import OracleDecisionMultiBuild
section
variable [sha : AspisR1.JHe_SHARealization]
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_C_Gr_M1Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def indices : List Nat := [93499,147529,216823,245899,209371,192317,65593,183859,193093,159813]
def bases (height : Nat) : List Nat := match height with
  | 0 => [65592,93498,147528,159812,183858,192316,193092,209370,216822,245898]
  | 1 => [65594,93496,147530,159814,183856,192318,193094,209368,216820,245896]
  | 2 => [65596,93500,147532,159808,183860,192312,193088,209372,216816,245900]
  | 3 => [65584,93488,147520,159816,183864,192304,193096,209360,216824,245888]
  | 4 => [65568,93472,147536,159824,183840,192288,193104,209344,216800,245904]
  | 5 => [65536,93440,147552,159840,183808,192256,193120,209376,216768,245920]
  | 6 => [65600,93504,147456,159744,183872,192320,193024,209280,216704,245952]
  | 7 => [65664,93568,147584,159872,183936,192384,193152,209152,216576,245760]
  | 8 => [65792,93184,147712,160000,184064,192000,193280,208896,216832,246016]
  | 9 => [66048,93696,147968,160256,183296,191488,192512,209408,216064,246272]
  | 10 => [66560,92160,148480,160768,182272,190464,193536,209920,215040,246784]
  | 11 => [67584,90112,149504,161792,180224,188416,194560,210944,212992,247808]
  | 12 => [69632,94208,151552,155648,184320,204800,217088,249856]
  | 13 => [73728,81920,196608,221184,253952]
  | 14 => [131072,163840,229376]
  | 15 => [98304]
  | 16 => [0]
  | 17 => []
  | _ => []
def siblingAt (height base : Nat) : State := match height with
  | 0 => match base with
    | 65592 => JGc_TX2_HashBytes.state [84,158,189,163,7,211,150,118,46,159,127,12,244,157,167,96,164,240,68,44,151,232,222,236,240,147,88,216,134,56,255,201]
    | 93498 => JGc_TX2_HashBytes.state [87,201,97,142,46,240,30,62,247,57,210,209,11,218,107,245,200,85,9,191,193,152,235,191,239,43,233,153,92,147,12,22]
    | 147528 => JGc_TX2_HashBytes.state [126,244,47,162,206,176,63,208,66,80,97,27,124,150,156,29,16,125,4,24,229,40,80,226,50,22,217,21,9,118,223,64]
    | 159812 => JGc_TX2_HashBytes.state [105,207,46,68,125,195,225,145,182,7,102,115,151,53,228,97,66,255,193,10,177,180,57,243,141,165,117,4,62,94,100,227]
    | 183858 => JGc_TX2_HashBytes.state [178,45,27,133,141,100,37,222,96,165,67,100,140,205,14,251,78,74,113,201,225,78,242,12,210,165,12,143,151,125,240,161]
    | 192316 => JGc_TX2_HashBytes.state [208,201,87,103,45,128,36,40,65,168,170,172,133,87,105,49,90,3,53,79,63,150,156,172,52,208,232,217,131,11,191,68]
    | 193092 => JGc_TX2_HashBytes.state [58,250,234,236,124,53,147,155,154,165,220,179,164,49,96,165,20,23,164,50,251,216,34,12,121,250,222,56,113,154,22,180]
    | 209370 => JGc_TX2_HashBytes.state [229,11,75,185,166,129,153,153,211,153,179,106,3,80,171,146,89,184,131,52,57,244,191,194,9,142,23,33,62,19,35,156]
    | 216822 => JGc_TX2_HashBytes.state [232,135,117,237,45,118,87,95,67,116,77,226,109,208,88,160,202,241,38,170,96,84,230,88,96,117,190,107,137,190,145,40]
    | 245898 => JGc_TX2_HashBytes.state [198,199,120,82,46,88,27,188,251,85,66,197,217,209,68,171,23,178,127,119,231,149,16,43,202,127,140,173,252,101,60,6]
    | _ => JGc_TX2_HashBytes.state []
  | 1 => match base with
    | 65594 => JGc_TX2_HashBytes.state [226,19,230,186,28,97,100,40,122,60,48,235,166,167,156,189,127,126,176,209,146,207,129,60,75,115,18,146,199,245,51,199]
    | 93496 => JGc_TX2_HashBytes.state [53,199,117,75,221,203,227,135,140,20,26,44,148,40,245,6,247,144,199,69,152,25,40,59,8,112,100,10,148,1,240,224]
    | 147530 => JGc_TX2_HashBytes.state [192,50,200,213,36,199,105,201,154,83,49,107,171,199,140,138,138,25,255,180,249,204,200,221,50,43,166,214,67,36,110,16]
    | 159814 => JGc_TX2_HashBytes.state [102,110,213,2,148,96,173,189,56,93,84,101,64,44,166,50,155,9,114,234,56,56,211,60,155,126,100,123,86,255,245,207]
    | 183856 => JGc_TX2_HashBytes.state [207,254,248,226,47,19,54,49,165,112,36,160,160,101,28,252,240,13,181,65,153,32,3,78,22,59,184,81,253,195,95,153]
    | 192318 => JGc_TX2_HashBytes.state [118,182,6,74,103,244,136,114,84,255,217,64,189,71,61,128,226,133,217,73,78,68,236,158,199,227,240,136,1,108,57,83]
    | 193094 => JGc_TX2_HashBytes.state [198,145,218,11,27,71,231,58,41,252,108,230,167,179,48,30,19,243,203,144,105,210,9,80,77,183,232,151,137,4,170,15]
    | 209368 => JGc_TX2_HashBytes.state [104,141,228,117,121,171,3,4,176,4,107,28,254,224,219,29,112,25,96,120,70,213,98,52,25,175,170,185,190,225,223,156]
    | 216820 => JGc_TX2_HashBytes.state [86,28,233,120,193,72,153,62,145,245,239,192,86,31,200,86,29,20,129,186,93,27,187,6,64,75,180,174,8,117,228,16]
    | 245896 => JGc_TX2_HashBytes.state [46,114,18,158,240,245,37,120,114,167,15,134,67,123,175,250,230,84,253,40,11,47,196,152,226,249,239,35,86,182,35,30]
    | _ => JGc_TX2_HashBytes.state []
  | 2 => match base with
    | 65596 => JGc_TX2_HashBytes.state [161,76,3,159,191,249,90,238,12,33,36,222,12,85,198,154,218,16,194,33,132,91,57,18,102,89,24,129,206,192,84,2]
    | 93500 => JGc_TX2_HashBytes.state [150,245,179,73,238,203,63,9,99,117,193,114,224,59,215,81,139,40,94,196,154,161,204,163,131,194,211,158,164,68,7,147]
    | 147532 => JGc_TX2_HashBytes.state [97,255,106,209,39,206,184,200,255,182,229,243,150,159,37,202,105,5,207,52,192,189,18,106,9,249,42,77,128,132,228,204]
    | 159808 => JGc_TX2_HashBytes.state [198,117,40,249,115,8,80,114,136,28,25,209,63,143,53,34,247,134,30,13,179,145,39,114,51,86,73,45,212,147,188,0]
    | 183860 => JGc_TX2_HashBytes.state [173,160,200,2,87,10,143,76,228,213,202,85,241,88,184,137,184,213,12,133,110,196,125,206,65,42,21,23,14,224,135,18]
    | 192312 => JGc_TX2_HashBytes.state [16,128,131,147,46,155,13,197,29,34,144,51,143,28,229,54,178,32,183,183,140,105,113,160,115,195,214,144,94,12,128,80]
    | 193088 => JGc_TX2_HashBytes.state [140,101,31,60,165,201,60,75,58,216,73,119,83,95,32,127,113,252,104,199,28,200,24,47,1,108,50,255,0,221,161,140]
    | 209372 => JGc_TX2_HashBytes.state [43,150,240,241,176,44,116,229,80,221,23,5,12,189,27,226,164,73,153,251,188,47,181,148,5,149,67,154,125,10,233,211]
    | 216816 => JGc_TX2_HashBytes.state [43,146,168,238,162,23,68,80,31,163,96,208,148,23,64,85,154,125,92,177,215,158,253,133,121,24,22,161,219,238,202,61]
    | 245900 => JGc_TX2_HashBytes.state [254,103,22,216,177,229,178,69,230,133,92,137,126,145,115,176,102,124,84,213,140,225,194,132,77,135,97,138,229,59,250,215]
    | _ => JGc_TX2_HashBytes.state []
  | 3 => match base with
    | 65584 => JGc_TX2_HashBytes.state [174,82,153,70,104,229,145,166,155,82,31,251,14,90,80,67,114,199,139,42,46,185,55,221,237,7,39,6,110,203,14,252]
    | 93488 => JGc_TX2_HashBytes.state [23,32,94,98,180,20,186,60,5,79,157,234,247,20,120,80,164,35,4,186,25,63,57,161,43,202,149,143,82,86,154,0]
    | 147520 => JGc_TX2_HashBytes.state [97,191,57,149,64,167,60,139,155,101,25,14,192,173,197,217,46,87,102,56,173,54,159,44,53,128,93,203,89,224,12,166]
    | 159816 => JGc_TX2_HashBytes.state [122,249,177,125,116,181,20,239,10,177,124,212,75,148,64,213,224,76,236,136,246,44,160,184,106,201,206,170,6,68,14,182]
    | 183864 => JGc_TX2_HashBytes.state [151,184,78,84,65,195,103,88,59,72,98,75,137,155,138,234,245,102,144,251,199,25,120,222,103,12,202,216,89,102,142,47]
    | 192304 => JGc_TX2_HashBytes.state [63,240,224,145,205,168,7,153,218,214,129,218,29,224,241,228,12,94,116,107,157,77,53,249,244,131,19,213,15,234,161,215]
    | 193096 => JGc_TX2_HashBytes.state [110,105,159,26,42,122,142,230,234,101,199,61,78,103,131,23,40,10,245,45,225,245,34,241,143,52,113,160,22,153,128,20]
    | 209360 => JGc_TX2_HashBytes.state [141,242,62,237,199,13,154,83,181,79,134,159,130,129,160,88,62,217,221,214,111,246,205,241,230,116,152,15,205,136,237,159]
    | 216824 => JGc_TX2_HashBytes.state [21,213,50,124,193,142,144,15,46,81,226,121,245,18,87,145,167,20,102,64,173,9,142,30,0,196,36,27,63,68,81,237]
    | 245888 => JGc_TX2_HashBytes.state [138,187,147,94,199,192,2,178,20,97,98,68,215,153,0,75,115,196,220,228,200,152,250,238,63,205,135,43,65,81,103,172]
    | _ => JGc_TX2_HashBytes.state []
  | 4 => match base with
    | 65568 => JGc_TX2_HashBytes.state [213,92,133,128,25,248,250,140,193,139,150,68,77,135,147,35,142,166,119,192,218,182,91,94,228,19,198,108,127,203,242,119]
    | 93472 => JGc_TX2_HashBytes.state [81,239,149,218,159,11,224,172,201,3,32,69,184,120,186,14,167,232,10,19,198,22,40,223,87,252,148,18,167,205,157,165]
    | 147536 => JGc_TX2_HashBytes.state [218,67,160,176,255,242,51,54,19,70,46,31,66,58,26,18,255,181,5,147,67,43,32,75,58,146,61,9,200,176,17,181]
    | 159824 => JGc_TX2_HashBytes.state [9,203,140,76,138,254,212,190,225,220,48,2,142,250,78,110,12,43,32,145,129,4,58,215,255,244,201,225,98,43,227,177]
    | 183840 => JGc_TX2_HashBytes.state [248,181,250,118,85,250,26,83,114,52,136,167,60,144,132,111,120,93,125,209,49,84,32,66,30,109,91,89,231,36,237,196]
    | 192288 => JGc_TX2_HashBytes.state [108,16,198,203,67,17,242,189,102,34,209,177,45,76,232,181,18,166,239,4,35,21,239,246,220,237,115,171,194,70,204,157]
    | 193104 => JGc_TX2_HashBytes.state [197,43,157,201,30,225,68,160,229,190,201,182,162,53,115,97,51,234,182,243,73,166,223,190,116,177,25,188,182,144,219,200]
    | 209344 => JGc_TX2_HashBytes.state [48,186,118,148,69,61,104,226,93,243,172,141,168,144,124,254,57,139,1,55,108,253,152,33,72,126,89,125,30,154,10,32]
    | 216800 => JGc_TX2_HashBytes.state [90,249,230,45,98,111,180,129,153,122,162,170,204,61,76,254,140,54,104,181,250,67,86,138,44,28,90,64,159,9,181,47]
    | 245904 => JGc_TX2_HashBytes.state [195,3,176,84,58,232,36,247,102,253,61,165,20,60,158,89,150,160,29,234,75,87,244,134,24,74,65,119,252,101,75,15]
    | _ => JGc_TX2_HashBytes.state []
  | 5 => match base with
    | 65536 => JGc_TX2_HashBytes.state [184,43,54,143,158,199,175,42,61,237,16,117,244,181,159,43,88,80,126,207,12,253,148,152,128,201,187,77,167,76,234,131]
    | 93440 => JGc_TX2_HashBytes.state [9,59,145,89,120,54,222,74,203,219,27,53,98,237,178,181,58,227,170,3,52,21,253,207,237,232,171,52,49,52,153,1]
    | 147552 => JGc_TX2_HashBytes.state [200,112,24,187,168,226,133,51,134,133,85,253,45,154,56,190,126,26,87,40,238,99,195,189,69,70,211,132,89,221,161,18]
    | 159840 => JGc_TX2_HashBytes.state [254,17,1,69,169,101,14,124,152,58,198,80,91,197,7,201,23,89,197,83,121,49,187,33,254,195,218,154,226,70,10,132]
    | 183808 => JGc_TX2_HashBytes.state [192,195,33,171,153,176,59,52,97,96,104,8,183,204,159,49,248,227,95,225,72,109,83,158,159,13,184,26,137,190,18,0]
    | 192256 => JGc_TX2_HashBytes.state [254,206,208,23,213,50,19,160,84,122,149,199,15,73,40,119,253,111,116,175,203,205,102,52,143,81,145,192,139,46,139,68]
    | 193120 => JGc_TX2_HashBytes.state [135,62,37,121,200,109,211,136,88,24,191,195,231,222,98,12,91,201,86,188,190,61,185,78,66,155,223,88,157,220,23,249]
    | 209376 => JGc_TX2_HashBytes.state [195,20,209,28,33,12,185,7,114,250,208,29,236,188,0,141,106,128,113,110,159,175,180,255,243,33,223,145,197,31,0,147]
    | 216768 => JGc_TX2_HashBytes.state [98,166,20,210,130,207,194,139,78,117,173,133,188,147,155,169,220,81,13,244,134,242,185,223,105,47,40,3,97,149,255,241]
    | 245920 => JGc_TX2_HashBytes.state [25,110,119,90,229,115,9,14,1,136,89,142,123,146,66,240,29,42,225,45,227,245,237,143,246,109,141,79,34,148,184,86]
    | _ => JGc_TX2_HashBytes.state []
  | 6 => match base with
    | 65600 => JGc_TX2_HashBytes.state [213,219,66,149,132,102,202,223,2,186,92,70,102,98,174,29,190,20,146,248,36,151,27,124,170,129,132,58,230,86,6,226]
    | 93504 => JGc_TX2_HashBytes.state [43,41,156,176,42,40,47,242,5,243,149,73,246,84,151,201,214,4,0,213,156,115,60,243,26,35,74,120,199,7,124,249]
    | 147456 => JGc_TX2_HashBytes.state [166,169,50,209,188,5,52,23,33,230,174,188,64,116,191,107,219,82,103,128,10,79,137,212,138,189,23,60,71,204,95,45]
    | 159744 => JGc_TX2_HashBytes.state [26,45,196,149,156,185,207,108,35,63,83,156,140,215,142,227,222,78,13,88,119,76,111,150,75,170,136,157,17,249,95,75]
    | 183872 => JGc_TX2_HashBytes.state [187,168,249,177,7,164,3,149,98,161,102,174,50,138,206,11,30,72,150,177,137,51,106,119,176,70,87,242,152,194,189,85]
    | 192320 => JGc_TX2_HashBytes.state [73,221,130,144,71,67,136,79,167,63,161,205,39,10,20,47,38,23,24,180,153,220,23,255,9,108,57,158,87,153,49,94]
    | 193024 => JGc_TX2_HashBytes.state [167,255,250,78,90,35,106,202,120,194,253,220,221,11,157,53,242,35,22,107,23,89,62,195,225,140,7,190,221,244,119,208]
    | 209280 => JGc_TX2_HashBytes.state [214,112,195,229,164,168,187,90,35,77,255,198,103,221,16,135,157,106,196,94,83,69,143,19,82,171,67,25,74,114,34,81]
    | 216704 => JGc_TX2_HashBytes.state [99,164,177,65,229,155,166,198,59,58,144,40,119,57,191,57,32,230,224,109,132,52,196,152,102,228,8,147,143,111,177,238]
    | 245952 => JGc_TX2_HashBytes.state [206,137,116,72,150,225,247,109,190,174,193,175,97,74,39,239,82,242,9,20,245,218,106,203,31,54,175,142,188,88,174,158]
    | _ => JGc_TX2_HashBytes.state []
  | 7 => match base with
    | 65664 => JGc_TX2_HashBytes.state [86,144,167,147,188,24,122,130,134,42,53,1,191,205,208,232,136,53,92,205,132,56,195,95,102,211,36,136,20,102,109,234]
    | 93568 => JGc_TX2_HashBytes.state [129,134,159,111,208,119,101,44,121,214,241,176,100,83,224,186,157,157,52,15,168,151,4,234,77,57,92,217,53,20,243,178]
    | 147584 => JGc_TX2_HashBytes.state [229,14,215,228,251,27,121,138,26,111,165,216,200,216,201,136,85,212,71,42,31,194,225,192,175,105,184,67,0,188,222,153]
    | 159872 => JGc_TX2_HashBytes.state [46,123,57,164,118,22,77,38,72,105,83,9,179,113,17,42,45,247,143,151,243,173,174,143,222,205,203,31,224,130,255,177]
    | 183936 => JGc_TX2_HashBytes.state [20,207,22,9,174,31,23,223,78,200,11,111,211,240,97,165,212,117,32,89,62,177,230,187,171,248,29,209,77,89,205,216]
    | 192384 => JGc_TX2_HashBytes.state [152,7,48,143,226,24,235,182,175,169,50,91,216,225,126,157,236,234,179,168,64,123,15,245,94,142,196,215,212,12,175,250]
    | 193152 => JGc_TX2_HashBytes.state [152,67,185,114,180,230,228,197,92,49,68,3,243,160,35,107,236,112,86,221,8,66,205,238,116,218,35,5,165,164,99,104]
    | 209152 => JGc_TX2_HashBytes.state [121,222,231,1,61,67,70,17,115,85,96,65,234,200,241,83,60,16,185,45,192,179,155,106,241,106,46,40,153,49,208,171]
    | 216576 => JGc_TX2_HashBytes.state [236,28,32,239,13,157,49,221,114,96,197,120,98,199,111,87,83,234,74,238,160,52,25,26,27,9,205,113,23,81,124,152]
    | 245760 => JGc_TX2_HashBytes.state [253,228,39,179,67,102,132,204,126,95,1,242,155,20,213,142,13,57,24,198,222,113,242,180,142,143,35,176,242,56,84,56]
    | _ => JGc_TX2_HashBytes.state []
  | 8 => match base with
    | 65792 => JGc_TX2_HashBytes.state [155,103,85,214,79,217,145,109,92,61,81,23,89,65,105,137,67,6,203,28,29,132,157,255,203,70,84,95,242,123,36,113]
    | 93184 => JGc_TX2_HashBytes.state [58,116,96,190,215,232,35,221,38,191,2,90,224,44,164,216,51,1,133,148,238,15,199,54,87,187,234,15,80,91,124,127]
    | 147712 => JGc_TX2_HashBytes.state [102,248,91,151,181,176,166,53,114,57,78,102,66,87,251,100,251,31,205,194,110,147,127,156,193,58,19,3,42,214,148,4]
    | 160000 => JGc_TX2_HashBytes.state [181,230,180,31,12,17,59,166,205,11,33,224,169,103,22,14,162,127,69,73,33,189,217,17,98,68,108,205,174,164,64,124]
    | 184064 => JGc_TX2_HashBytes.state [190,94,5,136,17,62,168,184,31,168,135,148,106,201,77,251,86,192,166,220,228,214,230,238,13,228,237,219,153,182,6,97]
    | 192000 => JGc_TX2_HashBytes.state [101,117,98,190,161,169,31,147,28,228,55,74,81,235,49,28,180,213,167,50,32,72,106,99,146,44,200,203,152,20,148,224]
    | 193280 => JGc_TX2_HashBytes.state [141,78,139,205,243,175,85,174,159,6,241,87,39,153,190,45,228,30,233,41,84,56,127,174,209,151,54,93,242,26,164,0]
    | 208896 => JGc_TX2_HashBytes.state [243,43,79,171,171,236,158,171,6,102,177,162,155,60,85,93,158,195,157,106,68,63,238,61,71,98,3,55,236,229,85,103]
    | 216832 => JGc_TX2_HashBytes.state [0,59,195,249,83,130,210,170,7,120,9,195,215,100,15,59,6,122,239,166,176,134,205,3,143,184,111,215,61,93,21,205]
    | 246016 => JGc_TX2_HashBytes.state [30,110,144,85,51,255,13,5,112,59,188,211,168,27,244,37,155,108,73,250,65,218,219,68,254,71,61,200,99,148,247,126]
    | _ => JGc_TX2_HashBytes.state []
  | 9 => match base with
    | 66048 => JGc_TX2_HashBytes.state [48,144,64,126,184,85,210,61,78,213,35,254,51,10,65,79,191,48,120,196,152,221,171,137,62,2,237,75,217,230,114,206]
    | 93696 => JGc_TX2_HashBytes.state [123,212,65,220,227,135,165,48,10,14,134,81,223,111,216,95,122,145,181,204,233,74,243,55,228,195,231,198,242,45,195,116]
    | 147968 => JGc_TX2_HashBytes.state [105,41,192,88,96,73,217,61,90,149,168,78,2,247,208,1,169,49,116,37,15,146,137,252,165,203,84,179,141,144,47,178]
    | 160256 => JGc_TX2_HashBytes.state [79,110,16,129,18,10,88,204,205,7,170,254,146,27,10,217,216,101,182,33,32,114,45,207,91,16,141,146,44,147,169,198]
    | 183296 => JGc_TX2_HashBytes.state [11,211,99,36,92,115,16,181,114,150,174,18,232,7,212,203,202,159,103,225,65,179,95,167,92,166,67,145,5,238,42,44]
    | 191488 => JGc_TX2_HashBytes.state [208,162,139,184,71,32,217,179,68,248,58,170,4,146,236,236,84,29,218,63,17,10,25,168,216,57,163,181,19,17,253,247]
    | 192512 => JGc_TX2_HashBytes.state [60,103,59,209,113,130,229,235,243,97,45,115,125,45,43,4,217,213,119,152,92,68,200,106,165,187,222,51,4,211,153,18]
    | 209408 => JGc_TX2_HashBytes.state [19,72,36,207,19,187,133,44,138,222,148,125,141,146,17,59,41,212,119,158,223,201,152,145,76,37,91,48,226,129,30,9]
    | 216064 => JGc_TX2_HashBytes.state [186,33,168,206,73,137,127,197,84,223,139,201,20,128,251,0,154,250,60,123,141,245,74,52,213,26,143,116,98,102,120,146]
    | 246272 => JGc_TX2_HashBytes.state [58,64,20,28,188,224,199,55,182,135,197,202,243,225,130,75,187,86,96,87,139,220,144,34,26,247,190,0,220,86,80,95]
    | _ => JGc_TX2_HashBytes.state []
  | 10 => match base with
    | 66560 => JGc_TX2_HashBytes.state [64,93,241,125,70,107,252,101,30,148,14,215,74,250,227,182,249,65,129,42,162,101,220,242,179,42,5,160,220,31,103,150]
    | 92160 => JGc_TX2_HashBytes.state [198,65,48,63,241,221,71,5,120,194,136,208,90,35,236,55,212,20,152,28,68,68,108,189,66,188,78,237,91,99,244,231]
    | 148480 => JGc_TX2_HashBytes.state [164,41,120,158,16,43,175,133,186,191,175,18,223,41,66,159,126,137,11,165,228,232,46,160,78,239,53,218,10,204,109,142]
    | 160768 => JGc_TX2_HashBytes.state [100,11,72,203,23,49,116,82,9,97,40,39,67,176,85,179,239,78,31,49,180,135,233,14,182,133,146,114,96,7,47,39]
    | 182272 => JGc_TX2_HashBytes.state [184,18,54,84,108,157,180,156,80,20,210,100,117,102,246,78,234,211,56,215,194,254,92,204,54,91,195,240,221,94,111,149]
    | 190464 => JGc_TX2_HashBytes.state [63,228,40,85,211,28,242,188,32,35,226,36,237,119,146,127,123,57,188,62,64,103,16,217,15,240,231,101,242,238,216,229]
    | 193536 => JGc_TX2_HashBytes.state [130,69,10,242,115,118,110,253,30,219,254,90,113,163,245,178,100,145,233,86,77,1,166,132,100,215,190,224,34,250,87,35]
    | 209920 => JGc_TX2_HashBytes.state [112,24,125,244,37,57,3,138,146,193,211,93,237,176,196,152,131,55,166,189,57,218,132,5,116,252,78,158,63,50,109,12]
    | 215040 => JGc_TX2_HashBytes.state [215,230,177,31,18,107,67,128,173,64,143,244,114,180,207,188,65,56,143,94,43,60,198,20,173,93,12,193,37,52,52,140]
    | 246784 => JGc_TX2_HashBytes.state [103,164,167,122,243,231,22,164,230,111,87,102,49,233,9,71,238,122,34,122,154,242,71,9,153,52,13,204,21,144,129,141]
    | _ => JGc_TX2_HashBytes.state []
  | 11 => match base with
    | 67584 => JGc_TX2_HashBytes.state [217,175,196,100,106,166,4,160,30,133,139,241,21,195,125,114,222,108,239,37,188,97,229,163,164,197,201,14,71,43,175,9]
    | 90112 => JGc_TX2_HashBytes.state [245,86,191,21,128,168,40,91,146,136,112,192,222,80,59,237,196,147,226,240,168,112,253,192,150,7,143,51,196,9,248,37]
    | 149504 => JGc_TX2_HashBytes.state [211,15,11,17,227,198,215,231,129,25,99,34,247,62,244,155,62,104,100,207,187,196,141,130,8,193,86,21,253,129,202,143]
    | 161792 => JGc_TX2_HashBytes.state [15,101,120,74,113,3,178,205,140,1,22,242,63,68,171,18,163,88,82,90,84,49,24,53,10,48,240,86,180,229,195,57]
    | 180224 => JGc_TX2_HashBytes.state [196,176,224,63,58,66,146,38,214,180,92,204,177,20,194,41,249,159,205,160,145,250,27,12,85,20,34,52,29,203,225,93]
    | 188416 => JGc_TX2_HashBytes.state [167,124,21,206,95,202,120,7,203,62,13,33,133,95,118,113,8,86,18,144,249,35,80,206,151,128,245,184,149,62,143,89]
    | 194560 => JGc_TX2_HashBytes.state [40,24,99,188,225,201,92,11,125,146,207,221,1,133,77,170,92,32,179,180,208,97,222,61,235,239,136,46,164,100,6,189]
    | 210944 => JGc_TX2_HashBytes.state [108,85,77,126,24,37,128,176,24,222,208,119,252,7,77,71,162,105,159,240,41,58,2,199,0,136,85,41,86,124,234,35]
    | 212992 => JGc_TX2_HashBytes.state [210,204,100,222,46,98,83,84,247,179,170,243,109,102,248,130,215,145,18,205,170,10,130,187,6,137,151,18,195,62,117,160]
    | 247808 => JGc_TX2_HashBytes.state [36,122,216,128,213,83,7,55,28,214,71,249,243,137,72,100,98,181,52,193,77,132,94,236,71,30,38,228,18,154,155,76]
    | _ => JGc_TX2_HashBytes.state []
  | 12 => match base with
    | 69632 => JGc_TX2_HashBytes.state [19,103,232,182,95,97,172,122,95,102,130,230,233,176,203,8,117,127,219,234,112,18,233,156,196,18,149,209,241,77,161,56]
    | 94208 => JGc_TX2_HashBytes.state [110,25,47,112,26,76,158,29,84,93,93,101,136,114,133,182,113,217,50,169,101,168,154,202,147,239,155,119,156,1,149,227]
    | 151552 => JGc_TX2_HashBytes.state [125,179,140,223,84,63,248,207,79,4,254,76,50,105,252,113,154,218,31,6,172,77,212,91,67,94,96,253,37,229,243,212]
    | 155648 => JGc_TX2_HashBytes.state [202,244,232,254,150,185,96,120,137,19,88,126,27,134,33,218,94,250,191,155,104,44,152,222,79,170,78,156,230,59,10,83]
    | 184320 => JGc_TX2_HashBytes.state [166,50,145,224,172,240,239,69,50,244,235,90,162,220,82,237,69,91,183,14,206,124,87,33,164,12,204,235,137,70,174,5]
    | 204800 => JGc_TX2_HashBytes.state [153,133,221,15,146,6,115,140,230,185,130,26,225,15,86,62,76,251,182,229,99,145,33,151,46,29,16,78,20,210,184,89]
    | 217088 => JGc_TX2_HashBytes.state [66,199,69,31,236,191,95,45,107,250,179,40,169,78,64,209,27,26,172,83,225,86,252,237,38,168,176,210,39,212,103,98]
    | 249856 => JGc_TX2_HashBytes.state [235,175,68,146,148,50,230,240,90,237,138,62,236,194,107,145,48,135,75,194,84,203,138,124,153,6,202,37,189,117,252,127]
    | _ => JGc_TX2_HashBytes.state []
  | 13 => match base with
    | 73728 => JGc_TX2_HashBytes.state [177,255,241,39,63,158,40,191,219,173,167,140,60,212,238,89,156,75,131,173,118,46,23,106,164,61,132,56,29,231,180,242]
    | 81920 => JGc_TX2_HashBytes.state [148,97,246,244,46,229,113,211,171,213,134,17,121,11,39,232,115,93,64,237,78,176,97,138,178,248,71,111,201,205,160,225]
    | 196608 => JGc_TX2_HashBytes.state [241,9,125,109,23,20,73,46,243,31,183,201,254,168,254,9,17,216,58,151,34,255,100,136,213,89,115,87,251,31,157,167]
    | 221184 => JGc_TX2_HashBytes.state [231,175,9,73,193,151,78,114,131,10,124,215,162,10,201,179,141,208,35,230,20,155,240,194,241,32,103,192,199,110,107,27]
    | 253952 => JGc_TX2_HashBytes.state [105,88,192,232,209,36,116,6,166,207,65,248,208,208,199,3,9,32,125,251,202,216,178,45,163,37,132,171,119,243,170,2]
    | _ => JGc_TX2_HashBytes.state []
  | 14 => match base with
    | 131072 => JGc_TX2_HashBytes.state [77,119,158,98,145,125,73,201,211,192,209,42,9,218,8,172,52,75,152,66,203,147,195,144,242,0,78,78,51,239,33,225]
    | 163840 => JGc_TX2_HashBytes.state [157,235,230,58,63,44,109,204,141,127,215,154,149,77,102,74,49,129,237,95,214,147,79,111,35,41,106,166,126,167,43,139]
    | 229376 => JGc_TX2_HashBytes.state [103,29,162,204,20,167,88,231,167,150,223,135,176,35,230,214,140,125,223,169,142,173,29,189,226,61,203,233,25,171,3,193]
    | _ => JGc_TX2_HashBytes.state []
  | 15 => match base with
    | 98304 => JGc_TX2_HashBytes.state [169,24,176,242,33,202,155,23,158,103,13,74,131,251,160,53,65,59,10,90,129,75,172,213,105,163,148,32,103,32,15,160]
    | _ => JGc_TX2_HashBytes.state []
  | 16 => match base with
    | 0 => JGc_TX2_HashBytes.state [141,210,29,143,172,113,121,140,232,80,9,198,209,48,160,240,216,160,117,117,21,164,211,65,104,173,187,170,81,120,182,252]
    | _ => JGc_TX2_HashBytes.state []
  | 17 => match base with
    | _ => JGc_TX2_HashBytes.state []
  | _ => JGc_TX2_HashBytes.state []
def SiblingLaw (f : Nat → Nat → State) : Prop := ∀ h,h<18 → ∀ b,b∈bases h → f h b=siblingAt h b
theorem unoccupied (f : Nat → Bytes) (g : Nat → Nat → State) (h b : Nat)
    (no : ¬OracleDecisionMultiBuild.Occupied indices h b) :
    OracleDecisionMultiBuild.build indices f g h b=.supplied (g h b) := by
  cases h <;> simp only [OracleDecisionMultiBuild.build,if_neg no]
#print axioms unoccupied
end AspisR1.JHh_C_Gr_M1Roots
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_C_Gr_M1Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input000 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash000.message
def value000 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash000.result
theorem hash000 : JFp_SHADigest.digest input000=value000 := by
  have law := JHe_SHARealization.tree1 ⟨0, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash000
def tree000 : Tree := .opened input000
theorem root000 : root JFp_SHADigest.digest tree000=value000 := hash000
#print axioms root000
def input001 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash001.message
def value001 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash001.result
theorem hash001 : JFp_SHADigest.digest input001=value001 := by
  have law := JHe_SHARealization.tree1 ⟨1, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash001
def tree001 : Tree := .opened input001
theorem root001 : root JFp_SHADigest.digest tree001=value001 := hash001
#print axioms root001
def input002 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash002.message
def value002 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash002.result
theorem hash002 : JFp_SHADigest.digest input002=value002 := by
  have law := JHe_SHARealization.tree1 ⟨2, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash002
def tree002 : Tree := .opened input002
theorem root002 : root JFp_SHADigest.digest tree002=value002 := hash002
#print axioms root002
def input003 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash003.message
def value003 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash003.result
theorem hash003 : JFp_SHADigest.digest input003=value003 := by
  have law := JHe_SHARealization.tree1 ⟨3, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash003
def tree003 : Tree := .opened input003
theorem root003 : root JFp_SHADigest.digest tree003=value003 := hash003
#print axioms root003
def input004 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash004.message
def value004 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash004.result
theorem hash004 : JFp_SHADigest.digest input004=value004 := by
  have law := JHe_SHARealization.tree1 ⟨4, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash004
def tree004 : Tree := .opened input004
theorem root004 : root JFp_SHADigest.digest tree004=value004 := hash004
#print axioms root004
def input005 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash005.message
def value005 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash005.result
theorem hash005 : JFp_SHADigest.digest input005=value005 := by
  have law := JHe_SHARealization.tree1 ⟨5, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash005
def tree005 : Tree := .opened input005
theorem root005 : root JFp_SHADigest.digest tree005=value005 := hash005
#print axioms root005
def input006 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash006.message
def value006 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash006.result
theorem hash006 : JFp_SHADigest.digest input006=value006 := by
  have law := JHe_SHARealization.tree1 ⟨6, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash006
def tree006 : Tree := .opened input006
theorem root006 : root JFp_SHADigest.digest tree006=value006 := hash006
#print axioms root006
def input007 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash007.message
def value007 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash007.result
theorem hash007 : JFp_SHADigest.digest input007=value007 := by
  have law := JHe_SHARealization.tree1 ⟨7, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash007
def tree007 : Tree := .opened input007
theorem root007 : root JFp_SHADigest.digest tree007=value007 := hash007
#print axioms root007
def input008 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash008.message
def value008 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash008.result
theorem hash008 : JFp_SHADigest.digest input008=value008 := by
  have law := JHe_SHARealization.tree1 ⟨8, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash008
def tree008 : Tree := .opened input008
theorem root008 : root JFp_SHADigest.digest tree008=value008 := hash008
#print axioms root008
def input009 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash009.message
def value009 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash009.result
theorem hash009 : JFp_SHADigest.digest input009=value009 := by
  have law := JHe_SHARealization.tree1 ⟨9, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash009
def tree009 : Tree := .opened input009
theorem root009 : root JFp_SHADigest.digest tree009=value009 := hash009
#print axioms root009
def inputAt (base : Nat) : Bytes := match base with
  | 93499 => input000
  | 147529 => input001
  | 216823 => input002
  | 245899 => input003
  | 209371 => input004
  | 192317 => input005
  | 65593 => input006
  | 183859 => input007
  | 193093 => input008
  | 159813 => input009
  | _ => []
def InputLaw (f : Nat → Bytes) : Prop := ∀ b,b∈indices → f b=inputAt b
theorem shape000 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (_siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 0 93499=tree000 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 0 93499),inputs 93499 (by decide)]
  rfl
#print axioms shape000
theorem shape001 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (_siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 0 147529=tree001 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 0 147529),inputs 147529 (by decide)]
  rfl
#print axioms shape001
theorem shape002 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (_siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 0 216823=tree002 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 0 216823),inputs 216823 (by decide)]
  rfl
#print axioms shape002
theorem shape003 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (_siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 0 245899=tree003 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 0 245899),inputs 245899 (by decide)]
  rfl
#print axioms shape003
theorem shape004 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (_siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 0 209371=tree004 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 0 209371),inputs 209371 (by decide)]
  rfl
#print axioms shape004
theorem shape005 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (_siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 0 192317=tree005 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 0 192317),inputs 192317 (by decide)]
  rfl
#print axioms shape005
theorem shape006 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (_siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 0 65593=tree006 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 0 65593),inputs 65593 (by decide)]
  rfl
#print axioms shape006
theorem shape007 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (_siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 0 183859=tree007 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 0 183859),inputs 183859 (by decide)]
  rfl
#print axioms shape007
theorem shape008 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (_siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 0 193093=tree008 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 0 193093),inputs 193093 (by decide)]
  rfl
#print axioms shape008
theorem shape009 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (_siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 0 159813=tree009 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 0 159813),inputs 159813 (by decide)]
  rfl
#print axioms shape009
end AspisR1.JHh_C_Gr_M1Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_C_Gr_M1Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input010 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash010.message
def value010 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash010.result
theorem hash010 : JFp_SHADigest.digest input010=value010 := by
  have law := JHe_SHARealization.tree1 ⟨10, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash010
theorem address010 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [84,158,189,163,7,211,150,118,46,159,127,12,244,157,167,96,164,240,68,44,151,232,222,236,240,147,88,216,134,56,255,201]) value006)=input010 := by rfl
#print axioms address010
def tree010 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [84,158,189,163,7,211,150,118,46,159,127,12,244,157,167,96,164,240,68,44,151,232,222,236,240,147,88,216,134,56,255,201])) tree006
theorem root010 : root JFp_SHADigest.digest tree010=value010 := by
  rw [tree010,root,root006]
  exact (congrArg JFp_SHADigest.digest address010).trans hash010
#print axioms root010
theorem shape010 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 65592=tree010 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 65592)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 0 65592 (by decide),siblings 0 (by decide) 65592 (by decide)]
  rw [shape006 f g inputs siblings]
  rfl
#print axioms shape010
def input011 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash011.message
def value011 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash011.result
theorem hash011 : JFp_SHADigest.digest input011=value011 := by
  have law := JHe_SHARealization.tree1 ⟨11, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash011
theorem address011 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [87,201,97,142,46,240,30,62,247,57,210,209,11,218,107,245,200,85,9,191,193,152,235,191,239,43,233,153,92,147,12,22]) value000)=input011 := by rfl
#print axioms address011
def tree011 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [87,201,97,142,46,240,30,62,247,57,210,209,11,218,107,245,200,85,9,191,193,152,235,191,239,43,233,153,92,147,12,22])) tree000
theorem root011 : root JFp_SHADigest.digest tree011=value011 := by
  rw [tree011,root,root000]
  exact (congrArg JFp_SHADigest.digest address011).trans hash011
#print axioms root011
theorem shape011 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 93498=tree011 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 93498)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 0 93498 (by decide),siblings 0 (by decide) 93498 (by decide)]
  rw [shape000 f g inputs siblings]
  rfl
#print axioms shape011
def input012 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash012.message
def value012 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash012.result
theorem hash012 : JFp_SHADigest.digest input012=value012 := by
  have law := JHe_SHARealization.tree1 ⟨12, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash012
theorem address012 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [126,244,47,162,206,176,63,208,66,80,97,27,124,150,156,29,16,125,4,24,229,40,80,226,50,22,217,21,9,118,223,64]) value001)=input012 := by rfl
#print axioms address012
def tree012 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [126,244,47,162,206,176,63,208,66,80,97,27,124,150,156,29,16,125,4,24,229,40,80,226,50,22,217,21,9,118,223,64])) tree001
theorem root012 : root JFp_SHADigest.digest tree012=value012 := by
  rw [tree012,root,root001]
  exact (congrArg JFp_SHADigest.digest address012).trans hash012
#print axioms root012
theorem shape012 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 147528=tree012 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 147528)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 0 147528 (by decide),siblings 0 (by decide) 147528 (by decide)]
  rw [shape001 f g inputs siblings]
  rfl
#print axioms shape012
def input013 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash013.message
def value013 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash013.result
theorem hash013 : JFp_SHADigest.digest input013=value013 := by
  have law := JHe_SHARealization.tree1 ⟨13, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash013
theorem address013 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [105,207,46,68,125,195,225,145,182,7,102,115,151,53,228,97,66,255,193,10,177,180,57,243,141,165,117,4,62,94,100,227]) value009)=input013 := by rfl
#print axioms address013
def tree013 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [105,207,46,68,125,195,225,145,182,7,102,115,151,53,228,97,66,255,193,10,177,180,57,243,141,165,117,4,62,94,100,227])) tree009
theorem root013 : root JFp_SHADigest.digest tree013=value013 := by
  rw [tree013,root,root009]
  exact (congrArg JFp_SHADigest.digest address013).trans hash013
#print axioms root013
theorem shape013 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 159812=tree013 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 159812)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 0 159812 (by decide),siblings 0 (by decide) 159812 (by decide)]
  rw [shape009 f g inputs siblings]
  rfl
#print axioms shape013
def input014 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash014.message
def value014 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash014.result
theorem hash014 : JFp_SHADigest.digest input014=value014 := by
  have law := JHe_SHARealization.tree1 ⟨14, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash014
theorem address014 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [178,45,27,133,141,100,37,222,96,165,67,100,140,205,14,251,78,74,113,201,225,78,242,12,210,165,12,143,151,125,240,161]) value007)=input014 := by rfl
#print axioms address014
def tree014 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [178,45,27,133,141,100,37,222,96,165,67,100,140,205,14,251,78,74,113,201,225,78,242,12,210,165,12,143,151,125,240,161])) tree007
theorem root014 : root JFp_SHADigest.digest tree014=value014 := by
  rw [tree014,root,root007]
  exact (congrArg JFp_SHADigest.digest address014).trans hash014
#print axioms root014
theorem shape014 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 183858=tree014 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 183858)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 0 183858 (by decide),siblings 0 (by decide) 183858 (by decide)]
  rw [shape007 f g inputs siblings]
  rfl
#print axioms shape014
def input015 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash015.message
def value015 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash015.result
theorem hash015 : JFp_SHADigest.digest input015=value015 := by
  have law := JHe_SHARealization.tree1 ⟨15, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash015
theorem address015 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [208,201,87,103,45,128,36,40,65,168,170,172,133,87,105,49,90,3,53,79,63,150,156,172,52,208,232,217,131,11,191,68]) value005)=input015 := by rfl
#print axioms address015
def tree015 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [208,201,87,103,45,128,36,40,65,168,170,172,133,87,105,49,90,3,53,79,63,150,156,172,52,208,232,217,131,11,191,68])) tree005
theorem root015 : root JFp_SHADigest.digest tree015=value015 := by
  rw [tree015,root,root005]
  exact (congrArg JFp_SHADigest.digest address015).trans hash015
#print axioms root015
theorem shape015 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 192316=tree015 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 192316)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 0 192316 (by decide),siblings 0 (by decide) 192316 (by decide)]
  rw [shape005 f g inputs siblings]
  rfl
#print axioms shape015
def input016 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash016.message
def value016 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash016.result
theorem hash016 : JFp_SHADigest.digest input016=value016 := by
  have law := JHe_SHARealization.tree1 ⟨16, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash016
theorem address016 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [58,250,234,236,124,53,147,155,154,165,220,179,164,49,96,165,20,23,164,50,251,216,34,12,121,250,222,56,113,154,22,180]) value008)=input016 := by rfl
#print axioms address016
def tree016 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [58,250,234,236,124,53,147,155,154,165,220,179,164,49,96,165,20,23,164,50,251,216,34,12,121,250,222,56,113,154,22,180])) tree008
theorem root016 : root JFp_SHADigest.digest tree016=value016 := by
  rw [tree016,root,root008]
  exact (congrArg JFp_SHADigest.digest address016).trans hash016
#print axioms root016
theorem shape016 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 193092=tree016 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 193092)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 0 193092 (by decide),siblings 0 (by decide) 193092 (by decide)]
  rw [shape008 f g inputs siblings]
  rfl
#print axioms shape016
def input017 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash017.message
def value017 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash017.result
theorem hash017 : JFp_SHADigest.digest input017=value017 := by
  have law := JHe_SHARealization.tree1 ⟨17, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash017
theorem address017 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [229,11,75,185,166,129,153,153,211,153,179,106,3,80,171,146,89,184,131,52,57,244,191,194,9,142,23,33,62,19,35,156]) value004)=input017 := by rfl
#print axioms address017
def tree017 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [229,11,75,185,166,129,153,153,211,153,179,106,3,80,171,146,89,184,131,52,57,244,191,194,9,142,23,33,62,19,35,156])) tree004
theorem root017 : root JFp_SHADigest.digest tree017=value017 := by
  rw [tree017,root,root004]
  exact (congrArg JFp_SHADigest.digest address017).trans hash017
#print axioms root017
theorem shape017 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 209370=tree017 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 209370)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 0 209370 (by decide),siblings 0 (by decide) 209370 (by decide)]
  rw [shape004 f g inputs siblings]
  rfl
#print axioms shape017
def input018 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash018.message
def value018 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash018.result
theorem hash018 : JFp_SHADigest.digest input018=value018 := by
  have law := JHe_SHARealization.tree1 ⟨18, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash018
theorem address018 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [232,135,117,237,45,118,87,95,67,116,77,226,109,208,88,160,202,241,38,170,96,84,230,88,96,117,190,107,137,190,145,40]) value002)=input018 := by rfl
#print axioms address018
def tree018 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [232,135,117,237,45,118,87,95,67,116,77,226,109,208,88,160,202,241,38,170,96,84,230,88,96,117,190,107,137,190,145,40])) tree002
theorem root018 : root JFp_SHADigest.digest tree018=value018 := by
  rw [tree018,root,root002]
  exact (congrArg JFp_SHADigest.digest address018).trans hash018
#print axioms root018
theorem shape018 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 216822=tree018 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 216822)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 0 216822 (by decide),siblings 0 (by decide) 216822 (by decide)]
  rw [shape002 f g inputs siblings]
  rfl
#print axioms shape018
def input019 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash019.message
def value019 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash019.result
theorem hash019 : JFp_SHADigest.digest input019=value019 := by
  have law := JHe_SHARealization.tree1 ⟨19, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash019
theorem address019 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [198,199,120,82,46,88,27,188,251,85,66,197,217,209,68,171,23,178,127,119,231,149,16,43,202,127,140,173,252,101,60,6]) value003)=input019 := by rfl
#print axioms address019
def tree019 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [198,199,120,82,46,88,27,188,251,85,66,197,217,209,68,171,23,178,127,119,231,149,16,43,202,127,140,173,252,101,60,6])) tree003
theorem root019 : root JFp_SHADigest.digest tree019=value019 := by
  rw [tree019,root,root003]
  exact (congrArg JFp_SHADigest.digest address019).trans hash019
#print axioms root019
theorem shape019 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 245898=tree019 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 245898)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 0 245898 (by decide),siblings 0 (by decide) 245898 (by decide)]
  rw [shape003 f g inputs siblings]
  rfl
#print axioms shape019
end AspisR1.JHh_C_Gr_M1Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_C_Gr_M1Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input020 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash020.message
def value020 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash020.result
theorem hash020 : JFp_SHADigest.digest input020=value020 := by
  have law := JHe_SHARealization.tree1 ⟨20, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash020
theorem address020 : BinMerkle32Path.nodeInput (children value010 (JGc_TX2_HashBytes.state [226,19,230,186,28,97,100,40,122,60,48,235,166,167,156,189,127,126,176,209,146,207,129,60,75,115,18,146,199,245,51,199]))=input020 := by rfl
#print axioms address020
def tree020 : Tree := .branch tree010 (.supplied (JGc_TX2_HashBytes.state [226,19,230,186,28,97,100,40,122,60,48,235,166,167,156,189,127,126,176,209,146,207,129,60,75,115,18,146,199,245,51,199]))
theorem root020 : root JFp_SHADigest.digest tree020=value020 := by
  rw [tree020,root,root010]
  exact (congrArg JFp_SHADigest.digest address020).trans hash020
#print axioms root020
theorem shape020 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 65592=tree020 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 65592)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape010 f g inputs siblings]
  rw [unoccupied f g 1 65594 (by decide),siblings 1 (by decide) 65594 (by decide)]
  rfl
#print axioms shape020
def input021 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash021.message
def value021 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash021.result
theorem hash021 : JFp_SHADigest.digest input021=value021 := by
  have law := JHe_SHARealization.tree1 ⟨21, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash021
theorem address021 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [53,199,117,75,221,203,227,135,140,20,26,44,148,40,245,6,247,144,199,69,152,25,40,59,8,112,100,10,148,1,240,224]) value011)=input021 := by rfl
#print axioms address021
def tree021 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [53,199,117,75,221,203,227,135,140,20,26,44,148,40,245,6,247,144,199,69,152,25,40,59,8,112,100,10,148,1,240,224])) tree011
theorem root021 : root JFp_SHADigest.digest tree021=value021 := by
  rw [tree021,root,root011]
  exact (congrArg JFp_SHADigest.digest address021).trans hash021
#print axioms root021
theorem shape021 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 93496=tree021 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 93496)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 1 93496 (by decide),siblings 1 (by decide) 93496 (by decide)]
  rw [shape011 f g inputs siblings]
  rfl
#print axioms shape021
def input022 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash022.message
def value022 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash022.result
theorem hash022 : JFp_SHADigest.digest input022=value022 := by
  have law := JHe_SHARealization.tree1 ⟨22, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash022
theorem address022 : BinMerkle32Path.nodeInput (children value012 (JGc_TX2_HashBytes.state [192,50,200,213,36,199,105,201,154,83,49,107,171,199,140,138,138,25,255,180,249,204,200,221,50,43,166,214,67,36,110,16]))=input022 := by rfl
#print axioms address022
def tree022 : Tree := .branch tree012 (.supplied (JGc_TX2_HashBytes.state [192,50,200,213,36,199,105,201,154,83,49,107,171,199,140,138,138,25,255,180,249,204,200,221,50,43,166,214,67,36,110,16]))
theorem root022 : root JFp_SHADigest.digest tree022=value022 := by
  rw [tree022,root,root012]
  exact (congrArg JFp_SHADigest.digest address022).trans hash022
#print axioms root022
theorem shape022 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 147528=tree022 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 147528)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape012 f g inputs siblings]
  rw [unoccupied f g 1 147530 (by decide),siblings 1 (by decide) 147530 (by decide)]
  rfl
#print axioms shape022
def input023 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash023.message
def value023 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash023.result
theorem hash023 : JFp_SHADigest.digest input023=value023 := by
  have law := JHe_SHARealization.tree1 ⟨23, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash023
theorem address023 : BinMerkle32Path.nodeInput (children value013 (JGc_TX2_HashBytes.state [102,110,213,2,148,96,173,189,56,93,84,101,64,44,166,50,155,9,114,234,56,56,211,60,155,126,100,123,86,255,245,207]))=input023 := by rfl
#print axioms address023
def tree023 : Tree := .branch tree013 (.supplied (JGc_TX2_HashBytes.state [102,110,213,2,148,96,173,189,56,93,84,101,64,44,166,50,155,9,114,234,56,56,211,60,155,126,100,123,86,255,245,207]))
theorem root023 : root JFp_SHADigest.digest tree023=value023 := by
  rw [tree023,root,root013]
  exact (congrArg JFp_SHADigest.digest address023).trans hash023
#print axioms root023
theorem shape023 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 159812=tree023 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 159812)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape013 f g inputs siblings]
  rw [unoccupied f g 1 159814 (by decide),siblings 1 (by decide) 159814 (by decide)]
  rfl
#print axioms shape023
def input024 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash024.message
def value024 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash024.result
theorem hash024 : JFp_SHADigest.digest input024=value024 := by
  have law := JHe_SHARealization.tree1 ⟨24, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash024
theorem address024 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [207,254,248,226,47,19,54,49,165,112,36,160,160,101,28,252,240,13,181,65,153,32,3,78,22,59,184,81,253,195,95,153]) value014)=input024 := by rfl
#print axioms address024
def tree024 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [207,254,248,226,47,19,54,49,165,112,36,160,160,101,28,252,240,13,181,65,153,32,3,78,22,59,184,81,253,195,95,153])) tree014
theorem root024 : root JFp_SHADigest.digest tree024=value024 := by
  rw [tree024,root,root014]
  exact (congrArg JFp_SHADigest.digest address024).trans hash024
#print axioms root024
theorem shape024 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 183856=tree024 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 183856)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 1 183856 (by decide),siblings 1 (by decide) 183856 (by decide)]
  rw [shape014 f g inputs siblings]
  rfl
#print axioms shape024
def input025 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash025.message
def value025 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash025.result
theorem hash025 : JFp_SHADigest.digest input025=value025 := by
  have law := JHe_SHARealization.tree1 ⟨25, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash025
theorem address025 : BinMerkle32Path.nodeInput (children value015 (JGc_TX2_HashBytes.state [118,182,6,74,103,244,136,114,84,255,217,64,189,71,61,128,226,133,217,73,78,68,236,158,199,227,240,136,1,108,57,83]))=input025 := by rfl
#print axioms address025
def tree025 : Tree := .branch tree015 (.supplied (JGc_TX2_HashBytes.state [118,182,6,74,103,244,136,114,84,255,217,64,189,71,61,128,226,133,217,73,78,68,236,158,199,227,240,136,1,108,57,83]))
theorem root025 : root JFp_SHADigest.digest tree025=value025 := by
  rw [tree025,root,root015]
  exact (congrArg JFp_SHADigest.digest address025).trans hash025
#print axioms root025
theorem shape025 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 192316=tree025 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 192316)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape015 f g inputs siblings]
  rw [unoccupied f g 1 192318 (by decide),siblings 1 (by decide) 192318 (by decide)]
  rfl
#print axioms shape025
def input026 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash026.message
def value026 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash026.result
theorem hash026 : JFp_SHADigest.digest input026=value026 := by
  have law := JHe_SHARealization.tree1 ⟨26, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash026
theorem address026 : BinMerkle32Path.nodeInput (children value016 (JGc_TX2_HashBytes.state [198,145,218,11,27,71,231,58,41,252,108,230,167,179,48,30,19,243,203,144,105,210,9,80,77,183,232,151,137,4,170,15]))=input026 := by rfl
#print axioms address026
def tree026 : Tree := .branch tree016 (.supplied (JGc_TX2_HashBytes.state [198,145,218,11,27,71,231,58,41,252,108,230,167,179,48,30,19,243,203,144,105,210,9,80,77,183,232,151,137,4,170,15]))
theorem root026 : root JFp_SHADigest.digest tree026=value026 := by
  rw [tree026,root,root016]
  exact (congrArg JFp_SHADigest.digest address026).trans hash026
#print axioms root026
theorem shape026 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 193092=tree026 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 193092)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape016 f g inputs siblings]
  rw [unoccupied f g 1 193094 (by decide),siblings 1 (by decide) 193094 (by decide)]
  rfl
#print axioms shape026
def input027 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash027.message
def value027 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash027.result
theorem hash027 : JFp_SHADigest.digest input027=value027 := by
  have law := JHe_SHARealization.tree1 ⟨27, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash027
theorem address027 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [104,141,228,117,121,171,3,4,176,4,107,28,254,224,219,29,112,25,96,120,70,213,98,52,25,175,170,185,190,225,223,156]) value017)=input027 := by rfl
#print axioms address027
def tree027 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [104,141,228,117,121,171,3,4,176,4,107,28,254,224,219,29,112,25,96,120,70,213,98,52,25,175,170,185,190,225,223,156])) tree017
theorem root027 : root JFp_SHADigest.digest tree027=value027 := by
  rw [tree027,root,root017]
  exact (congrArg JFp_SHADigest.digest address027).trans hash027
#print axioms root027
theorem shape027 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 209368=tree027 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 209368)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 1 209368 (by decide),siblings 1 (by decide) 209368 (by decide)]
  rw [shape017 f g inputs siblings]
  rfl
#print axioms shape027
def input028 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash028.message
def value028 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash028.result
theorem hash028 : JFp_SHADigest.digest input028=value028 := by
  have law := JHe_SHARealization.tree1 ⟨28, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash028
theorem address028 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [86,28,233,120,193,72,153,62,145,245,239,192,86,31,200,86,29,20,129,186,93,27,187,6,64,75,180,174,8,117,228,16]) value018)=input028 := by rfl
#print axioms address028
def tree028 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [86,28,233,120,193,72,153,62,145,245,239,192,86,31,200,86,29,20,129,186,93,27,187,6,64,75,180,174,8,117,228,16])) tree018
theorem root028 : root JFp_SHADigest.digest tree028=value028 := by
  rw [tree028,root,root018]
  exact (congrArg JFp_SHADigest.digest address028).trans hash028
#print axioms root028
theorem shape028 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 216820=tree028 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 216820)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 1 216820 (by decide),siblings 1 (by decide) 216820 (by decide)]
  rw [shape018 f g inputs siblings]
  rfl
#print axioms shape028
def input029 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash029.message
def value029 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash029.result
theorem hash029 : JFp_SHADigest.digest input029=value029 := by
  have law := JHe_SHARealization.tree1 ⟨29, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash029
theorem address029 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [46,114,18,158,240,245,37,120,114,167,15,134,67,123,175,250,230,84,253,40,11,47,196,152,226,249,239,35,86,182,35,30]) value019)=input029 := by rfl
#print axioms address029
def tree029 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [46,114,18,158,240,245,37,120,114,167,15,134,67,123,175,250,230,84,253,40,11,47,196,152,226,249,239,35,86,182,35,30])) tree019
theorem root029 : root JFp_SHADigest.digest tree029=value029 := by
  rw [tree029,root,root019]
  exact (congrArg JFp_SHADigest.digest address029).trans hash029
#print axioms root029
theorem shape029 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 245896=tree029 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 245896)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 1 245896 (by decide),siblings 1 (by decide) 245896 (by decide)]
  rw [shape019 f g inputs siblings]
  rfl
#print axioms shape029
end AspisR1.JHh_C_Gr_M1Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_C_Gr_M1Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input030 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash030.message
def value030 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash030.result
theorem hash030 : JFp_SHADigest.digest input030=value030 := by
  have law := JHe_SHARealization.tree1 ⟨30, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash030
theorem address030 : BinMerkle32Path.nodeInput (children value020 (JGc_TX2_HashBytes.state [161,76,3,159,191,249,90,238,12,33,36,222,12,85,198,154,218,16,194,33,132,91,57,18,102,89,24,129,206,192,84,2]))=input030 := by rfl
#print axioms address030
def tree030 : Tree := .branch tree020 (.supplied (JGc_TX2_HashBytes.state [161,76,3,159,191,249,90,238,12,33,36,222,12,85,198,154,218,16,194,33,132,91,57,18,102,89,24,129,206,192,84,2]))
theorem root030 : root JFp_SHADigest.digest tree030=value030 := by
  rw [tree030,root,root020]
  exact (congrArg JFp_SHADigest.digest address030).trans hash030
#print axioms root030
theorem shape030 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 65592=tree030 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 65592)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape020 f g inputs siblings]
  rw [unoccupied f g 2 65596 (by decide),siblings 2 (by decide) 65596 (by decide)]
  rfl
#print axioms shape030
def input031 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash031.message
def value031 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash031.result
theorem hash031 : JFp_SHADigest.digest input031=value031 := by
  have law := JHe_SHARealization.tree1 ⟨31, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash031
theorem address031 : BinMerkle32Path.nodeInput (children value021 (JGc_TX2_HashBytes.state [150,245,179,73,238,203,63,9,99,117,193,114,224,59,215,81,139,40,94,196,154,161,204,163,131,194,211,158,164,68,7,147]))=input031 := by rfl
#print axioms address031
def tree031 : Tree := .branch tree021 (.supplied (JGc_TX2_HashBytes.state [150,245,179,73,238,203,63,9,99,117,193,114,224,59,215,81,139,40,94,196,154,161,204,163,131,194,211,158,164,68,7,147]))
theorem root031 : root JFp_SHADigest.digest tree031=value031 := by
  rw [tree031,root,root021]
  exact (congrArg JFp_SHADigest.digest address031).trans hash031
#print axioms root031
theorem shape031 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 93496=tree031 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 93496)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape021 f g inputs siblings]
  rw [unoccupied f g 2 93500 (by decide),siblings 2 (by decide) 93500 (by decide)]
  rfl
#print axioms shape031
def input032 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash032.message
def value032 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash032.result
theorem hash032 : JFp_SHADigest.digest input032=value032 := by
  have law := JHe_SHARealization.tree1 ⟨32, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash032
theorem address032 : BinMerkle32Path.nodeInput (children value022 (JGc_TX2_HashBytes.state [97,255,106,209,39,206,184,200,255,182,229,243,150,159,37,202,105,5,207,52,192,189,18,106,9,249,42,77,128,132,228,204]))=input032 := by rfl
#print axioms address032
def tree032 : Tree := .branch tree022 (.supplied (JGc_TX2_HashBytes.state [97,255,106,209,39,206,184,200,255,182,229,243,150,159,37,202,105,5,207,52,192,189,18,106,9,249,42,77,128,132,228,204]))
theorem root032 : root JFp_SHADigest.digest tree032=value032 := by
  rw [tree032,root,root022]
  exact (congrArg JFp_SHADigest.digest address032).trans hash032
#print axioms root032
theorem shape032 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 147528=tree032 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 147528)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape022 f g inputs siblings]
  rw [unoccupied f g 2 147532 (by decide),siblings 2 (by decide) 147532 (by decide)]
  rfl
#print axioms shape032
def input033 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash033.message
def value033 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash033.result
theorem hash033 : JFp_SHADigest.digest input033=value033 := by
  have law := JHe_SHARealization.tree1 ⟨33, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash033
theorem address033 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [198,117,40,249,115,8,80,114,136,28,25,209,63,143,53,34,247,134,30,13,179,145,39,114,51,86,73,45,212,147,188,0]) value023)=input033 := by rfl
#print axioms address033
def tree033 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [198,117,40,249,115,8,80,114,136,28,25,209,63,143,53,34,247,134,30,13,179,145,39,114,51,86,73,45,212,147,188,0])) tree023
theorem root033 : root JFp_SHADigest.digest tree033=value033 := by
  rw [tree033,root,root023]
  exact (congrArg JFp_SHADigest.digest address033).trans hash033
#print axioms root033
theorem shape033 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 159808=tree033 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 159808)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 2 159808 (by decide),siblings 2 (by decide) 159808 (by decide)]
  rw [shape023 f g inputs siblings]
  rfl
#print axioms shape033
def input034 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash034.message
def value034 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash034.result
theorem hash034 : JFp_SHADigest.digest input034=value034 := by
  have law := JHe_SHARealization.tree1 ⟨34, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash034
theorem address034 : BinMerkle32Path.nodeInput (children value024 (JGc_TX2_HashBytes.state [173,160,200,2,87,10,143,76,228,213,202,85,241,88,184,137,184,213,12,133,110,196,125,206,65,42,21,23,14,224,135,18]))=input034 := by rfl
#print axioms address034
def tree034 : Tree := .branch tree024 (.supplied (JGc_TX2_HashBytes.state [173,160,200,2,87,10,143,76,228,213,202,85,241,88,184,137,184,213,12,133,110,196,125,206,65,42,21,23,14,224,135,18]))
theorem root034 : root JFp_SHADigest.digest tree034=value034 := by
  rw [tree034,root,root024]
  exact (congrArg JFp_SHADigest.digest address034).trans hash034
#print axioms root034
theorem shape034 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 183856=tree034 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 183856)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape024 f g inputs siblings]
  rw [unoccupied f g 2 183860 (by decide),siblings 2 (by decide) 183860 (by decide)]
  rfl
#print axioms shape034
def input035 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash035.message
def value035 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash035.result
theorem hash035 : JFp_SHADigest.digest input035=value035 := by
  have law := JHe_SHARealization.tree1 ⟨35, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash035
theorem address035 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [16,128,131,147,46,155,13,197,29,34,144,51,143,28,229,54,178,32,183,183,140,105,113,160,115,195,214,144,94,12,128,80]) value025)=input035 := by rfl
#print axioms address035
def tree035 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [16,128,131,147,46,155,13,197,29,34,144,51,143,28,229,54,178,32,183,183,140,105,113,160,115,195,214,144,94,12,128,80])) tree025
theorem root035 : root JFp_SHADigest.digest tree035=value035 := by
  rw [tree035,root,root025]
  exact (congrArg JFp_SHADigest.digest address035).trans hash035
#print axioms root035
theorem shape035 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 192312=tree035 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 192312)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 2 192312 (by decide),siblings 2 (by decide) 192312 (by decide)]
  rw [shape025 f g inputs siblings]
  rfl
#print axioms shape035
def input036 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash036.message
def value036 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash036.result
theorem hash036 : JFp_SHADigest.digest input036=value036 := by
  have law := JHe_SHARealization.tree1 ⟨36, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash036
theorem address036 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [140,101,31,60,165,201,60,75,58,216,73,119,83,95,32,127,113,252,104,199,28,200,24,47,1,108,50,255,0,221,161,140]) value026)=input036 := by rfl
#print axioms address036
def tree036 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [140,101,31,60,165,201,60,75,58,216,73,119,83,95,32,127,113,252,104,199,28,200,24,47,1,108,50,255,0,221,161,140])) tree026
theorem root036 : root JFp_SHADigest.digest tree036=value036 := by
  rw [tree036,root,root026]
  exact (congrArg JFp_SHADigest.digest address036).trans hash036
#print axioms root036
theorem shape036 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 193088=tree036 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 193088)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 2 193088 (by decide),siblings 2 (by decide) 193088 (by decide)]
  rw [shape026 f g inputs siblings]
  rfl
#print axioms shape036
def input037 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash037.message
def value037 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash037.result
theorem hash037 : JFp_SHADigest.digest input037=value037 := by
  have law := JHe_SHARealization.tree1 ⟨37, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash037
theorem address037 : BinMerkle32Path.nodeInput (children value027 (JGc_TX2_HashBytes.state [43,150,240,241,176,44,116,229,80,221,23,5,12,189,27,226,164,73,153,251,188,47,181,148,5,149,67,154,125,10,233,211]))=input037 := by rfl
#print axioms address037
def tree037 : Tree := .branch tree027 (.supplied (JGc_TX2_HashBytes.state [43,150,240,241,176,44,116,229,80,221,23,5,12,189,27,226,164,73,153,251,188,47,181,148,5,149,67,154,125,10,233,211]))
theorem root037 : root JFp_SHADigest.digest tree037=value037 := by
  rw [tree037,root,root027]
  exact (congrArg JFp_SHADigest.digest address037).trans hash037
#print axioms root037
theorem shape037 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 209368=tree037 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 209368)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape027 f g inputs siblings]
  rw [unoccupied f g 2 209372 (by decide),siblings 2 (by decide) 209372 (by decide)]
  rfl
#print axioms shape037
def input038 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash038.message
def value038 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash038.result
theorem hash038 : JFp_SHADigest.digest input038=value038 := by
  have law := JHe_SHARealization.tree1 ⟨38, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash038
theorem address038 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [43,146,168,238,162,23,68,80,31,163,96,208,148,23,64,85,154,125,92,177,215,158,253,133,121,24,22,161,219,238,202,61]) value028)=input038 := by rfl
#print axioms address038
def tree038 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [43,146,168,238,162,23,68,80,31,163,96,208,148,23,64,85,154,125,92,177,215,158,253,133,121,24,22,161,219,238,202,61])) tree028
theorem root038 : root JFp_SHADigest.digest tree038=value038 := by
  rw [tree038,root,root028]
  exact (congrArg JFp_SHADigest.digest address038).trans hash038
#print axioms root038
theorem shape038 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 216816=tree038 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 216816)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 2 216816 (by decide),siblings 2 (by decide) 216816 (by decide)]
  rw [shape028 f g inputs siblings]
  rfl
#print axioms shape038
def input039 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash039.message
def value039 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash039.result
theorem hash039 : JFp_SHADigest.digest input039=value039 := by
  have law := JHe_SHARealization.tree1 ⟨39, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash039
theorem address039 : BinMerkle32Path.nodeInput (children value029 (JGc_TX2_HashBytes.state [254,103,22,216,177,229,178,69,230,133,92,137,126,145,115,176,102,124,84,213,140,225,194,132,77,135,97,138,229,59,250,215]))=input039 := by rfl
#print axioms address039
def tree039 : Tree := .branch tree029 (.supplied (JGc_TX2_HashBytes.state [254,103,22,216,177,229,178,69,230,133,92,137,126,145,115,176,102,124,84,213,140,225,194,132,77,135,97,138,229,59,250,215]))
theorem root039 : root JFp_SHADigest.digest tree039=value039 := by
  rw [tree039,root,root029]
  exact (congrArg JFp_SHADigest.digest address039).trans hash039
#print axioms root039
theorem shape039 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 245896=tree039 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 245896)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape029 f g inputs siblings]
  rw [unoccupied f g 2 245900 (by decide),siblings 2 (by decide) 245900 (by decide)]
  rfl
#print axioms shape039
end AspisR1.JHh_C_Gr_M1Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_C_Gr_M1Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input040 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash040.message
def value040 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash040.result
theorem hash040 : JFp_SHADigest.digest input040=value040 := by
  have law := JHe_SHARealization.tree1 ⟨40, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash040
theorem address040 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [174,82,153,70,104,229,145,166,155,82,31,251,14,90,80,67,114,199,139,42,46,185,55,221,237,7,39,6,110,203,14,252]) value030)=input040 := by rfl
#print axioms address040
def tree040 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [174,82,153,70,104,229,145,166,155,82,31,251,14,90,80,67,114,199,139,42,46,185,55,221,237,7,39,6,110,203,14,252])) tree030
theorem root040 : root JFp_SHADigest.digest tree040=value040 := by
  rw [tree040,root,root030]
  exact (congrArg JFp_SHADigest.digest address040).trans hash040
#print axioms root040
theorem shape040 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 65584=tree040 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 65584)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 3 65584 (by decide),siblings 3 (by decide) 65584 (by decide)]
  rw [shape030 f g inputs siblings]
  rfl
#print axioms shape040
def input041 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash041.message
def value041 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash041.result
theorem hash041 : JFp_SHADigest.digest input041=value041 := by
  have law := JHe_SHARealization.tree1 ⟨41, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash041
theorem address041 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [23,32,94,98,180,20,186,60,5,79,157,234,247,20,120,80,164,35,4,186,25,63,57,161,43,202,149,143,82,86,154,0]) value031)=input041 := by rfl
#print axioms address041
def tree041 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [23,32,94,98,180,20,186,60,5,79,157,234,247,20,120,80,164,35,4,186,25,63,57,161,43,202,149,143,82,86,154,0])) tree031
theorem root041 : root JFp_SHADigest.digest tree041=value041 := by
  rw [tree041,root,root031]
  exact (congrArg JFp_SHADigest.digest address041).trans hash041
#print axioms root041
theorem shape041 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 93488=tree041 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 93488)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 3 93488 (by decide),siblings 3 (by decide) 93488 (by decide)]
  rw [shape031 f g inputs siblings]
  rfl
#print axioms shape041
def input042 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash042.message
def value042 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash042.result
theorem hash042 : JFp_SHADigest.digest input042=value042 := by
  have law := JHe_SHARealization.tree1 ⟨42, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash042
theorem address042 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [97,191,57,149,64,167,60,139,155,101,25,14,192,173,197,217,46,87,102,56,173,54,159,44,53,128,93,203,89,224,12,166]) value032)=input042 := by rfl
#print axioms address042
def tree042 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [97,191,57,149,64,167,60,139,155,101,25,14,192,173,197,217,46,87,102,56,173,54,159,44,53,128,93,203,89,224,12,166])) tree032
theorem root042 : root JFp_SHADigest.digest tree042=value042 := by
  rw [tree042,root,root032]
  exact (congrArg JFp_SHADigest.digest address042).trans hash042
#print axioms root042
theorem shape042 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 147520=tree042 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 147520)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 3 147520 (by decide),siblings 3 (by decide) 147520 (by decide)]
  rw [shape032 f g inputs siblings]
  rfl
#print axioms shape042
def input043 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash043.message
def value043 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash043.result
theorem hash043 : JFp_SHADigest.digest input043=value043 := by
  have law := JHe_SHARealization.tree1 ⟨43, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash043
theorem address043 : BinMerkle32Path.nodeInput (children value033 (JGc_TX2_HashBytes.state [122,249,177,125,116,181,20,239,10,177,124,212,75,148,64,213,224,76,236,136,246,44,160,184,106,201,206,170,6,68,14,182]))=input043 := by rfl
#print axioms address043
def tree043 : Tree := .branch tree033 (.supplied (JGc_TX2_HashBytes.state [122,249,177,125,116,181,20,239,10,177,124,212,75,148,64,213,224,76,236,136,246,44,160,184,106,201,206,170,6,68,14,182]))
theorem root043 : root JFp_SHADigest.digest tree043=value043 := by
  rw [tree043,root,root033]
  exact (congrArg JFp_SHADigest.digest address043).trans hash043
#print axioms root043
theorem shape043 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 159808=tree043 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 159808)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape033 f g inputs siblings]
  rw [unoccupied f g 3 159816 (by decide),siblings 3 (by decide) 159816 (by decide)]
  rfl
#print axioms shape043
def input044 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash044.message
def value044 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash044.result
theorem hash044 : JFp_SHADigest.digest input044=value044 := by
  have law := JHe_SHARealization.tree1 ⟨44, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash044
theorem address044 : BinMerkle32Path.nodeInput (children value034 (JGc_TX2_HashBytes.state [151,184,78,84,65,195,103,88,59,72,98,75,137,155,138,234,245,102,144,251,199,25,120,222,103,12,202,216,89,102,142,47]))=input044 := by rfl
#print axioms address044
def tree044 : Tree := .branch tree034 (.supplied (JGc_TX2_HashBytes.state [151,184,78,84,65,195,103,88,59,72,98,75,137,155,138,234,245,102,144,251,199,25,120,222,103,12,202,216,89,102,142,47]))
theorem root044 : root JFp_SHADigest.digest tree044=value044 := by
  rw [tree044,root,root034]
  exact (congrArg JFp_SHADigest.digest address044).trans hash044
#print axioms root044
theorem shape044 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 183856=tree044 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 183856)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape034 f g inputs siblings]
  rw [unoccupied f g 3 183864 (by decide),siblings 3 (by decide) 183864 (by decide)]
  rfl
#print axioms shape044
def input045 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash045.message
def value045 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash045.result
theorem hash045 : JFp_SHADigest.digest input045=value045 := by
  have law := JHe_SHARealization.tree1 ⟨45, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash045
theorem address045 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [63,240,224,145,205,168,7,153,218,214,129,218,29,224,241,228,12,94,116,107,157,77,53,249,244,131,19,213,15,234,161,215]) value035)=input045 := by rfl
#print axioms address045
def tree045 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [63,240,224,145,205,168,7,153,218,214,129,218,29,224,241,228,12,94,116,107,157,77,53,249,244,131,19,213,15,234,161,215])) tree035
theorem root045 : root JFp_SHADigest.digest tree045=value045 := by
  rw [tree045,root,root035]
  exact (congrArg JFp_SHADigest.digest address045).trans hash045
#print axioms root045
theorem shape045 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 192304=tree045 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 192304)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 3 192304 (by decide),siblings 3 (by decide) 192304 (by decide)]
  rw [shape035 f g inputs siblings]
  rfl
#print axioms shape045
def input046 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash046.message
def value046 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash046.result
theorem hash046 : JFp_SHADigest.digest input046=value046 := by
  have law := JHe_SHARealization.tree1 ⟨46, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash046
theorem address046 : BinMerkle32Path.nodeInput (children value036 (JGc_TX2_HashBytes.state [110,105,159,26,42,122,142,230,234,101,199,61,78,103,131,23,40,10,245,45,225,245,34,241,143,52,113,160,22,153,128,20]))=input046 := by rfl
#print axioms address046
def tree046 : Tree := .branch tree036 (.supplied (JGc_TX2_HashBytes.state [110,105,159,26,42,122,142,230,234,101,199,61,78,103,131,23,40,10,245,45,225,245,34,241,143,52,113,160,22,153,128,20]))
theorem root046 : root JFp_SHADigest.digest tree046=value046 := by
  rw [tree046,root,root036]
  exact (congrArg JFp_SHADigest.digest address046).trans hash046
#print axioms root046
theorem shape046 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 193088=tree046 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 193088)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape036 f g inputs siblings]
  rw [unoccupied f g 3 193096 (by decide),siblings 3 (by decide) 193096 (by decide)]
  rfl
#print axioms shape046
def input047 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash047.message
def value047 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash047.result
theorem hash047 : JFp_SHADigest.digest input047=value047 := by
  have law := JHe_SHARealization.tree1 ⟨47, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash047
theorem address047 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [141,242,62,237,199,13,154,83,181,79,134,159,130,129,160,88,62,217,221,214,111,246,205,241,230,116,152,15,205,136,237,159]) value037)=input047 := by rfl
#print axioms address047
def tree047 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [141,242,62,237,199,13,154,83,181,79,134,159,130,129,160,88,62,217,221,214,111,246,205,241,230,116,152,15,205,136,237,159])) tree037
theorem root047 : root JFp_SHADigest.digest tree047=value047 := by
  rw [tree047,root,root037]
  exact (congrArg JFp_SHADigest.digest address047).trans hash047
#print axioms root047
theorem shape047 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 209360=tree047 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 209360)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 3 209360 (by decide),siblings 3 (by decide) 209360 (by decide)]
  rw [shape037 f g inputs siblings]
  rfl
#print axioms shape047
def input048 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash048.message
def value048 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash048.result
theorem hash048 : JFp_SHADigest.digest input048=value048 := by
  have law := JHe_SHARealization.tree1 ⟨48, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash048
theorem address048 : BinMerkle32Path.nodeInput (children value038 (JGc_TX2_HashBytes.state [21,213,50,124,193,142,144,15,46,81,226,121,245,18,87,145,167,20,102,64,173,9,142,30,0,196,36,27,63,68,81,237]))=input048 := by rfl
#print axioms address048
def tree048 : Tree := .branch tree038 (.supplied (JGc_TX2_HashBytes.state [21,213,50,124,193,142,144,15,46,81,226,121,245,18,87,145,167,20,102,64,173,9,142,30,0,196,36,27,63,68,81,237]))
theorem root048 : root JFp_SHADigest.digest tree048=value048 := by
  rw [tree048,root,root038]
  exact (congrArg JFp_SHADigest.digest address048).trans hash048
#print axioms root048
theorem shape048 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 216816=tree048 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 216816)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape038 f g inputs siblings]
  rw [unoccupied f g 3 216824 (by decide),siblings 3 (by decide) 216824 (by decide)]
  rfl
#print axioms shape048
def input049 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash049.message
def value049 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash049.result
theorem hash049 : JFp_SHADigest.digest input049=value049 := by
  have law := JHe_SHARealization.tree1 ⟨49, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash049
theorem address049 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [138,187,147,94,199,192,2,178,20,97,98,68,215,153,0,75,115,196,220,228,200,152,250,238,63,205,135,43,65,81,103,172]) value039)=input049 := by rfl
#print axioms address049
def tree049 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [138,187,147,94,199,192,2,178,20,97,98,68,215,153,0,75,115,196,220,228,200,152,250,238,63,205,135,43,65,81,103,172])) tree039
theorem root049 : root JFp_SHADigest.digest tree049=value049 := by
  rw [tree049,root,root039]
  exact (congrArg JFp_SHADigest.digest address049).trans hash049
#print axioms root049
theorem shape049 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 245888=tree049 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 245888)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 3 245888 (by decide),siblings 3 (by decide) 245888 (by decide)]
  rw [shape039 f g inputs siblings]
  rfl
#print axioms shape049
end AspisR1.JHh_C_Gr_M1Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_C_Gr_M1Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input050 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash050.message
def value050 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash050.result
theorem hash050 : JFp_SHADigest.digest input050=value050 := by
  have law := JHe_SHARealization.tree1 ⟨50, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash050
theorem address050 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [213,92,133,128,25,248,250,140,193,139,150,68,77,135,147,35,142,166,119,192,218,182,91,94,228,19,198,108,127,203,242,119]) value040)=input050 := by rfl
#print axioms address050
def tree050 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [213,92,133,128,25,248,250,140,193,139,150,68,77,135,147,35,142,166,119,192,218,182,91,94,228,19,198,108,127,203,242,119])) tree040
theorem root050 : root JFp_SHADigest.digest tree050=value050 := by
  rw [tree050,root,root040]
  exact (congrArg JFp_SHADigest.digest address050).trans hash050
#print axioms root050
theorem shape050 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 65568=tree050 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 65568)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 4 65568 (by decide),siblings 4 (by decide) 65568 (by decide)]
  rw [shape040 f g inputs siblings]
  rfl
#print axioms shape050
def input051 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash051.message
def value051 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash051.result
theorem hash051 : JFp_SHADigest.digest input051=value051 := by
  have law := JHe_SHARealization.tree1 ⟨51, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash051
theorem address051 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [81,239,149,218,159,11,224,172,201,3,32,69,184,120,186,14,167,232,10,19,198,22,40,223,87,252,148,18,167,205,157,165]) value041)=input051 := by rfl
#print axioms address051
def tree051 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [81,239,149,218,159,11,224,172,201,3,32,69,184,120,186,14,167,232,10,19,198,22,40,223,87,252,148,18,167,205,157,165])) tree041
theorem root051 : root JFp_SHADigest.digest tree051=value051 := by
  rw [tree051,root,root041]
  exact (congrArg JFp_SHADigest.digest address051).trans hash051
#print axioms root051
theorem shape051 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 93472=tree051 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 93472)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 4 93472 (by decide),siblings 4 (by decide) 93472 (by decide)]
  rw [shape041 f g inputs siblings]
  rfl
#print axioms shape051
def input052 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash052.message
def value052 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash052.result
theorem hash052 : JFp_SHADigest.digest input052=value052 := by
  have law := JHe_SHARealization.tree1 ⟨52, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash052
theorem address052 : BinMerkle32Path.nodeInput (children value042 (JGc_TX2_HashBytes.state [218,67,160,176,255,242,51,54,19,70,46,31,66,58,26,18,255,181,5,147,67,43,32,75,58,146,61,9,200,176,17,181]))=input052 := by rfl
#print axioms address052
def tree052 : Tree := .branch tree042 (.supplied (JGc_TX2_HashBytes.state [218,67,160,176,255,242,51,54,19,70,46,31,66,58,26,18,255,181,5,147,67,43,32,75,58,146,61,9,200,176,17,181]))
theorem root052 : root JFp_SHADigest.digest tree052=value052 := by
  rw [tree052,root,root042]
  exact (congrArg JFp_SHADigest.digest address052).trans hash052
#print axioms root052
theorem shape052 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 147520=tree052 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 147520)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape042 f g inputs siblings]
  rw [unoccupied f g 4 147536 (by decide),siblings 4 (by decide) 147536 (by decide)]
  rfl
#print axioms shape052
def input053 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash053.message
def value053 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash053.result
theorem hash053 : JFp_SHADigest.digest input053=value053 := by
  have law := JHe_SHARealization.tree1 ⟨53, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash053
theorem address053 : BinMerkle32Path.nodeInput (children value043 (JGc_TX2_HashBytes.state [9,203,140,76,138,254,212,190,225,220,48,2,142,250,78,110,12,43,32,145,129,4,58,215,255,244,201,225,98,43,227,177]))=input053 := by rfl
#print axioms address053
def tree053 : Tree := .branch tree043 (.supplied (JGc_TX2_HashBytes.state [9,203,140,76,138,254,212,190,225,220,48,2,142,250,78,110,12,43,32,145,129,4,58,215,255,244,201,225,98,43,227,177]))
theorem root053 : root JFp_SHADigest.digest tree053=value053 := by
  rw [tree053,root,root043]
  exact (congrArg JFp_SHADigest.digest address053).trans hash053
#print axioms root053
theorem shape053 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 159808=tree053 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 159808)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape043 f g inputs siblings]
  rw [unoccupied f g 4 159824 (by decide),siblings 4 (by decide) 159824 (by decide)]
  rfl
#print axioms shape053
def input054 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash054.message
def value054 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash054.result
theorem hash054 : JFp_SHADigest.digest input054=value054 := by
  have law := JHe_SHARealization.tree1 ⟨54, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash054
theorem address054 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [248,181,250,118,85,250,26,83,114,52,136,167,60,144,132,111,120,93,125,209,49,84,32,66,30,109,91,89,231,36,237,196]) value044)=input054 := by rfl
#print axioms address054
def tree054 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [248,181,250,118,85,250,26,83,114,52,136,167,60,144,132,111,120,93,125,209,49,84,32,66,30,109,91,89,231,36,237,196])) tree044
theorem root054 : root JFp_SHADigest.digest tree054=value054 := by
  rw [tree054,root,root044]
  exact (congrArg JFp_SHADigest.digest address054).trans hash054
#print axioms root054
theorem shape054 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 183840=tree054 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 183840)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 4 183840 (by decide),siblings 4 (by decide) 183840 (by decide)]
  rw [shape044 f g inputs siblings]
  rfl
#print axioms shape054
def input055 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash055.message
def value055 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash055.result
theorem hash055 : JFp_SHADigest.digest input055=value055 := by
  have law := JHe_SHARealization.tree1 ⟨55, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash055
theorem address055 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [108,16,198,203,67,17,242,189,102,34,209,177,45,76,232,181,18,166,239,4,35,21,239,246,220,237,115,171,194,70,204,157]) value045)=input055 := by rfl
#print axioms address055
def tree055 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [108,16,198,203,67,17,242,189,102,34,209,177,45,76,232,181,18,166,239,4,35,21,239,246,220,237,115,171,194,70,204,157])) tree045
theorem root055 : root JFp_SHADigest.digest tree055=value055 := by
  rw [tree055,root,root045]
  exact (congrArg JFp_SHADigest.digest address055).trans hash055
#print axioms root055
theorem shape055 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 192288=tree055 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 192288)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 4 192288 (by decide),siblings 4 (by decide) 192288 (by decide)]
  rw [shape045 f g inputs siblings]
  rfl
#print axioms shape055
def input056 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash056.message
def value056 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash056.result
theorem hash056 : JFp_SHADigest.digest input056=value056 := by
  have law := JHe_SHARealization.tree1 ⟨56, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash056
theorem address056 : BinMerkle32Path.nodeInput (children value046 (JGc_TX2_HashBytes.state [197,43,157,201,30,225,68,160,229,190,201,182,162,53,115,97,51,234,182,243,73,166,223,190,116,177,25,188,182,144,219,200]))=input056 := by rfl
#print axioms address056
def tree056 : Tree := .branch tree046 (.supplied (JGc_TX2_HashBytes.state [197,43,157,201,30,225,68,160,229,190,201,182,162,53,115,97,51,234,182,243,73,166,223,190,116,177,25,188,182,144,219,200]))
theorem root056 : root JFp_SHADigest.digest tree056=value056 := by
  rw [tree056,root,root046]
  exact (congrArg JFp_SHADigest.digest address056).trans hash056
#print axioms root056
theorem shape056 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 193088=tree056 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 193088)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape046 f g inputs siblings]
  rw [unoccupied f g 4 193104 (by decide),siblings 4 (by decide) 193104 (by decide)]
  rfl
#print axioms shape056
def input057 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash057.message
def value057 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash057.result
theorem hash057 : JFp_SHADigest.digest input057=value057 := by
  have law := JHe_SHARealization.tree1 ⟨57, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash057
theorem address057 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [48,186,118,148,69,61,104,226,93,243,172,141,168,144,124,254,57,139,1,55,108,253,152,33,72,126,89,125,30,154,10,32]) value047)=input057 := by rfl
#print axioms address057
def tree057 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [48,186,118,148,69,61,104,226,93,243,172,141,168,144,124,254,57,139,1,55,108,253,152,33,72,126,89,125,30,154,10,32])) tree047
theorem root057 : root JFp_SHADigest.digest tree057=value057 := by
  rw [tree057,root,root047]
  exact (congrArg JFp_SHADigest.digest address057).trans hash057
#print axioms root057
theorem shape057 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 209344=tree057 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 209344)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 4 209344 (by decide),siblings 4 (by decide) 209344 (by decide)]
  rw [shape047 f g inputs siblings]
  rfl
#print axioms shape057
def input058 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash058.message
def value058 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash058.result
theorem hash058 : JFp_SHADigest.digest input058=value058 := by
  have law := JHe_SHARealization.tree1 ⟨58, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash058
theorem address058 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [90,249,230,45,98,111,180,129,153,122,162,170,204,61,76,254,140,54,104,181,250,67,86,138,44,28,90,64,159,9,181,47]) value048)=input058 := by rfl
#print axioms address058
def tree058 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [90,249,230,45,98,111,180,129,153,122,162,170,204,61,76,254,140,54,104,181,250,67,86,138,44,28,90,64,159,9,181,47])) tree048
theorem root058 : root JFp_SHADigest.digest tree058=value058 := by
  rw [tree058,root,root048]
  exact (congrArg JFp_SHADigest.digest address058).trans hash058
#print axioms root058
theorem shape058 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 216800=tree058 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 216800)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 4 216800 (by decide),siblings 4 (by decide) 216800 (by decide)]
  rw [shape048 f g inputs siblings]
  rfl
#print axioms shape058
def input059 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash059.message
def value059 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash059.result
theorem hash059 : JFp_SHADigest.digest input059=value059 := by
  have law := JHe_SHARealization.tree1 ⟨59, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash059
theorem address059 : BinMerkle32Path.nodeInput (children value049 (JGc_TX2_HashBytes.state [195,3,176,84,58,232,36,247,102,253,61,165,20,60,158,89,150,160,29,234,75,87,244,134,24,74,65,119,252,101,75,15]))=input059 := by rfl
#print axioms address059
def tree059 : Tree := .branch tree049 (.supplied (JGc_TX2_HashBytes.state [195,3,176,84,58,232,36,247,102,253,61,165,20,60,158,89,150,160,29,234,75,87,244,134,24,74,65,119,252,101,75,15]))
theorem root059 : root JFp_SHADigest.digest tree059=value059 := by
  rw [tree059,root,root049]
  exact (congrArg JFp_SHADigest.digest address059).trans hash059
#print axioms root059
theorem shape059 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 245888=tree059 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 245888)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape049 f g inputs siblings]
  rw [unoccupied f g 4 245904 (by decide),siblings 4 (by decide) 245904 (by decide)]
  rfl
#print axioms shape059
end AspisR1.JHh_C_Gr_M1Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_C_Gr_M1Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input060 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash060.message
def value060 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash060.result
theorem hash060 : JFp_SHADigest.digest input060=value060 := by
  have law := JHe_SHARealization.tree1 ⟨60, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash060
theorem address060 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [184,43,54,143,158,199,175,42,61,237,16,117,244,181,159,43,88,80,126,207,12,253,148,152,128,201,187,77,167,76,234,131]) value050)=input060 := by rfl
#print axioms address060
def tree060 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [184,43,54,143,158,199,175,42,61,237,16,117,244,181,159,43,88,80,126,207,12,253,148,152,128,201,187,77,167,76,234,131])) tree050
theorem root060 : root JFp_SHADigest.digest tree060=value060 := by
  rw [tree060,root,root050]
  exact (congrArg JFp_SHADigest.digest address060).trans hash060
#print axioms root060
theorem shape060 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 65536=tree060 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 65536)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 5 65536 (by decide),siblings 5 (by decide) 65536 (by decide)]
  rw [shape050 f g inputs siblings]
  rfl
#print axioms shape060
def input061 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash061.message
def value061 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash061.result
theorem hash061 : JFp_SHADigest.digest input061=value061 := by
  have law := JHe_SHARealization.tree1 ⟨61, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash061
theorem address061 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [9,59,145,89,120,54,222,74,203,219,27,53,98,237,178,181,58,227,170,3,52,21,253,207,237,232,171,52,49,52,153,1]) value051)=input061 := by rfl
#print axioms address061
def tree061 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [9,59,145,89,120,54,222,74,203,219,27,53,98,237,178,181,58,227,170,3,52,21,253,207,237,232,171,52,49,52,153,1])) tree051
theorem root061 : root JFp_SHADigest.digest tree061=value061 := by
  rw [tree061,root,root051]
  exact (congrArg JFp_SHADigest.digest address061).trans hash061
#print axioms root061
theorem shape061 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 93440=tree061 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 93440)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 5 93440 (by decide),siblings 5 (by decide) 93440 (by decide)]
  rw [shape051 f g inputs siblings]
  rfl
#print axioms shape061
def input062 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash062.message
def value062 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash062.result
theorem hash062 : JFp_SHADigest.digest input062=value062 := by
  have law := JHe_SHARealization.tree1 ⟨62, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash062
theorem address062 : BinMerkle32Path.nodeInput (children value052 (JGc_TX2_HashBytes.state [200,112,24,187,168,226,133,51,134,133,85,253,45,154,56,190,126,26,87,40,238,99,195,189,69,70,211,132,89,221,161,18]))=input062 := by rfl
#print axioms address062
def tree062 : Tree := .branch tree052 (.supplied (JGc_TX2_HashBytes.state [200,112,24,187,168,226,133,51,134,133,85,253,45,154,56,190,126,26,87,40,238,99,195,189,69,70,211,132,89,221,161,18]))
theorem root062 : root JFp_SHADigest.digest tree062=value062 := by
  rw [tree062,root,root052]
  exact (congrArg JFp_SHADigest.digest address062).trans hash062
#print axioms root062
theorem shape062 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 147520=tree062 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 147520)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape052 f g inputs siblings]
  rw [unoccupied f g 5 147552 (by decide),siblings 5 (by decide) 147552 (by decide)]
  rfl
#print axioms shape062
def input063 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash063.message
def value063 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash063.result
theorem hash063 : JFp_SHADigest.digest input063=value063 := by
  have law := JHe_SHARealization.tree1 ⟨63, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash063
theorem address063 : BinMerkle32Path.nodeInput (children value053 (JGc_TX2_HashBytes.state [254,17,1,69,169,101,14,124,152,58,198,80,91,197,7,201,23,89,197,83,121,49,187,33,254,195,218,154,226,70,10,132]))=input063 := by rfl
#print axioms address063
def tree063 : Tree := .branch tree053 (.supplied (JGc_TX2_HashBytes.state [254,17,1,69,169,101,14,124,152,58,198,80,91,197,7,201,23,89,197,83,121,49,187,33,254,195,218,154,226,70,10,132]))
theorem root063 : root JFp_SHADigest.digest tree063=value063 := by
  rw [tree063,root,root053]
  exact (congrArg JFp_SHADigest.digest address063).trans hash063
#print axioms root063
theorem shape063 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 159808=tree063 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 159808)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape053 f g inputs siblings]
  rw [unoccupied f g 5 159840 (by decide),siblings 5 (by decide) 159840 (by decide)]
  rfl
#print axioms shape063
def input064 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash064.message
def value064 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash064.result
theorem hash064 : JFp_SHADigest.digest input064=value064 := by
  have law := JHe_SHARealization.tree1 ⟨64, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash064
theorem address064 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [192,195,33,171,153,176,59,52,97,96,104,8,183,204,159,49,248,227,95,225,72,109,83,158,159,13,184,26,137,190,18,0]) value054)=input064 := by rfl
#print axioms address064
def tree064 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [192,195,33,171,153,176,59,52,97,96,104,8,183,204,159,49,248,227,95,225,72,109,83,158,159,13,184,26,137,190,18,0])) tree054
theorem root064 : root JFp_SHADigest.digest tree064=value064 := by
  rw [tree064,root,root054]
  exact (congrArg JFp_SHADigest.digest address064).trans hash064
#print axioms root064
theorem shape064 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 183808=tree064 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 183808)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 5 183808 (by decide),siblings 5 (by decide) 183808 (by decide)]
  rw [shape054 f g inputs siblings]
  rfl
#print axioms shape064
def input065 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash065.message
def value065 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash065.result
theorem hash065 : JFp_SHADigest.digest input065=value065 := by
  have law := JHe_SHARealization.tree1 ⟨65, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash065
theorem address065 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [254,206,208,23,213,50,19,160,84,122,149,199,15,73,40,119,253,111,116,175,203,205,102,52,143,81,145,192,139,46,139,68]) value055)=input065 := by rfl
#print axioms address065
def tree065 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [254,206,208,23,213,50,19,160,84,122,149,199,15,73,40,119,253,111,116,175,203,205,102,52,143,81,145,192,139,46,139,68])) tree055
theorem root065 : root JFp_SHADigest.digest tree065=value065 := by
  rw [tree065,root,root055]
  exact (congrArg JFp_SHADigest.digest address065).trans hash065
#print axioms root065
theorem shape065 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 192256=tree065 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 192256)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 5 192256 (by decide),siblings 5 (by decide) 192256 (by decide)]
  rw [shape055 f g inputs siblings]
  rfl
#print axioms shape065
def input066 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash066.message
def value066 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash066.result
theorem hash066 : JFp_SHADigest.digest input066=value066 := by
  have law := JHe_SHARealization.tree1 ⟨66, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash066
theorem address066 : BinMerkle32Path.nodeInput (children value056 (JGc_TX2_HashBytes.state [135,62,37,121,200,109,211,136,88,24,191,195,231,222,98,12,91,201,86,188,190,61,185,78,66,155,223,88,157,220,23,249]))=input066 := by rfl
#print axioms address066
def tree066 : Tree := .branch tree056 (.supplied (JGc_TX2_HashBytes.state [135,62,37,121,200,109,211,136,88,24,191,195,231,222,98,12,91,201,86,188,190,61,185,78,66,155,223,88,157,220,23,249]))
theorem root066 : root JFp_SHADigest.digest tree066=value066 := by
  rw [tree066,root,root056]
  exact (congrArg JFp_SHADigest.digest address066).trans hash066
#print axioms root066
theorem shape066 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 193088=tree066 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 193088)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape056 f g inputs siblings]
  rw [unoccupied f g 5 193120 (by decide),siblings 5 (by decide) 193120 (by decide)]
  rfl
#print axioms shape066
def input067 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash067.message
def value067 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash067.result
theorem hash067 : JFp_SHADigest.digest input067=value067 := by
  have law := JHe_SHARealization.tree1 ⟨67, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash067
theorem address067 : BinMerkle32Path.nodeInput (children value057 (JGc_TX2_HashBytes.state [195,20,209,28,33,12,185,7,114,250,208,29,236,188,0,141,106,128,113,110,159,175,180,255,243,33,223,145,197,31,0,147]))=input067 := by rfl
#print axioms address067
def tree067 : Tree := .branch tree057 (.supplied (JGc_TX2_HashBytes.state [195,20,209,28,33,12,185,7,114,250,208,29,236,188,0,141,106,128,113,110,159,175,180,255,243,33,223,145,197,31,0,147]))
theorem root067 : root JFp_SHADigest.digest tree067=value067 := by
  rw [tree067,root,root057]
  exact (congrArg JFp_SHADigest.digest address067).trans hash067
#print axioms root067
theorem shape067 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 209344=tree067 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 209344)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape057 f g inputs siblings]
  rw [unoccupied f g 5 209376 (by decide),siblings 5 (by decide) 209376 (by decide)]
  rfl
#print axioms shape067
def input068 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash068.message
def value068 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash068.result
theorem hash068 : JFp_SHADigest.digest input068=value068 := by
  have law := JHe_SHARealization.tree1 ⟨68, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash068
theorem address068 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [98,166,20,210,130,207,194,139,78,117,173,133,188,147,155,169,220,81,13,244,134,242,185,223,105,47,40,3,97,149,255,241]) value058)=input068 := by rfl
#print axioms address068
def tree068 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [98,166,20,210,130,207,194,139,78,117,173,133,188,147,155,169,220,81,13,244,134,242,185,223,105,47,40,3,97,149,255,241])) tree058
theorem root068 : root JFp_SHADigest.digest tree068=value068 := by
  rw [tree068,root,root058]
  exact (congrArg JFp_SHADigest.digest address068).trans hash068
#print axioms root068
theorem shape068 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 216768=tree068 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 216768)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 5 216768 (by decide),siblings 5 (by decide) 216768 (by decide)]
  rw [shape058 f g inputs siblings]
  rfl
#print axioms shape068
def input069 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash069.message
def value069 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash069.result
theorem hash069 : JFp_SHADigest.digest input069=value069 := by
  have law := JHe_SHARealization.tree1 ⟨69, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash069
theorem address069 : BinMerkle32Path.nodeInput (children value059 (JGc_TX2_HashBytes.state [25,110,119,90,229,115,9,14,1,136,89,142,123,146,66,240,29,42,225,45,227,245,237,143,246,109,141,79,34,148,184,86]))=input069 := by rfl
#print axioms address069
def tree069 : Tree := .branch tree059 (.supplied (JGc_TX2_HashBytes.state [25,110,119,90,229,115,9,14,1,136,89,142,123,146,66,240,29,42,225,45,227,245,237,143,246,109,141,79,34,148,184,86]))
theorem root069 : root JFp_SHADigest.digest tree069=value069 := by
  rw [tree069,root,root059]
  exact (congrArg JFp_SHADigest.digest address069).trans hash069
#print axioms root069
theorem shape069 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 245888=tree069 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 245888)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape059 f g inputs siblings]
  rw [unoccupied f g 5 245920 (by decide),siblings 5 (by decide) 245920 (by decide)]
  rfl
#print axioms shape069
end AspisR1.JHh_C_Gr_M1Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_C_Gr_M1Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input070 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash070.message
def value070 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash070.result
theorem hash070 : JFp_SHADigest.digest input070=value070 := by
  have law := JHe_SHARealization.tree1 ⟨70, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash070
theorem address070 : BinMerkle32Path.nodeInput (children value060 (JGc_TX2_HashBytes.state [213,219,66,149,132,102,202,223,2,186,92,70,102,98,174,29,190,20,146,248,36,151,27,124,170,129,132,58,230,86,6,226]))=input070 := by rfl
#print axioms address070
def tree070 : Tree := .branch tree060 (.supplied (JGc_TX2_HashBytes.state [213,219,66,149,132,102,202,223,2,186,92,70,102,98,174,29,190,20,146,248,36,151,27,124,170,129,132,58,230,86,6,226]))
theorem root070 : root JFp_SHADigest.digest tree070=value070 := by
  rw [tree070,root,root060]
  exact (congrArg JFp_SHADigest.digest address070).trans hash070
#print axioms root070
theorem shape070 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 65536=tree070 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 65536)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape060 f g inputs siblings]
  rw [unoccupied f g 6 65600 (by decide),siblings 6 (by decide) 65600 (by decide)]
  rfl
#print axioms shape070
def input071 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash071.message
def value071 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash071.result
theorem hash071 : JFp_SHADigest.digest input071=value071 := by
  have law := JHe_SHARealization.tree1 ⟨71, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash071
theorem address071 : BinMerkle32Path.nodeInput (children value061 (JGc_TX2_HashBytes.state [43,41,156,176,42,40,47,242,5,243,149,73,246,84,151,201,214,4,0,213,156,115,60,243,26,35,74,120,199,7,124,249]))=input071 := by rfl
#print axioms address071
def tree071 : Tree := .branch tree061 (.supplied (JGc_TX2_HashBytes.state [43,41,156,176,42,40,47,242,5,243,149,73,246,84,151,201,214,4,0,213,156,115,60,243,26,35,74,120,199,7,124,249]))
theorem root071 : root JFp_SHADigest.digest tree071=value071 := by
  rw [tree071,root,root061]
  exact (congrArg JFp_SHADigest.digest address071).trans hash071
#print axioms root071
theorem shape071 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 93440=tree071 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 93440)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape061 f g inputs siblings]
  rw [unoccupied f g 6 93504 (by decide),siblings 6 (by decide) 93504 (by decide)]
  rfl
#print axioms shape071
def input072 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash072.message
def value072 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash072.result
theorem hash072 : JFp_SHADigest.digest input072=value072 := by
  have law := JHe_SHARealization.tree1 ⟨72, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash072
theorem address072 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [166,169,50,209,188,5,52,23,33,230,174,188,64,116,191,107,219,82,103,128,10,79,137,212,138,189,23,60,71,204,95,45]) value062)=input072 := by rfl
#print axioms address072
def tree072 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [166,169,50,209,188,5,52,23,33,230,174,188,64,116,191,107,219,82,103,128,10,79,137,212,138,189,23,60,71,204,95,45])) tree062
theorem root072 : root JFp_SHADigest.digest tree072=value072 := by
  rw [tree072,root,root062]
  exact (congrArg JFp_SHADigest.digest address072).trans hash072
#print axioms root072
theorem shape072 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 147456=tree072 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 147456)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 6 147456 (by decide),siblings 6 (by decide) 147456 (by decide)]
  rw [shape062 f g inputs siblings]
  rfl
#print axioms shape072
def input073 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash073.message
def value073 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash073.result
theorem hash073 : JFp_SHADigest.digest input073=value073 := by
  have law := JHe_SHARealization.tree1 ⟨73, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash073
theorem address073 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [26,45,196,149,156,185,207,108,35,63,83,156,140,215,142,227,222,78,13,88,119,76,111,150,75,170,136,157,17,249,95,75]) value063)=input073 := by rfl
#print axioms address073
def tree073 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [26,45,196,149,156,185,207,108,35,63,83,156,140,215,142,227,222,78,13,88,119,76,111,150,75,170,136,157,17,249,95,75])) tree063
theorem root073 : root JFp_SHADigest.digest tree073=value073 := by
  rw [tree073,root,root063]
  exact (congrArg JFp_SHADigest.digest address073).trans hash073
#print axioms root073
theorem shape073 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 159744=tree073 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 159744)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 6 159744 (by decide),siblings 6 (by decide) 159744 (by decide)]
  rw [shape063 f g inputs siblings]
  rfl
#print axioms shape073
def input074 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash074.message
def value074 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash074.result
theorem hash074 : JFp_SHADigest.digest input074=value074 := by
  have law := JHe_SHARealization.tree1 ⟨74, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash074
theorem address074 : BinMerkle32Path.nodeInput (children value064 (JGc_TX2_HashBytes.state [187,168,249,177,7,164,3,149,98,161,102,174,50,138,206,11,30,72,150,177,137,51,106,119,176,70,87,242,152,194,189,85]))=input074 := by rfl
#print axioms address074
def tree074 : Tree := .branch tree064 (.supplied (JGc_TX2_HashBytes.state [187,168,249,177,7,164,3,149,98,161,102,174,50,138,206,11,30,72,150,177,137,51,106,119,176,70,87,242,152,194,189,85]))
theorem root074 : root JFp_SHADigest.digest tree074=value074 := by
  rw [tree074,root,root064]
  exact (congrArg JFp_SHADigest.digest address074).trans hash074
#print axioms root074
theorem shape074 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 183808=tree074 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 183808)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape064 f g inputs siblings]
  rw [unoccupied f g 6 183872 (by decide),siblings 6 (by decide) 183872 (by decide)]
  rfl
#print axioms shape074
def input075 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash075.message
def value075 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash075.result
theorem hash075 : JFp_SHADigest.digest input075=value075 := by
  have law := JHe_SHARealization.tree1 ⟨75, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash075
theorem address075 : BinMerkle32Path.nodeInput (children value065 (JGc_TX2_HashBytes.state [73,221,130,144,71,67,136,79,167,63,161,205,39,10,20,47,38,23,24,180,153,220,23,255,9,108,57,158,87,153,49,94]))=input075 := by rfl
#print axioms address075
def tree075 : Tree := .branch tree065 (.supplied (JGc_TX2_HashBytes.state [73,221,130,144,71,67,136,79,167,63,161,205,39,10,20,47,38,23,24,180,153,220,23,255,9,108,57,158,87,153,49,94]))
theorem root075 : root JFp_SHADigest.digest tree075=value075 := by
  rw [tree075,root,root065]
  exact (congrArg JFp_SHADigest.digest address075).trans hash075
#print axioms root075
theorem shape075 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 192256=tree075 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 192256)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape065 f g inputs siblings]
  rw [unoccupied f g 6 192320 (by decide),siblings 6 (by decide) 192320 (by decide)]
  rfl
#print axioms shape075
def input076 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash076.message
def value076 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash076.result
theorem hash076 : JFp_SHADigest.digest input076=value076 := by
  have law := JHe_SHARealization.tree1 ⟨76, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash076
theorem address076 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [167,255,250,78,90,35,106,202,120,194,253,220,221,11,157,53,242,35,22,107,23,89,62,195,225,140,7,190,221,244,119,208]) value066)=input076 := by rfl
#print axioms address076
def tree076 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [167,255,250,78,90,35,106,202,120,194,253,220,221,11,157,53,242,35,22,107,23,89,62,195,225,140,7,190,221,244,119,208])) tree066
theorem root076 : root JFp_SHADigest.digest tree076=value076 := by
  rw [tree076,root,root066]
  exact (congrArg JFp_SHADigest.digest address076).trans hash076
#print axioms root076
theorem shape076 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 193024=tree076 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 193024)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 6 193024 (by decide),siblings 6 (by decide) 193024 (by decide)]
  rw [shape066 f g inputs siblings]
  rfl
#print axioms shape076
def input077 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash077.message
def value077 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash077.result
theorem hash077 : JFp_SHADigest.digest input077=value077 := by
  have law := JHe_SHARealization.tree1 ⟨77, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash077
theorem address077 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [214,112,195,229,164,168,187,90,35,77,255,198,103,221,16,135,157,106,196,94,83,69,143,19,82,171,67,25,74,114,34,81]) value067)=input077 := by rfl
#print axioms address077
def tree077 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [214,112,195,229,164,168,187,90,35,77,255,198,103,221,16,135,157,106,196,94,83,69,143,19,82,171,67,25,74,114,34,81])) tree067
theorem root077 : root JFp_SHADigest.digest tree077=value077 := by
  rw [tree077,root,root067]
  exact (congrArg JFp_SHADigest.digest address077).trans hash077
#print axioms root077
theorem shape077 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 209280=tree077 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 209280)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 6 209280 (by decide),siblings 6 (by decide) 209280 (by decide)]
  rw [shape067 f g inputs siblings]
  rfl
#print axioms shape077
def input078 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash078.message
def value078 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash078.result
theorem hash078 : JFp_SHADigest.digest input078=value078 := by
  have law := JHe_SHARealization.tree1 ⟨78, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash078
theorem address078 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [99,164,177,65,229,155,166,198,59,58,144,40,119,57,191,57,32,230,224,109,132,52,196,152,102,228,8,147,143,111,177,238]) value068)=input078 := by rfl
#print axioms address078
def tree078 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [99,164,177,65,229,155,166,198,59,58,144,40,119,57,191,57,32,230,224,109,132,52,196,152,102,228,8,147,143,111,177,238])) tree068
theorem root078 : root JFp_SHADigest.digest tree078=value078 := by
  rw [tree078,root,root068]
  exact (congrArg JFp_SHADigest.digest address078).trans hash078
#print axioms root078
theorem shape078 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 216704=tree078 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 216704)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 6 216704 (by decide),siblings 6 (by decide) 216704 (by decide)]
  rw [shape068 f g inputs siblings]
  rfl
#print axioms shape078
def input079 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash079.message
def value079 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash079.result
theorem hash079 : JFp_SHADigest.digest input079=value079 := by
  have law := JHe_SHARealization.tree1 ⟨79, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash079
theorem address079 : BinMerkle32Path.nodeInput (children value069 (JGc_TX2_HashBytes.state [206,137,116,72,150,225,247,109,190,174,193,175,97,74,39,239,82,242,9,20,245,218,106,203,31,54,175,142,188,88,174,158]))=input079 := by rfl
#print axioms address079
def tree079 : Tree := .branch tree069 (.supplied (JGc_TX2_HashBytes.state [206,137,116,72,150,225,247,109,190,174,193,175,97,74,39,239,82,242,9,20,245,218,106,203,31,54,175,142,188,88,174,158]))
theorem root079 : root JFp_SHADigest.digest tree079=value079 := by
  rw [tree079,root,root069]
  exact (congrArg JFp_SHADigest.digest address079).trans hash079
#print axioms root079
theorem shape079 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 245888=tree079 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 245888)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape069 f g inputs siblings]
  rw [unoccupied f g 6 245952 (by decide),siblings 6 (by decide) 245952 (by decide)]
  rfl
#print axioms shape079
end AspisR1.JHh_C_Gr_M1Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_C_Gr_M1Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input080 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash080.message
def value080 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash080.result
theorem hash080 : JFp_SHADigest.digest input080=value080 := by
  have law := JHe_SHARealization.tree1 ⟨80, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash080
theorem address080 : BinMerkle32Path.nodeInput (children value070 (JGc_TX2_HashBytes.state [86,144,167,147,188,24,122,130,134,42,53,1,191,205,208,232,136,53,92,205,132,56,195,95,102,211,36,136,20,102,109,234]))=input080 := by rfl
#print axioms address080
def tree080 : Tree := .branch tree070 (.supplied (JGc_TX2_HashBytes.state [86,144,167,147,188,24,122,130,134,42,53,1,191,205,208,232,136,53,92,205,132,56,195,95,102,211,36,136,20,102,109,234]))
theorem root080 : root JFp_SHADigest.digest tree080=value080 := by
  rw [tree080,root,root070]
  exact (congrArg JFp_SHADigest.digest address080).trans hash080
#print axioms root080
theorem shape080 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 65536=tree080 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 65536)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape070 f g inputs siblings]
  rw [unoccupied f g 7 65664 (by decide),siblings 7 (by decide) 65664 (by decide)]
  rfl
#print axioms shape080
def input081 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash081.message
def value081 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash081.result
theorem hash081 : JFp_SHADigest.digest input081=value081 := by
  have law := JHe_SHARealization.tree1 ⟨81, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash081
theorem address081 : BinMerkle32Path.nodeInput (children value071 (JGc_TX2_HashBytes.state [129,134,159,111,208,119,101,44,121,214,241,176,100,83,224,186,157,157,52,15,168,151,4,234,77,57,92,217,53,20,243,178]))=input081 := by rfl
#print axioms address081
def tree081 : Tree := .branch tree071 (.supplied (JGc_TX2_HashBytes.state [129,134,159,111,208,119,101,44,121,214,241,176,100,83,224,186,157,157,52,15,168,151,4,234,77,57,92,217,53,20,243,178]))
theorem root081 : root JFp_SHADigest.digest tree081=value081 := by
  rw [tree081,root,root071]
  exact (congrArg JFp_SHADigest.digest address081).trans hash081
#print axioms root081
theorem shape081 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 93440=tree081 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 93440)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape071 f g inputs siblings]
  rw [unoccupied f g 7 93568 (by decide),siblings 7 (by decide) 93568 (by decide)]
  rfl
#print axioms shape081
def input082 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash082.message
def value082 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash082.result
theorem hash082 : JFp_SHADigest.digest input082=value082 := by
  have law := JHe_SHARealization.tree1 ⟨82, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash082
theorem address082 : BinMerkle32Path.nodeInput (children value072 (JGc_TX2_HashBytes.state [229,14,215,228,251,27,121,138,26,111,165,216,200,216,201,136,85,212,71,42,31,194,225,192,175,105,184,67,0,188,222,153]))=input082 := by rfl
#print axioms address082
def tree082 : Tree := .branch tree072 (.supplied (JGc_TX2_HashBytes.state [229,14,215,228,251,27,121,138,26,111,165,216,200,216,201,136,85,212,71,42,31,194,225,192,175,105,184,67,0,188,222,153]))
theorem root082 : root JFp_SHADigest.digest tree082=value082 := by
  rw [tree082,root,root072]
  exact (congrArg JFp_SHADigest.digest address082).trans hash082
#print axioms root082
theorem shape082 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 147456=tree082 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 147456)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape072 f g inputs siblings]
  rw [unoccupied f g 7 147584 (by decide),siblings 7 (by decide) 147584 (by decide)]
  rfl
#print axioms shape082
def input083 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash083.message
def value083 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash083.result
theorem hash083 : JFp_SHADigest.digest input083=value083 := by
  have law := JHe_SHARealization.tree1 ⟨83, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash083
theorem address083 : BinMerkle32Path.nodeInput (children value073 (JGc_TX2_HashBytes.state [46,123,57,164,118,22,77,38,72,105,83,9,179,113,17,42,45,247,143,151,243,173,174,143,222,205,203,31,224,130,255,177]))=input083 := by rfl
#print axioms address083
def tree083 : Tree := .branch tree073 (.supplied (JGc_TX2_HashBytes.state [46,123,57,164,118,22,77,38,72,105,83,9,179,113,17,42,45,247,143,151,243,173,174,143,222,205,203,31,224,130,255,177]))
theorem root083 : root JFp_SHADigest.digest tree083=value083 := by
  rw [tree083,root,root073]
  exact (congrArg JFp_SHADigest.digest address083).trans hash083
#print axioms root083
theorem shape083 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 159744=tree083 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 159744)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape073 f g inputs siblings]
  rw [unoccupied f g 7 159872 (by decide),siblings 7 (by decide) 159872 (by decide)]
  rfl
#print axioms shape083
def input084 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash084.message
def value084 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash084.result
theorem hash084 : JFp_SHADigest.digest input084=value084 := by
  have law := JHe_SHARealization.tree1 ⟨84, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash084
theorem address084 : BinMerkle32Path.nodeInput (children value074 (JGc_TX2_HashBytes.state [20,207,22,9,174,31,23,223,78,200,11,111,211,240,97,165,212,117,32,89,62,177,230,187,171,248,29,209,77,89,205,216]))=input084 := by rfl
#print axioms address084
def tree084 : Tree := .branch tree074 (.supplied (JGc_TX2_HashBytes.state [20,207,22,9,174,31,23,223,78,200,11,111,211,240,97,165,212,117,32,89,62,177,230,187,171,248,29,209,77,89,205,216]))
theorem root084 : root JFp_SHADigest.digest tree084=value084 := by
  rw [tree084,root,root074]
  exact (congrArg JFp_SHADigest.digest address084).trans hash084
#print axioms root084
theorem shape084 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 183808=tree084 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 183808)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape074 f g inputs siblings]
  rw [unoccupied f g 7 183936 (by decide),siblings 7 (by decide) 183936 (by decide)]
  rfl
#print axioms shape084
def input085 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash085.message
def value085 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash085.result
theorem hash085 : JFp_SHADigest.digest input085=value085 := by
  have law := JHe_SHARealization.tree1 ⟨85, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash085
theorem address085 : BinMerkle32Path.nodeInput (children value075 (JGc_TX2_HashBytes.state [152,7,48,143,226,24,235,182,175,169,50,91,216,225,126,157,236,234,179,168,64,123,15,245,94,142,196,215,212,12,175,250]))=input085 := by rfl
#print axioms address085
def tree085 : Tree := .branch tree075 (.supplied (JGc_TX2_HashBytes.state [152,7,48,143,226,24,235,182,175,169,50,91,216,225,126,157,236,234,179,168,64,123,15,245,94,142,196,215,212,12,175,250]))
theorem root085 : root JFp_SHADigest.digest tree085=value085 := by
  rw [tree085,root,root075]
  exact (congrArg JFp_SHADigest.digest address085).trans hash085
#print axioms root085
theorem shape085 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 192256=tree085 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 192256)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape075 f g inputs siblings]
  rw [unoccupied f g 7 192384 (by decide),siblings 7 (by decide) 192384 (by decide)]
  rfl
#print axioms shape085
def input086 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash086.message
def value086 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash086.result
theorem hash086 : JFp_SHADigest.digest input086=value086 := by
  have law := JHe_SHARealization.tree1 ⟨86, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash086
theorem address086 : BinMerkle32Path.nodeInput (children value076 (JGc_TX2_HashBytes.state [152,67,185,114,180,230,228,197,92,49,68,3,243,160,35,107,236,112,86,221,8,66,205,238,116,218,35,5,165,164,99,104]))=input086 := by rfl
#print axioms address086
def tree086 : Tree := .branch tree076 (.supplied (JGc_TX2_HashBytes.state [152,67,185,114,180,230,228,197,92,49,68,3,243,160,35,107,236,112,86,221,8,66,205,238,116,218,35,5,165,164,99,104]))
theorem root086 : root JFp_SHADigest.digest tree086=value086 := by
  rw [tree086,root,root076]
  exact (congrArg JFp_SHADigest.digest address086).trans hash086
#print axioms root086
theorem shape086 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 193024=tree086 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 193024)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape076 f g inputs siblings]
  rw [unoccupied f g 7 193152 (by decide),siblings 7 (by decide) 193152 (by decide)]
  rfl
#print axioms shape086
def input087 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash087.message
def value087 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash087.result
theorem hash087 : JFp_SHADigest.digest input087=value087 := by
  have law := JHe_SHARealization.tree1 ⟨87, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash087
theorem address087 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [121,222,231,1,61,67,70,17,115,85,96,65,234,200,241,83,60,16,185,45,192,179,155,106,241,106,46,40,153,49,208,171]) value077)=input087 := by rfl
#print axioms address087
def tree087 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [121,222,231,1,61,67,70,17,115,85,96,65,234,200,241,83,60,16,185,45,192,179,155,106,241,106,46,40,153,49,208,171])) tree077
theorem root087 : root JFp_SHADigest.digest tree087=value087 := by
  rw [tree087,root,root077]
  exact (congrArg JFp_SHADigest.digest address087).trans hash087
#print axioms root087
theorem shape087 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 209152=tree087 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 209152)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 7 209152 (by decide),siblings 7 (by decide) 209152 (by decide)]
  rw [shape077 f g inputs siblings]
  rfl
#print axioms shape087
def input088 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash088.message
def value088 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash088.result
theorem hash088 : JFp_SHADigest.digest input088=value088 := by
  have law := JHe_SHARealization.tree1 ⟨88, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash088
theorem address088 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [236,28,32,239,13,157,49,221,114,96,197,120,98,199,111,87,83,234,74,238,160,52,25,26,27,9,205,113,23,81,124,152]) value078)=input088 := by rfl
#print axioms address088
def tree088 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [236,28,32,239,13,157,49,221,114,96,197,120,98,199,111,87,83,234,74,238,160,52,25,26,27,9,205,113,23,81,124,152])) tree078
theorem root088 : root JFp_SHADigest.digest tree088=value088 := by
  rw [tree088,root,root078]
  exact (congrArg JFp_SHADigest.digest address088).trans hash088
#print axioms root088
theorem shape088 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 216576=tree088 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 216576)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 7 216576 (by decide),siblings 7 (by decide) 216576 (by decide)]
  rw [shape078 f g inputs siblings]
  rfl
#print axioms shape088
def input089 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash089.message
def value089 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash089.result
theorem hash089 : JFp_SHADigest.digest input089=value089 := by
  have law := JHe_SHARealization.tree1 ⟨89, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash089
theorem address089 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [253,228,39,179,67,102,132,204,126,95,1,242,155,20,213,142,13,57,24,198,222,113,242,180,142,143,35,176,242,56,84,56]) value079)=input089 := by rfl
#print axioms address089
def tree089 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [253,228,39,179,67,102,132,204,126,95,1,242,155,20,213,142,13,57,24,198,222,113,242,180,142,143,35,176,242,56,84,56])) tree079
theorem root089 : root JFp_SHADigest.digest tree089=value089 := by
  rw [tree089,root,root079]
  exact (congrArg JFp_SHADigest.digest address089).trans hash089
#print axioms root089
theorem shape089 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 245760=tree089 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 245760)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 7 245760 (by decide),siblings 7 (by decide) 245760 (by decide)]
  rw [shape079 f g inputs siblings]
  rfl
#print axioms shape089
end AspisR1.JHh_C_Gr_M1Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_C_Gr_M1Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input090 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash090.message
def value090 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash090.result
theorem hash090 : JFp_SHADigest.digest input090=value090 := by
  have law := JHe_SHARealization.tree1 ⟨90, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash090
theorem address090 : BinMerkle32Path.nodeInput (children value080 (JGc_TX2_HashBytes.state [155,103,85,214,79,217,145,109,92,61,81,23,89,65,105,137,67,6,203,28,29,132,157,255,203,70,84,95,242,123,36,113]))=input090 := by rfl
#print axioms address090
def tree090 : Tree := .branch tree080 (.supplied (JGc_TX2_HashBytes.state [155,103,85,214,79,217,145,109,92,61,81,23,89,65,105,137,67,6,203,28,29,132,157,255,203,70,84,95,242,123,36,113]))
theorem root090 : root JFp_SHADigest.digest tree090=value090 := by
  rw [tree090,root,root080]
  exact (congrArg JFp_SHADigest.digest address090).trans hash090
#print axioms root090
theorem shape090 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 65536=tree090 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 65536)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape080 f g inputs siblings]
  rw [unoccupied f g 8 65792 (by decide),siblings 8 (by decide) 65792 (by decide)]
  rfl
#print axioms shape090
def input091 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash091.message
def value091 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash091.result
theorem hash091 : JFp_SHADigest.digest input091=value091 := by
  have law := JHe_SHARealization.tree1 ⟨91, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash091
theorem address091 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [58,116,96,190,215,232,35,221,38,191,2,90,224,44,164,216,51,1,133,148,238,15,199,54,87,187,234,15,80,91,124,127]) value081)=input091 := by rfl
#print axioms address091
def tree091 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [58,116,96,190,215,232,35,221,38,191,2,90,224,44,164,216,51,1,133,148,238,15,199,54,87,187,234,15,80,91,124,127])) tree081
theorem root091 : root JFp_SHADigest.digest tree091=value091 := by
  rw [tree091,root,root081]
  exact (congrArg JFp_SHADigest.digest address091).trans hash091
#print axioms root091
theorem shape091 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 93184=tree091 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 93184)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 8 93184 (by decide),siblings 8 (by decide) 93184 (by decide)]
  rw [shape081 f g inputs siblings]
  rfl
#print axioms shape091
def input092 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash092.message
def value092 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash092.result
theorem hash092 : JFp_SHADigest.digest input092=value092 := by
  have law := JHe_SHARealization.tree1 ⟨92, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash092
theorem address092 : BinMerkle32Path.nodeInput (children value082 (JGc_TX2_HashBytes.state [102,248,91,151,181,176,166,53,114,57,78,102,66,87,251,100,251,31,205,194,110,147,127,156,193,58,19,3,42,214,148,4]))=input092 := by rfl
#print axioms address092
def tree092 : Tree := .branch tree082 (.supplied (JGc_TX2_HashBytes.state [102,248,91,151,181,176,166,53,114,57,78,102,66,87,251,100,251,31,205,194,110,147,127,156,193,58,19,3,42,214,148,4]))
theorem root092 : root JFp_SHADigest.digest tree092=value092 := by
  rw [tree092,root,root082]
  exact (congrArg JFp_SHADigest.digest address092).trans hash092
#print axioms root092
theorem shape092 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 147456=tree092 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 147456)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape082 f g inputs siblings]
  rw [unoccupied f g 8 147712 (by decide),siblings 8 (by decide) 147712 (by decide)]
  rfl
#print axioms shape092
def input093 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash093.message
def value093 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash093.result
theorem hash093 : JFp_SHADigest.digest input093=value093 := by
  have law := JHe_SHARealization.tree1 ⟨93, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash093
theorem address093 : BinMerkle32Path.nodeInput (children value083 (JGc_TX2_HashBytes.state [181,230,180,31,12,17,59,166,205,11,33,224,169,103,22,14,162,127,69,73,33,189,217,17,98,68,108,205,174,164,64,124]))=input093 := by rfl
#print axioms address093
def tree093 : Tree := .branch tree083 (.supplied (JGc_TX2_HashBytes.state [181,230,180,31,12,17,59,166,205,11,33,224,169,103,22,14,162,127,69,73,33,189,217,17,98,68,108,205,174,164,64,124]))
theorem root093 : root JFp_SHADigest.digest tree093=value093 := by
  rw [tree093,root,root083]
  exact (congrArg JFp_SHADigest.digest address093).trans hash093
#print axioms root093
theorem shape093 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 159744=tree093 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 159744)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape083 f g inputs siblings]
  rw [unoccupied f g 8 160000 (by decide),siblings 8 (by decide) 160000 (by decide)]
  rfl
#print axioms shape093
def input094 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash094.message
def value094 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash094.result
theorem hash094 : JFp_SHADigest.digest input094=value094 := by
  have law := JHe_SHARealization.tree1 ⟨94, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash094
theorem address094 : BinMerkle32Path.nodeInput (children value084 (JGc_TX2_HashBytes.state [190,94,5,136,17,62,168,184,31,168,135,148,106,201,77,251,86,192,166,220,228,214,230,238,13,228,237,219,153,182,6,97]))=input094 := by rfl
#print axioms address094
def tree094 : Tree := .branch tree084 (.supplied (JGc_TX2_HashBytes.state [190,94,5,136,17,62,168,184,31,168,135,148,106,201,77,251,86,192,166,220,228,214,230,238,13,228,237,219,153,182,6,97]))
theorem root094 : root JFp_SHADigest.digest tree094=value094 := by
  rw [tree094,root,root084]
  exact (congrArg JFp_SHADigest.digest address094).trans hash094
#print axioms root094
theorem shape094 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 183808=tree094 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 183808)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape084 f g inputs siblings]
  rw [unoccupied f g 8 184064 (by decide),siblings 8 (by decide) 184064 (by decide)]
  rfl
#print axioms shape094
def input095 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash095.message
def value095 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash095.result
theorem hash095 : JFp_SHADigest.digest input095=value095 := by
  have law := JHe_SHARealization.tree1 ⟨95, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash095
theorem address095 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [101,117,98,190,161,169,31,147,28,228,55,74,81,235,49,28,180,213,167,50,32,72,106,99,146,44,200,203,152,20,148,224]) value085)=input095 := by rfl
#print axioms address095
def tree095 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [101,117,98,190,161,169,31,147,28,228,55,74,81,235,49,28,180,213,167,50,32,72,106,99,146,44,200,203,152,20,148,224])) tree085
theorem root095 : root JFp_SHADigest.digest tree095=value095 := by
  rw [tree095,root,root085]
  exact (congrArg JFp_SHADigest.digest address095).trans hash095
#print axioms root095
theorem shape095 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 192000=tree095 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 192000)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 8 192000 (by decide),siblings 8 (by decide) 192000 (by decide)]
  rw [shape085 f g inputs siblings]
  rfl
#print axioms shape095
def input096 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash096.message
def value096 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash096.result
theorem hash096 : JFp_SHADigest.digest input096=value096 := by
  have law := JHe_SHARealization.tree1 ⟨96, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash096
theorem address096 : BinMerkle32Path.nodeInput (children value086 (JGc_TX2_HashBytes.state [141,78,139,205,243,175,85,174,159,6,241,87,39,153,190,45,228,30,233,41,84,56,127,174,209,151,54,93,242,26,164,0]))=input096 := by rfl
#print axioms address096
def tree096 : Tree := .branch tree086 (.supplied (JGc_TX2_HashBytes.state [141,78,139,205,243,175,85,174,159,6,241,87,39,153,190,45,228,30,233,41,84,56,127,174,209,151,54,93,242,26,164,0]))
theorem root096 : root JFp_SHADigest.digest tree096=value096 := by
  rw [tree096,root,root086]
  exact (congrArg JFp_SHADigest.digest address096).trans hash096
#print axioms root096
theorem shape096 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 193024=tree096 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 193024)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape086 f g inputs siblings]
  rw [unoccupied f g 8 193280 (by decide),siblings 8 (by decide) 193280 (by decide)]
  rfl
#print axioms shape096
def input097 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash097.message
def value097 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash097.result
theorem hash097 : JFp_SHADigest.digest input097=value097 := by
  have law := JHe_SHARealization.tree1 ⟨97, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash097
theorem address097 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [243,43,79,171,171,236,158,171,6,102,177,162,155,60,85,93,158,195,157,106,68,63,238,61,71,98,3,55,236,229,85,103]) value087)=input097 := by rfl
#print axioms address097
def tree097 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [243,43,79,171,171,236,158,171,6,102,177,162,155,60,85,93,158,195,157,106,68,63,238,61,71,98,3,55,236,229,85,103])) tree087
theorem root097 : root JFp_SHADigest.digest tree097=value097 := by
  rw [tree097,root,root087]
  exact (congrArg JFp_SHADigest.digest address097).trans hash097
#print axioms root097
theorem shape097 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 208896=tree097 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 208896)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 8 208896 (by decide),siblings 8 (by decide) 208896 (by decide)]
  rw [shape087 f g inputs siblings]
  rfl
#print axioms shape097
def input098 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash098.message
def value098 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash098.result
theorem hash098 : JFp_SHADigest.digest input098=value098 := by
  have law := JHe_SHARealization.tree1 ⟨98, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash098
theorem address098 : BinMerkle32Path.nodeInput (children value088 (JGc_TX2_HashBytes.state [0,59,195,249,83,130,210,170,7,120,9,195,215,100,15,59,6,122,239,166,176,134,205,3,143,184,111,215,61,93,21,205]))=input098 := by rfl
#print axioms address098
def tree098 : Tree := .branch tree088 (.supplied (JGc_TX2_HashBytes.state [0,59,195,249,83,130,210,170,7,120,9,195,215,100,15,59,6,122,239,166,176,134,205,3,143,184,111,215,61,93,21,205]))
theorem root098 : root JFp_SHADigest.digest tree098=value098 := by
  rw [tree098,root,root088]
  exact (congrArg JFp_SHADigest.digest address098).trans hash098
#print axioms root098
theorem shape098 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 216576=tree098 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 216576)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape088 f g inputs siblings]
  rw [unoccupied f g 8 216832 (by decide),siblings 8 (by decide) 216832 (by decide)]
  rfl
#print axioms shape098
def input099 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash099.message
def value099 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash099.result
theorem hash099 : JFp_SHADigest.digest input099=value099 := by
  have law := JHe_SHARealization.tree1 ⟨99, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash099
theorem address099 : BinMerkle32Path.nodeInput (children value089 (JGc_TX2_HashBytes.state [30,110,144,85,51,255,13,5,112,59,188,211,168,27,244,37,155,108,73,250,65,218,219,68,254,71,61,200,99,148,247,126]))=input099 := by rfl
#print axioms address099
def tree099 : Tree := .branch tree089 (.supplied (JGc_TX2_HashBytes.state [30,110,144,85,51,255,13,5,112,59,188,211,168,27,244,37,155,108,73,250,65,218,219,68,254,71,61,200,99,148,247,126]))
theorem root099 : root JFp_SHADigest.digest tree099=value099 := by
  rw [tree099,root,root089]
  exact (congrArg JFp_SHADigest.digest address099).trans hash099
#print axioms root099
theorem shape099 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 245760=tree099 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 245760)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape089 f g inputs siblings]
  rw [unoccupied f g 8 246016 (by decide),siblings 8 (by decide) 246016 (by decide)]
  rfl
#print axioms shape099
end AspisR1.JHh_C_Gr_M1Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_C_Gr_M1Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input100 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash100.message
def value100 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash100.result
theorem hash100 : JFp_SHADigest.digest input100=value100 := by
  have law := JHe_SHARealization.tree1 ⟨100, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash100
theorem address100 : BinMerkle32Path.nodeInput (children value090 (JGc_TX2_HashBytes.state [48,144,64,126,184,85,210,61,78,213,35,254,51,10,65,79,191,48,120,196,152,221,171,137,62,2,237,75,217,230,114,206]))=input100 := by rfl
#print axioms address100
def tree100 : Tree := .branch tree090 (.supplied (JGc_TX2_HashBytes.state [48,144,64,126,184,85,210,61,78,213,35,254,51,10,65,79,191,48,120,196,152,221,171,137,62,2,237,75,217,230,114,206]))
theorem root100 : root JFp_SHADigest.digest tree100=value100 := by
  rw [tree100,root,root090]
  exact (congrArg JFp_SHADigest.digest address100).trans hash100
#print axioms root100
theorem shape100 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 65536=tree100 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 65536)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape090 f g inputs siblings]
  rw [unoccupied f g 9 66048 (by decide),siblings 9 (by decide) 66048 (by decide)]
  rfl
#print axioms shape100
def input101 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash101.message
def value101 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash101.result
theorem hash101 : JFp_SHADigest.digest input101=value101 := by
  have law := JHe_SHARealization.tree1 ⟨101, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash101
theorem address101 : BinMerkle32Path.nodeInput (children value091 (JGc_TX2_HashBytes.state [123,212,65,220,227,135,165,48,10,14,134,81,223,111,216,95,122,145,181,204,233,74,243,55,228,195,231,198,242,45,195,116]))=input101 := by rfl
#print axioms address101
def tree101 : Tree := .branch tree091 (.supplied (JGc_TX2_HashBytes.state [123,212,65,220,227,135,165,48,10,14,134,81,223,111,216,95,122,145,181,204,233,74,243,55,228,195,231,198,242,45,195,116]))
theorem root101 : root JFp_SHADigest.digest tree101=value101 := by
  rw [tree101,root,root091]
  exact (congrArg JFp_SHADigest.digest address101).trans hash101
#print axioms root101
theorem shape101 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 93184=tree101 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 93184)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape091 f g inputs siblings]
  rw [unoccupied f g 9 93696 (by decide),siblings 9 (by decide) 93696 (by decide)]
  rfl
#print axioms shape101
def input102 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash102.message
def value102 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash102.result
theorem hash102 : JFp_SHADigest.digest input102=value102 := by
  have law := JHe_SHARealization.tree1 ⟨102, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash102
theorem address102 : BinMerkle32Path.nodeInput (children value092 (JGc_TX2_HashBytes.state [105,41,192,88,96,73,217,61,90,149,168,78,2,247,208,1,169,49,116,37,15,146,137,252,165,203,84,179,141,144,47,178]))=input102 := by rfl
#print axioms address102
def tree102 : Tree := .branch tree092 (.supplied (JGc_TX2_HashBytes.state [105,41,192,88,96,73,217,61,90,149,168,78,2,247,208,1,169,49,116,37,15,146,137,252,165,203,84,179,141,144,47,178]))
theorem root102 : root JFp_SHADigest.digest tree102=value102 := by
  rw [tree102,root,root092]
  exact (congrArg JFp_SHADigest.digest address102).trans hash102
#print axioms root102
theorem shape102 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 147456=tree102 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 147456)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape092 f g inputs siblings]
  rw [unoccupied f g 9 147968 (by decide),siblings 9 (by decide) 147968 (by decide)]
  rfl
#print axioms shape102
def input103 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash103.message
def value103 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash103.result
theorem hash103 : JFp_SHADigest.digest input103=value103 := by
  have law := JHe_SHARealization.tree1 ⟨103, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash103
theorem address103 : BinMerkle32Path.nodeInput (children value093 (JGc_TX2_HashBytes.state [79,110,16,129,18,10,88,204,205,7,170,254,146,27,10,217,216,101,182,33,32,114,45,207,91,16,141,146,44,147,169,198]))=input103 := by rfl
#print axioms address103
def tree103 : Tree := .branch tree093 (.supplied (JGc_TX2_HashBytes.state [79,110,16,129,18,10,88,204,205,7,170,254,146,27,10,217,216,101,182,33,32,114,45,207,91,16,141,146,44,147,169,198]))
theorem root103 : root JFp_SHADigest.digest tree103=value103 := by
  rw [tree103,root,root093]
  exact (congrArg JFp_SHADigest.digest address103).trans hash103
#print axioms root103
theorem shape103 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 159744=tree103 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 159744)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape093 f g inputs siblings]
  rw [unoccupied f g 9 160256 (by decide),siblings 9 (by decide) 160256 (by decide)]
  rfl
#print axioms shape103
def input104 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash104.message
def value104 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash104.result
theorem hash104 : JFp_SHADigest.digest input104=value104 := by
  have law := JHe_SHARealization.tree1 ⟨104, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash104
theorem address104 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [11,211,99,36,92,115,16,181,114,150,174,18,232,7,212,203,202,159,103,225,65,179,95,167,92,166,67,145,5,238,42,44]) value094)=input104 := by rfl
#print axioms address104
def tree104 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [11,211,99,36,92,115,16,181,114,150,174,18,232,7,212,203,202,159,103,225,65,179,95,167,92,166,67,145,5,238,42,44])) tree094
theorem root104 : root JFp_SHADigest.digest tree104=value104 := by
  rw [tree104,root,root094]
  exact (congrArg JFp_SHADigest.digest address104).trans hash104
#print axioms root104
theorem shape104 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 183296=tree104 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 183296)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 9 183296 (by decide),siblings 9 (by decide) 183296 (by decide)]
  rw [shape094 f g inputs siblings]
  rfl
#print axioms shape104
def input105 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash105.message
def value105 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash105.result
theorem hash105 : JFp_SHADigest.digest input105=value105 := by
  have law := JHe_SHARealization.tree1 ⟨105, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash105
theorem address105 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [208,162,139,184,71,32,217,179,68,248,58,170,4,146,236,236,84,29,218,63,17,10,25,168,216,57,163,181,19,17,253,247]) value095)=input105 := by rfl
#print axioms address105
def tree105 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [208,162,139,184,71,32,217,179,68,248,58,170,4,146,236,236,84,29,218,63,17,10,25,168,216,57,163,181,19,17,253,247])) tree095
theorem root105 : root JFp_SHADigest.digest tree105=value105 := by
  rw [tree105,root,root095]
  exact (congrArg JFp_SHADigest.digest address105).trans hash105
#print axioms root105
theorem shape105 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 191488=tree105 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 191488)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 9 191488 (by decide),siblings 9 (by decide) 191488 (by decide)]
  rw [shape095 f g inputs siblings]
  rfl
#print axioms shape105
def input106 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash106.message
def value106 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash106.result
theorem hash106 : JFp_SHADigest.digest input106=value106 := by
  have law := JHe_SHARealization.tree1 ⟨106, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash106
theorem address106 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [60,103,59,209,113,130,229,235,243,97,45,115,125,45,43,4,217,213,119,152,92,68,200,106,165,187,222,51,4,211,153,18]) value096)=input106 := by rfl
#print axioms address106
def tree106 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [60,103,59,209,113,130,229,235,243,97,45,115,125,45,43,4,217,213,119,152,92,68,200,106,165,187,222,51,4,211,153,18])) tree096
theorem root106 : root JFp_SHADigest.digest tree106=value106 := by
  rw [tree106,root,root096]
  exact (congrArg JFp_SHADigest.digest address106).trans hash106
#print axioms root106
theorem shape106 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 192512=tree106 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 192512)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 9 192512 (by decide),siblings 9 (by decide) 192512 (by decide)]
  rw [shape096 f g inputs siblings]
  rfl
#print axioms shape106
def input107 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash107.message
def value107 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash107.result
theorem hash107 : JFp_SHADigest.digest input107=value107 := by
  have law := JHe_SHARealization.tree1 ⟨107, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash107
theorem address107 : BinMerkle32Path.nodeInput (children value097 (JGc_TX2_HashBytes.state [19,72,36,207,19,187,133,44,138,222,148,125,141,146,17,59,41,212,119,158,223,201,152,145,76,37,91,48,226,129,30,9]))=input107 := by rfl
#print axioms address107
def tree107 : Tree := .branch tree097 (.supplied (JGc_TX2_HashBytes.state [19,72,36,207,19,187,133,44,138,222,148,125,141,146,17,59,41,212,119,158,223,201,152,145,76,37,91,48,226,129,30,9]))
theorem root107 : root JFp_SHADigest.digest tree107=value107 := by
  rw [tree107,root,root097]
  exact (congrArg JFp_SHADigest.digest address107).trans hash107
#print axioms root107
theorem shape107 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 208896=tree107 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 208896)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape097 f g inputs siblings]
  rw [unoccupied f g 9 209408 (by decide),siblings 9 (by decide) 209408 (by decide)]
  rfl
#print axioms shape107
def input108 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash108.message
def value108 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash108.result
theorem hash108 : JFp_SHADigest.digest input108=value108 := by
  have law := JHe_SHARealization.tree1 ⟨108, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash108
theorem address108 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [186,33,168,206,73,137,127,197,84,223,139,201,20,128,251,0,154,250,60,123,141,245,74,52,213,26,143,116,98,102,120,146]) value098)=input108 := by rfl
#print axioms address108
def tree108 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [186,33,168,206,73,137,127,197,84,223,139,201,20,128,251,0,154,250,60,123,141,245,74,52,213,26,143,116,98,102,120,146])) tree098
theorem root108 : root JFp_SHADigest.digest tree108=value108 := by
  rw [tree108,root,root098]
  exact (congrArg JFp_SHADigest.digest address108).trans hash108
#print axioms root108
theorem shape108 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 216064=tree108 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 216064)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 9 216064 (by decide),siblings 9 (by decide) 216064 (by decide)]
  rw [shape098 f g inputs siblings]
  rfl
#print axioms shape108
def input109 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash109.message
def value109 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash109.result
theorem hash109 : JFp_SHADigest.digest input109=value109 := by
  have law := JHe_SHARealization.tree1 ⟨109, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash109
theorem address109 : BinMerkle32Path.nodeInput (children value099 (JGc_TX2_HashBytes.state [58,64,20,28,188,224,199,55,182,135,197,202,243,225,130,75,187,86,96,87,139,220,144,34,26,247,190,0,220,86,80,95]))=input109 := by rfl
#print axioms address109
def tree109 : Tree := .branch tree099 (.supplied (JGc_TX2_HashBytes.state [58,64,20,28,188,224,199,55,182,135,197,202,243,225,130,75,187,86,96,87,139,220,144,34,26,247,190,0,220,86,80,95]))
theorem root109 : root JFp_SHADigest.digest tree109=value109 := by
  rw [tree109,root,root099]
  exact (congrArg JFp_SHADigest.digest address109).trans hash109
#print axioms root109
theorem shape109 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 245760=tree109 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 245760)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape099 f g inputs siblings]
  rw [unoccupied f g 9 246272 (by decide),siblings 9 (by decide) 246272 (by decide)]
  rfl
#print axioms shape109
end AspisR1.JHh_C_Gr_M1Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_C_Gr_M1Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input110 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash110.message
def value110 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash110.result
theorem hash110 : JFp_SHADigest.digest input110=value110 := by
  have law := JHe_SHARealization.tree1 ⟨110, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash110
theorem address110 : BinMerkle32Path.nodeInput (children value100 (JGc_TX2_HashBytes.state [64,93,241,125,70,107,252,101,30,148,14,215,74,250,227,182,249,65,129,42,162,101,220,242,179,42,5,160,220,31,103,150]))=input110 := by rfl
#print axioms address110
def tree110 : Tree := .branch tree100 (.supplied (JGc_TX2_HashBytes.state [64,93,241,125,70,107,252,101,30,148,14,215,74,250,227,182,249,65,129,42,162,101,220,242,179,42,5,160,220,31,103,150]))
theorem root110 : root JFp_SHADigest.digest tree110=value110 := by
  rw [tree110,root,root100]
  exact (congrArg JFp_SHADigest.digest address110).trans hash110
#print axioms root110
theorem shape110 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 65536=tree110 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 65536)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape100 f g inputs siblings]
  rw [unoccupied f g 10 66560 (by decide),siblings 10 (by decide) 66560 (by decide)]
  rfl
#print axioms shape110
def input111 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash111.message
def value111 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash111.result
theorem hash111 : JFp_SHADigest.digest input111=value111 := by
  have law := JHe_SHARealization.tree1 ⟨111, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash111
theorem address111 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [198,65,48,63,241,221,71,5,120,194,136,208,90,35,236,55,212,20,152,28,68,68,108,189,66,188,78,237,91,99,244,231]) value101)=input111 := by rfl
#print axioms address111
def tree111 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [198,65,48,63,241,221,71,5,120,194,136,208,90,35,236,55,212,20,152,28,68,68,108,189,66,188,78,237,91,99,244,231])) tree101
theorem root111 : root JFp_SHADigest.digest tree111=value111 := by
  rw [tree111,root,root101]
  exact (congrArg JFp_SHADigest.digest address111).trans hash111
#print axioms root111
theorem shape111 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 92160=tree111 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 92160)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 10 92160 (by decide),siblings 10 (by decide) 92160 (by decide)]
  rw [shape101 f g inputs siblings]
  rfl
#print axioms shape111
def input112 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash112.message
def value112 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash112.result
theorem hash112 : JFp_SHADigest.digest input112=value112 := by
  have law := JHe_SHARealization.tree1 ⟨112, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash112
theorem address112 : BinMerkle32Path.nodeInput (children value102 (JGc_TX2_HashBytes.state [164,41,120,158,16,43,175,133,186,191,175,18,223,41,66,159,126,137,11,165,228,232,46,160,78,239,53,218,10,204,109,142]))=input112 := by rfl
#print axioms address112
def tree112 : Tree := .branch tree102 (.supplied (JGc_TX2_HashBytes.state [164,41,120,158,16,43,175,133,186,191,175,18,223,41,66,159,126,137,11,165,228,232,46,160,78,239,53,218,10,204,109,142]))
theorem root112 : root JFp_SHADigest.digest tree112=value112 := by
  rw [tree112,root,root102]
  exact (congrArg JFp_SHADigest.digest address112).trans hash112
#print axioms root112
theorem shape112 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 147456=tree112 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 147456)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape102 f g inputs siblings]
  rw [unoccupied f g 10 148480 (by decide),siblings 10 (by decide) 148480 (by decide)]
  rfl
#print axioms shape112
def input113 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash113.message
def value113 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash113.result
theorem hash113 : JFp_SHADigest.digest input113=value113 := by
  have law := JHe_SHARealization.tree1 ⟨113, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash113
theorem address113 : BinMerkle32Path.nodeInput (children value103 (JGc_TX2_HashBytes.state [100,11,72,203,23,49,116,82,9,97,40,39,67,176,85,179,239,78,31,49,180,135,233,14,182,133,146,114,96,7,47,39]))=input113 := by rfl
#print axioms address113
def tree113 : Tree := .branch tree103 (.supplied (JGc_TX2_HashBytes.state [100,11,72,203,23,49,116,82,9,97,40,39,67,176,85,179,239,78,31,49,180,135,233,14,182,133,146,114,96,7,47,39]))
theorem root113 : root JFp_SHADigest.digest tree113=value113 := by
  rw [tree113,root,root103]
  exact (congrArg JFp_SHADigest.digest address113).trans hash113
#print axioms root113
theorem shape113 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 159744=tree113 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 159744)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape103 f g inputs siblings]
  rw [unoccupied f g 10 160768 (by decide),siblings 10 (by decide) 160768 (by decide)]
  rfl
#print axioms shape113
def input114 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash114.message
def value114 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash114.result
theorem hash114 : JFp_SHADigest.digest input114=value114 := by
  have law := JHe_SHARealization.tree1 ⟨114, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash114
theorem address114 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [184,18,54,84,108,157,180,156,80,20,210,100,117,102,246,78,234,211,56,215,194,254,92,204,54,91,195,240,221,94,111,149]) value104)=input114 := by rfl
#print axioms address114
def tree114 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [184,18,54,84,108,157,180,156,80,20,210,100,117,102,246,78,234,211,56,215,194,254,92,204,54,91,195,240,221,94,111,149])) tree104
theorem root114 : root JFp_SHADigest.digest tree114=value114 := by
  rw [tree114,root,root104]
  exact (congrArg JFp_SHADigest.digest address114).trans hash114
#print axioms root114
theorem shape114 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 182272=tree114 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 182272)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 10 182272 (by decide),siblings 10 (by decide) 182272 (by decide)]
  rw [shape104 f g inputs siblings]
  rfl
#print axioms shape114
def input115 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash115.message
def value115 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash115.result
theorem hash115 : JFp_SHADigest.digest input115=value115 := by
  have law := JHe_SHARealization.tree1 ⟨115, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash115
theorem address115 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [63,228,40,85,211,28,242,188,32,35,226,36,237,119,146,127,123,57,188,62,64,103,16,217,15,240,231,101,242,238,216,229]) value105)=input115 := by rfl
#print axioms address115
def tree115 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [63,228,40,85,211,28,242,188,32,35,226,36,237,119,146,127,123,57,188,62,64,103,16,217,15,240,231,101,242,238,216,229])) tree105
theorem root115 : root JFp_SHADigest.digest tree115=value115 := by
  rw [tree115,root,root105]
  exact (congrArg JFp_SHADigest.digest address115).trans hash115
#print axioms root115
theorem shape115 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 190464=tree115 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 190464)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 10 190464 (by decide),siblings 10 (by decide) 190464 (by decide)]
  rw [shape105 f g inputs siblings]
  rfl
#print axioms shape115
def input116 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash116.message
def value116 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash116.result
theorem hash116 : JFp_SHADigest.digest input116=value116 := by
  have law := JHe_SHARealization.tree1 ⟨116, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash116
theorem address116 : BinMerkle32Path.nodeInput (children value106 (JGc_TX2_HashBytes.state [130,69,10,242,115,118,110,253,30,219,254,90,113,163,245,178,100,145,233,86,77,1,166,132,100,215,190,224,34,250,87,35]))=input116 := by rfl
#print axioms address116
def tree116 : Tree := .branch tree106 (.supplied (JGc_TX2_HashBytes.state [130,69,10,242,115,118,110,253,30,219,254,90,113,163,245,178,100,145,233,86,77,1,166,132,100,215,190,224,34,250,87,35]))
theorem root116 : root JFp_SHADigest.digest tree116=value116 := by
  rw [tree116,root,root106]
  exact (congrArg JFp_SHADigest.digest address116).trans hash116
#print axioms root116
theorem shape116 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 192512=tree116 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 192512)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape106 f g inputs siblings]
  rw [unoccupied f g 10 193536 (by decide),siblings 10 (by decide) 193536 (by decide)]
  rfl
#print axioms shape116
def input117 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash117.message
def value117 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash117.result
theorem hash117 : JFp_SHADigest.digest input117=value117 := by
  have law := JHe_SHARealization.tree1 ⟨117, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash117
theorem address117 : BinMerkle32Path.nodeInput (children value107 (JGc_TX2_HashBytes.state [112,24,125,244,37,57,3,138,146,193,211,93,237,176,196,152,131,55,166,189,57,218,132,5,116,252,78,158,63,50,109,12]))=input117 := by rfl
#print axioms address117
def tree117 : Tree := .branch tree107 (.supplied (JGc_TX2_HashBytes.state [112,24,125,244,37,57,3,138,146,193,211,93,237,176,196,152,131,55,166,189,57,218,132,5,116,252,78,158,63,50,109,12]))
theorem root117 : root JFp_SHADigest.digest tree117=value117 := by
  rw [tree117,root,root107]
  exact (congrArg JFp_SHADigest.digest address117).trans hash117
#print axioms root117
theorem shape117 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 208896=tree117 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 208896)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape107 f g inputs siblings]
  rw [unoccupied f g 10 209920 (by decide),siblings 10 (by decide) 209920 (by decide)]
  rfl
#print axioms shape117
def input118 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash118.message
def value118 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash118.result
theorem hash118 : JFp_SHADigest.digest input118=value118 := by
  have law := JHe_SHARealization.tree1 ⟨118, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash118
theorem address118 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [215,230,177,31,18,107,67,128,173,64,143,244,114,180,207,188,65,56,143,94,43,60,198,20,173,93,12,193,37,52,52,140]) value108)=input118 := by rfl
#print axioms address118
def tree118 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [215,230,177,31,18,107,67,128,173,64,143,244,114,180,207,188,65,56,143,94,43,60,198,20,173,93,12,193,37,52,52,140])) tree108
theorem root118 : root JFp_SHADigest.digest tree118=value118 := by
  rw [tree118,root,root108]
  exact (congrArg JFp_SHADigest.digest address118).trans hash118
#print axioms root118
theorem shape118 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 215040=tree118 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 215040)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 10 215040 (by decide),siblings 10 (by decide) 215040 (by decide)]
  rw [shape108 f g inputs siblings]
  rfl
#print axioms shape118
def input119 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash119.message
def value119 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash119.result
theorem hash119 : JFp_SHADigest.digest input119=value119 := by
  have law := JHe_SHARealization.tree1 ⟨119, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash119
theorem address119 : BinMerkle32Path.nodeInput (children value109 (JGc_TX2_HashBytes.state [103,164,167,122,243,231,22,164,230,111,87,102,49,233,9,71,238,122,34,122,154,242,71,9,153,52,13,204,21,144,129,141]))=input119 := by rfl
#print axioms address119
def tree119 : Tree := .branch tree109 (.supplied (JGc_TX2_HashBytes.state [103,164,167,122,243,231,22,164,230,111,87,102,49,233,9,71,238,122,34,122,154,242,71,9,153,52,13,204,21,144,129,141]))
theorem root119 : root JFp_SHADigest.digest tree119=value119 := by
  rw [tree119,root,root109]
  exact (congrArg JFp_SHADigest.digest address119).trans hash119
#print axioms root119
theorem shape119 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 245760=tree119 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 245760)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape109 f g inputs siblings]
  rw [unoccupied f g 10 246784 (by decide),siblings 10 (by decide) 246784 (by decide)]
  rfl
#print axioms shape119
end AspisR1.JHh_C_Gr_M1Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_C_Gr_M1Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input120 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash120.message
def value120 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash120.result
theorem hash120 : JFp_SHADigest.digest input120=value120 := by
  have law := JHe_SHARealization.tree1 ⟨120, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash120
theorem address120 : BinMerkle32Path.nodeInput (children value110 (JGc_TX2_HashBytes.state [217,175,196,100,106,166,4,160,30,133,139,241,21,195,125,114,222,108,239,37,188,97,229,163,164,197,201,14,71,43,175,9]))=input120 := by rfl
#print axioms address120
def tree120 : Tree := .branch tree110 (.supplied (JGc_TX2_HashBytes.state [217,175,196,100,106,166,4,160,30,133,139,241,21,195,125,114,222,108,239,37,188,97,229,163,164,197,201,14,71,43,175,9]))
theorem root120 : root JFp_SHADigest.digest tree120=value120 := by
  rw [tree120,root,root110]
  exact (congrArg JFp_SHADigest.digest address120).trans hash120
#print axioms root120
theorem shape120 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 12 65536=tree120 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 12 65536)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape110 f g inputs siblings]
  rw [unoccupied f g 11 67584 (by decide),siblings 11 (by decide) 67584 (by decide)]
  rfl
#print axioms shape120
def input121 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash121.message
def value121 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash121.result
theorem hash121 : JFp_SHADigest.digest input121=value121 := by
  have law := JHe_SHARealization.tree1 ⟨121, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash121
theorem address121 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [245,86,191,21,128,168,40,91,146,136,112,192,222,80,59,237,196,147,226,240,168,112,253,192,150,7,143,51,196,9,248,37]) value111)=input121 := by rfl
#print axioms address121
def tree121 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [245,86,191,21,128,168,40,91,146,136,112,192,222,80,59,237,196,147,226,240,168,112,253,192,150,7,143,51,196,9,248,37])) tree111
theorem root121 : root JFp_SHADigest.digest tree121=value121 := by
  rw [tree121,root,root111]
  exact (congrArg JFp_SHADigest.digest address121).trans hash121
#print axioms root121
theorem shape121 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 12 90112=tree121 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 12 90112)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 11 90112 (by decide),siblings 11 (by decide) 90112 (by decide)]
  rw [shape111 f g inputs siblings]
  rfl
#print axioms shape121
def input122 : Bytes := JGh_TX2_M1Roots.input150
def value122 : State := JGh_TX2_M1Roots.value150
theorem hash122 : JFp_SHADigest.digest input122=value122 := by
  have law := JHe_SHARealization.tree1 ⟨122, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash122
theorem address122 : BinMerkle32Path.nodeInput (children value112 (JGc_TX2_HashBytes.state [211,15,11,17,227,198,215,231,129,25,99,34,247,62,244,155,62,104,100,207,187,196,141,130,8,193,86,21,253,129,202,143]))=input122 := by rfl
#print axioms address122
def tree122 : Tree := .branch tree112 (.supplied (JGc_TX2_HashBytes.state [211,15,11,17,227,198,215,231,129,25,99,34,247,62,244,155,62,104,100,207,187,196,141,130,8,193,86,21,253,129,202,143]))
theorem root122 : root JFp_SHADigest.digest tree122=value122 := by
  rw [tree122,root,root112]
  exact (congrArg JFp_SHADigest.digest address122).trans hash122
#print axioms root122
theorem shape122 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 12 147456=tree122 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 12 147456)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape112 f g inputs siblings]
  rw [unoccupied f g 11 149504 (by decide),siblings 11 (by decide) 149504 (by decide)]
  rfl
#print axioms shape122
def input123 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash123.message
def value123 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash123.result
theorem hash123 : JFp_SHADigest.digest input123=value123 := by
  have law := JHe_SHARealization.tree1 ⟨123, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash123
theorem address123 : BinMerkle32Path.nodeInput (children value113 (JGc_TX2_HashBytes.state [15,101,120,74,113,3,178,205,140,1,22,242,63,68,171,18,163,88,82,90,84,49,24,53,10,48,240,86,180,229,195,57]))=input123 := by rfl
#print axioms address123
def tree123 : Tree := .branch tree113 (.supplied (JGc_TX2_HashBytes.state [15,101,120,74,113,3,178,205,140,1,22,242,63,68,171,18,163,88,82,90,84,49,24,53,10,48,240,86,180,229,195,57]))
theorem root123 : root JFp_SHADigest.digest tree123=value123 := by
  rw [tree123,root,root113]
  exact (congrArg JFp_SHADigest.digest address123).trans hash123
#print axioms root123
theorem shape123 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 12 159744=tree123 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 12 159744)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape113 f g inputs siblings]
  rw [unoccupied f g 11 161792 (by decide),siblings 11 (by decide) 161792 (by decide)]
  rfl
#print axioms shape123
def input124 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash124.message
def value124 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash124.result
theorem hash124 : JFp_SHADigest.digest input124=value124 := by
  have law := JHe_SHARealization.tree1 ⟨124, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash124
theorem address124 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [196,176,224,63,58,66,146,38,214,180,92,204,177,20,194,41,249,159,205,160,145,250,27,12,85,20,34,52,29,203,225,93]) value114)=input124 := by rfl
#print axioms address124
def tree124 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [196,176,224,63,58,66,146,38,214,180,92,204,177,20,194,41,249,159,205,160,145,250,27,12,85,20,34,52,29,203,225,93])) tree114
theorem root124 : root JFp_SHADigest.digest tree124=value124 := by
  rw [tree124,root,root114]
  exact (congrArg JFp_SHADigest.digest address124).trans hash124
#print axioms root124
theorem shape124 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 12 180224=tree124 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 12 180224)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 11 180224 (by decide),siblings 11 (by decide) 180224 (by decide)]
  rw [shape114 f g inputs siblings]
  rfl
#print axioms shape124
def input125 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash125.message
def value125 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash125.result
theorem hash125 : JFp_SHADigest.digest input125=value125 := by
  have law := JHe_SHARealization.tree1 ⟨125, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash125
theorem address125 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [167,124,21,206,95,202,120,7,203,62,13,33,133,95,118,113,8,86,18,144,249,35,80,206,151,128,245,184,149,62,143,89]) value115)=input125 := by rfl
#print axioms address125
def tree125 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [167,124,21,206,95,202,120,7,203,62,13,33,133,95,118,113,8,86,18,144,249,35,80,206,151,128,245,184,149,62,143,89])) tree115
theorem root125 : root JFp_SHADigest.digest tree125=value125 := by
  rw [tree125,root,root115]
  exact (congrArg JFp_SHADigest.digest address125).trans hash125
#print axioms root125
theorem shape125 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 12 188416=tree125 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 12 188416)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 11 188416 (by decide),siblings 11 (by decide) 188416 (by decide)]
  rw [shape115 f g inputs siblings]
  rfl
#print axioms shape125
def input126 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash126.message
def value126 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash126.result
theorem hash126 : JFp_SHADigest.digest input126=value126 := by
  have law := JHe_SHARealization.tree1 ⟨126, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash126
theorem address126 : BinMerkle32Path.nodeInput (children value116 (JGc_TX2_HashBytes.state [40,24,99,188,225,201,92,11,125,146,207,221,1,133,77,170,92,32,179,180,208,97,222,61,235,239,136,46,164,100,6,189]))=input126 := by rfl
#print axioms address126
def tree126 : Tree := .branch tree116 (.supplied (JGc_TX2_HashBytes.state [40,24,99,188,225,201,92,11,125,146,207,221,1,133,77,170,92,32,179,180,208,97,222,61,235,239,136,46,164,100,6,189]))
theorem root126 : root JFp_SHADigest.digest tree126=value126 := by
  rw [tree126,root,root116]
  exact (congrArg JFp_SHADigest.digest address126).trans hash126
#print axioms root126
theorem shape126 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 12 192512=tree126 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 12 192512)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape116 f g inputs siblings]
  rw [unoccupied f g 11 194560 (by decide),siblings 11 (by decide) 194560 (by decide)]
  rfl
#print axioms shape126
def input127 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash127.message
def value127 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash127.result
theorem hash127 : JFp_SHADigest.digest input127=value127 := by
  have law := JHe_SHARealization.tree1 ⟨127, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash127
theorem address127 : BinMerkle32Path.nodeInput (children value117 (JGc_TX2_HashBytes.state [108,85,77,126,24,37,128,176,24,222,208,119,252,7,77,71,162,105,159,240,41,58,2,199,0,136,85,41,86,124,234,35]))=input127 := by rfl
#print axioms address127
def tree127 : Tree := .branch tree117 (.supplied (JGc_TX2_HashBytes.state [108,85,77,126,24,37,128,176,24,222,208,119,252,7,77,71,162,105,159,240,41,58,2,199,0,136,85,41,86,124,234,35]))
theorem root127 : root JFp_SHADigest.digest tree127=value127 := by
  rw [tree127,root,root117]
  exact (congrArg JFp_SHADigest.digest address127).trans hash127
#print axioms root127
theorem shape127 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 12 208896=tree127 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 12 208896)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape117 f g inputs siblings]
  rw [unoccupied f g 11 210944 (by decide),siblings 11 (by decide) 210944 (by decide)]
  rfl
#print axioms shape127
def input128 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash128.message
def value128 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash128.result
theorem hash128 : JFp_SHADigest.digest input128=value128 := by
  have law := JHe_SHARealization.tree1 ⟨128, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash128
theorem address128 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [210,204,100,222,46,98,83,84,247,179,170,243,109,102,248,130,215,145,18,205,170,10,130,187,6,137,151,18,195,62,117,160]) value118)=input128 := by rfl
#print axioms address128
def tree128 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [210,204,100,222,46,98,83,84,247,179,170,243,109,102,248,130,215,145,18,205,170,10,130,187,6,137,151,18,195,62,117,160])) tree118
theorem root128 : root JFp_SHADigest.digest tree128=value128 := by
  rw [tree128,root,root118]
  exact (congrArg JFp_SHADigest.digest address128).trans hash128
#print axioms root128
theorem shape128 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 12 212992=tree128 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 12 212992)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 11 212992 (by decide),siblings 11 (by decide) 212992 (by decide)]
  rw [shape118 f g inputs siblings]
  rfl
#print axioms shape128
def input129 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash129.message
def value129 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash129.result
theorem hash129 : JFp_SHADigest.digest input129=value129 := by
  have law := JHe_SHARealization.tree1 ⟨129, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash129
theorem address129 : BinMerkle32Path.nodeInput (children value119 (JGc_TX2_HashBytes.state [36,122,216,128,213,83,7,55,28,214,71,249,243,137,72,100,98,181,52,193,77,132,94,236,71,30,38,228,18,154,155,76]))=input129 := by rfl
#print axioms address129
def tree129 : Tree := .branch tree119 (.supplied (JGc_TX2_HashBytes.state [36,122,216,128,213,83,7,55,28,214,71,249,243,137,72,100,98,181,52,193,77,132,94,236,71,30,38,228,18,154,155,76]))
theorem root129 : root JFp_SHADigest.digest tree129=value129 := by
  rw [tree129,root,root119]
  exact (congrArg JFp_SHADigest.digest address129).trans hash129
#print axioms root129
theorem shape129 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 12 245760=tree129 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 12 245760)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape119 f g inputs siblings]
  rw [unoccupied f g 11 247808 (by decide),siblings 11 (by decide) 247808 (by decide)]
  rfl
#print axioms shape129
end AspisR1.JHh_C_Gr_M1Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_C_Gr_M1Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input130 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash130.message
def value130 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash130.result
theorem hash130 : JFp_SHADigest.digest input130=value130 := by
  have law := JHe_SHARealization.tree1 ⟨130, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash130
theorem address130 : BinMerkle32Path.nodeInput (children value120 (JGc_TX2_HashBytes.state [19,103,232,182,95,97,172,122,95,102,130,230,233,176,203,8,117,127,219,234,112,18,233,156,196,18,149,209,241,77,161,56]))=input130 := by rfl
#print axioms address130
def tree130 : Tree := .branch tree120 (.supplied (JGc_TX2_HashBytes.state [19,103,232,182,95,97,172,122,95,102,130,230,233,176,203,8,117,127,219,234,112,18,233,156,196,18,149,209,241,77,161,56]))
theorem root130 : root JFp_SHADigest.digest tree130=value130 := by
  rw [tree130,root,root120]
  exact (congrArg JFp_SHADigest.digest address130).trans hash130
#print axioms root130
theorem shape130 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 13 65536=tree130 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 13 65536)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape120 f g inputs siblings]
  rw [unoccupied f g 12 69632 (by decide),siblings 12 (by decide) 69632 (by decide)]
  rfl
#print axioms shape130
def input131 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash131.message
def value131 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash131.result
theorem hash131 : JFp_SHADigest.digest input131=value131 := by
  have law := JHe_SHARealization.tree1 ⟨131, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash131
theorem address131 : BinMerkle32Path.nodeInput (children value121 (JGc_TX2_HashBytes.state [110,25,47,112,26,76,158,29,84,93,93,101,136,114,133,182,113,217,50,169,101,168,154,202,147,239,155,119,156,1,149,227]))=input131 := by rfl
#print axioms address131
def tree131 : Tree := .branch tree121 (.supplied (JGc_TX2_HashBytes.state [110,25,47,112,26,76,158,29,84,93,93,101,136,114,133,182,113,217,50,169,101,168,154,202,147,239,155,119,156,1,149,227]))
theorem root131 : root JFp_SHADigest.digest tree131=value131 := by
  rw [tree131,root,root121]
  exact (congrArg JFp_SHADigest.digest address131).trans hash131
#print axioms root131
theorem shape131 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 13 90112=tree131 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 13 90112)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape121 f g inputs siblings]
  rw [unoccupied f g 12 94208 (by decide),siblings 12 (by decide) 94208 (by decide)]
  rfl
#print axioms shape131
def input132 : Bytes := JGh_TX2_M1Roots.input161
def value132 : State := JGh_TX2_M1Roots.value161
theorem hash132 : JFp_SHADigest.digest input132=value132 := by
  have law := JHe_SHARealization.tree1 ⟨132, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash132
theorem address132 : BinMerkle32Path.nodeInput (children value122 (JGc_TX2_HashBytes.state [125,179,140,223,84,63,248,207,79,4,254,76,50,105,252,113,154,218,31,6,172,77,212,91,67,94,96,253,37,229,243,212]))=input132 := by rfl
#print axioms address132
def tree132 : Tree := .branch tree122 (.supplied (JGc_TX2_HashBytes.state [125,179,140,223,84,63,248,207,79,4,254,76,50,105,252,113,154,218,31,6,172,77,212,91,67,94,96,253,37,229,243,212]))
theorem root132 : root JFp_SHADigest.digest tree132=value132 := by
  rw [tree132,root,root122]
  exact (congrArg JFp_SHADigest.digest address132).trans hash132
#print axioms root132
theorem shape132 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 13 147456=tree132 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 13 147456)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape122 f g inputs siblings]
  rw [unoccupied f g 12 151552 (by decide),siblings 12 (by decide) 151552 (by decide)]
  rfl
#print axioms shape132
def input133 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash133.message
def value133 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash133.result
theorem hash133 : JFp_SHADigest.digest input133=value133 := by
  have law := JHe_SHARealization.tree1 ⟨133, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash133
theorem address133 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [202,244,232,254,150,185,96,120,137,19,88,126,27,134,33,218,94,250,191,155,104,44,152,222,79,170,78,156,230,59,10,83]) value123)=input133 := by rfl
#print axioms address133
def tree133 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [202,244,232,254,150,185,96,120,137,19,88,126,27,134,33,218,94,250,191,155,104,44,152,222,79,170,78,156,230,59,10,83])) tree123
theorem root133 : root JFp_SHADigest.digest tree133=value133 := by
  rw [tree133,root,root123]
  exact (congrArg JFp_SHADigest.digest address133).trans hash133
#print axioms root133
theorem shape133 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 13 155648=tree133 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 13 155648)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 12 155648 (by decide),siblings 12 (by decide) 155648 (by decide)]
  rw [shape123 f g inputs siblings]
  rfl
#print axioms shape133
def input134 : Bytes := JGh_TX2_M1Roots.input164
def value134 : State := JGh_TX2_M1Roots.value164
theorem hash134 : JFp_SHADigest.digest input134=value134 := by
  have law := JHe_SHARealization.tree1 ⟨134, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash134
theorem address134 : BinMerkle32Path.nodeInput (children value124 (JGc_TX2_HashBytes.state [166,50,145,224,172,240,239,69,50,244,235,90,162,220,82,237,69,91,183,14,206,124,87,33,164,12,204,235,137,70,174,5]))=input134 := by rfl
#print axioms address134
def tree134 : Tree := .branch tree124 (.supplied (JGc_TX2_HashBytes.state [166,50,145,224,172,240,239,69,50,244,235,90,162,220,82,237,69,91,183,14,206,124,87,33,164,12,204,235,137,70,174,5]))
theorem root134 : root JFp_SHADigest.digest tree134=value134 := by
  rw [tree134,root,root124]
  exact (congrArg JFp_SHADigest.digest address134).trans hash134
#print axioms root134
theorem shape134 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 13 180224=tree134 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 13 180224)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape124 f g inputs siblings]
  rw [unoccupied f g 12 184320 (by decide),siblings 12 (by decide) 184320 (by decide)]
  rfl
#print axioms shape134
def input135 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash135.message
def value135 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash135.result
theorem hash135 : JFp_SHADigest.digest input135=value135 := by
  have law := JHe_SHARealization.tree1 ⟨135, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash135
theorem address135 : BinMerkle32Path.nodeInput (children value125 value126)=input135 := by rfl
#print axioms address135
def tree135 : Tree := .branch tree125 tree126
theorem root135 : root JFp_SHADigest.digest tree135=value135 := by
  rw [tree135,root,root125,root126]
  exact (congrArg JFp_SHADigest.digest address135).trans hash135
#print axioms root135
theorem shape135 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 13 188416=tree135 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 13 188416)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape125 f g inputs siblings]
  rw [shape126 f g inputs siblings]
  rfl
#print axioms shape135
def input136 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash136.message
def value136 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash136.result
theorem hash136 : JFp_SHADigest.digest input136=value136 := by
  have law := JHe_SHARealization.tree1 ⟨136, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash136
theorem address136 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [153,133,221,15,146,6,115,140,230,185,130,26,225,15,86,62,76,251,182,229,99,145,33,151,46,29,16,78,20,210,184,89]) value127)=input136 := by rfl
#print axioms address136
def tree136 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [153,133,221,15,146,6,115,140,230,185,130,26,225,15,86,62,76,251,182,229,99,145,33,151,46,29,16,78,20,210,184,89])) tree127
theorem root136 : root JFp_SHADigest.digest tree136=value136 := by
  rw [tree136,root,root127]
  exact (congrArg JFp_SHADigest.digest address136).trans hash136
#print axioms root136
theorem shape136 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 13 204800=tree136 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 13 204800)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 12 204800 (by decide),siblings 12 (by decide) 204800 (by decide)]
  rw [shape127 f g inputs siblings]
  rfl
#print axioms shape136
def input137 : Bytes := JGh_TX2_M1Roots.input165
def value137 : State := JGh_TX2_M1Roots.value165
theorem hash137 : JFp_SHADigest.digest input137=value137 := by
  have law := JHe_SHARealization.tree1 ⟨137, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash137
theorem address137 : BinMerkle32Path.nodeInput (children value128 (JGc_TX2_HashBytes.state [66,199,69,31,236,191,95,45,107,250,179,40,169,78,64,209,27,26,172,83,225,86,252,237,38,168,176,210,39,212,103,98]))=input137 := by rfl
#print axioms address137
def tree137 : Tree := .branch tree128 (.supplied (JGc_TX2_HashBytes.state [66,199,69,31,236,191,95,45,107,250,179,40,169,78,64,209,27,26,172,83,225,86,252,237,38,168,176,210,39,212,103,98]))
theorem root137 : root JFp_SHADigest.digest tree137=value137 := by
  rw [tree137,root,root128]
  exact (congrArg JFp_SHADigest.digest address137).trans hash137
#print axioms root137
theorem shape137 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 13 212992=tree137 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 13 212992)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape128 f g inputs siblings]
  rw [unoccupied f g 12 217088 (by decide),siblings 12 (by decide) 217088 (by decide)]
  rfl
#print axioms shape137
def input138 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash138.message
def value138 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash138.result
theorem hash138 : JFp_SHADigest.digest input138=value138 := by
  have law := JHe_SHARealization.tree1 ⟨138, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash138
theorem address138 : BinMerkle32Path.nodeInput (children value129 (JGc_TX2_HashBytes.state [235,175,68,146,148,50,230,240,90,237,138,62,236,194,107,145,48,135,75,194,84,203,138,124,153,6,202,37,189,117,252,127]))=input138 := by rfl
#print axioms address138
def tree138 : Tree := .branch tree129 (.supplied (JGc_TX2_HashBytes.state [235,175,68,146,148,50,230,240,90,237,138,62,236,194,107,145,48,135,75,194,84,203,138,124,153,6,202,37,189,117,252,127]))
theorem root138 : root JFp_SHADigest.digest tree138=value138 := by
  rw [tree138,root,root129]
  exact (congrArg JFp_SHADigest.digest address138).trans hash138
#print axioms root138
theorem shape138 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 13 245760=tree138 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 13 245760)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape129 f g inputs siblings]
  rw [unoccupied f g 12 249856 (by decide),siblings 12 (by decide) 249856 (by decide)]
  rfl
#print axioms shape138
end AspisR1.JHh_C_Gr_M1Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_C_Gr_M1Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input139 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash139.message
def value139 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash139.result
theorem hash139 : JFp_SHADigest.digest input139=value139 := by
  have law := JHe_SHARealization.tree1 ⟨139, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash139
theorem address139 : BinMerkle32Path.nodeInput (children value130 (JGc_TX2_HashBytes.state [177,255,241,39,63,158,40,191,219,173,167,140,60,212,238,89,156,75,131,173,118,46,23,106,164,61,132,56,29,231,180,242]))=input139 := by rfl
#print axioms address139
def tree139 : Tree := .branch tree130 (.supplied (JGc_TX2_HashBytes.state [177,255,241,39,63,158,40,191,219,173,167,140,60,212,238,89,156,75,131,173,118,46,23,106,164,61,132,56,29,231,180,242]))
theorem root139 : root JFp_SHADigest.digest tree139=value139 := by
  rw [tree139,root,root130]
  exact (congrArg JFp_SHADigest.digest address139).trans hash139
#print axioms root139
theorem shape139 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 14 65536=tree139 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 14 65536)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape130 f g inputs siblings]
  rw [unoccupied f g 13 73728 (by decide),siblings 13 (by decide) 73728 (by decide)]
  rfl
#print axioms shape139
def input140 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash140.message
def value140 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash140.result
theorem hash140 : JFp_SHADigest.digest input140=value140 := by
  have law := JHe_SHARealization.tree1 ⟨140, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash140
theorem address140 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [148,97,246,244,46,229,113,211,171,213,134,17,121,11,39,232,115,93,64,237,78,176,97,138,178,248,71,111,201,205,160,225]) value131)=input140 := by rfl
#print axioms address140
def tree140 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [148,97,246,244,46,229,113,211,171,213,134,17,121,11,39,232,115,93,64,237,78,176,97,138,178,248,71,111,201,205,160,225])) tree131
theorem root140 : root JFp_SHADigest.digest tree140=value140 := by
  rw [tree140,root,root131]
  exact (congrArg JFp_SHADigest.digest address140).trans hash140
#print axioms root140
theorem shape140 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 14 81920=tree140 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 14 81920)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 13 81920 (by decide),siblings 13 (by decide) 81920 (by decide)]
  rw [shape131 f g inputs siblings]
  rfl
#print axioms shape140
def input141 : Bytes := JGh_TX2_M1Roots.input171
def value141 : State := JGh_TX2_M1Roots.value171
theorem hash141 : JFp_SHADigest.digest input141=value141 := by
  have law := JHe_SHARealization.tree1 ⟨141, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash141
theorem address141 : BinMerkle32Path.nodeInput (children value132 value133)=input141 := by rfl
#print axioms address141
def tree141 : Tree := .branch tree132 tree133
theorem root141 : root JFp_SHADigest.digest tree141=value141 := by
  rw [tree141,root,root132,root133]
  exact (congrArg JFp_SHADigest.digest address141).trans hash141
#print axioms root141
theorem shape141 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 14 147456=tree141 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 14 147456)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape132 f g inputs siblings]
  rw [shape133 f g inputs siblings]
  rfl
#print axioms shape141
def input142 : Bytes := JGh_TX2_M1Roots.input173
def value142 : State := JGh_TX2_M1Roots.value173
theorem hash142 : JFp_SHADigest.digest input142=value142 := by
  have law := JHe_SHARealization.tree1 ⟨142, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash142
theorem address142 : BinMerkle32Path.nodeInput (children value134 value135)=input142 := by rfl
#print axioms address142
def tree142 : Tree := .branch tree134 tree135
theorem root142 : root JFp_SHADigest.digest tree142=value142 := by
  rw [tree142,root,root134,root135]
  exact (congrArg JFp_SHADigest.digest address142).trans hash142
#print axioms root142
theorem shape142 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 14 180224=tree142 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 14 180224)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape134 f g inputs siblings]
  rw [shape135 f g inputs siblings]
  rfl
#print axioms shape142
def input143 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash143.message
def value143 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash143.result
theorem hash143 : JFp_SHADigest.digest input143=value143 := by
  have law := JHe_SHARealization.tree1 ⟨143, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash143
theorem address143 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [241,9,125,109,23,20,73,46,243,31,183,201,254,168,254,9,17,216,58,151,34,255,100,136,213,89,115,87,251,31,157,167]) value136)=input143 := by rfl
#print axioms address143
def tree143 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [241,9,125,109,23,20,73,46,243,31,183,201,254,168,254,9,17,216,58,151,34,255,100,136,213,89,115,87,251,31,157,167])) tree136
theorem root143 : root JFp_SHADigest.digest tree143=value143 := by
  rw [tree143,root,root136]
  exact (congrArg JFp_SHADigest.digest address143).trans hash143
#print axioms root143
theorem shape143 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 14 196608=tree143 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 14 196608)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 13 196608 (by decide),siblings 13 (by decide) 196608 (by decide)]
  rw [shape136 f g inputs siblings]
  rfl
#print axioms shape143
def input144 : Bytes := JGh_TX2_M1Roots.input174
def value144 : State := JGh_TX2_M1Roots.value174
theorem hash144 : JFp_SHADigest.digest input144=value144 := by
  have law := JHe_SHARealization.tree1 ⟨144, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash144
theorem address144 : BinMerkle32Path.nodeInput (children value137 (JGc_TX2_HashBytes.state [231,175,9,73,193,151,78,114,131,10,124,215,162,10,201,179,141,208,35,230,20,155,240,194,241,32,103,192,199,110,107,27]))=input144 := by rfl
#print axioms address144
def tree144 : Tree := .branch tree137 (.supplied (JGc_TX2_HashBytes.state [231,175,9,73,193,151,78,114,131,10,124,215,162,10,201,179,141,208,35,230,20,155,240,194,241,32,103,192,199,110,107,27]))
theorem root144 : root JFp_SHADigest.digest tree144=value144 := by
  rw [tree144,root,root137]
  exact (congrArg JFp_SHADigest.digest address144).trans hash144
#print axioms root144
theorem shape144 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 14 212992=tree144 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 14 212992)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape137 f g inputs siblings]
  rw [unoccupied f g 13 221184 (by decide),siblings 13 (by decide) 221184 (by decide)]
  rfl
#print axioms shape144
def input145 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash145.message
def value145 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash145.result
theorem hash145 : JFp_SHADigest.digest input145=value145 := by
  have law := JHe_SHARealization.tree1 ⟨145, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash145
theorem address145 : BinMerkle32Path.nodeInput (children value138 (JGc_TX2_HashBytes.state [105,88,192,232,209,36,116,6,166,207,65,248,208,208,199,3,9,32,125,251,202,216,178,45,163,37,132,171,119,243,170,2]))=input145 := by rfl
#print axioms address145
def tree145 : Tree := .branch tree138 (.supplied (JGc_TX2_HashBytes.state [105,88,192,232,209,36,116,6,166,207,65,248,208,208,199,3,9,32,125,251,202,216,178,45,163,37,132,171,119,243,170,2]))
theorem root145 : root JFp_SHADigest.digest tree145=value145 := by
  rw [tree145,root,root138]
  exact (congrArg JFp_SHADigest.digest address145).trans hash145
#print axioms root145
theorem shape145 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 14 245760=tree145 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 14 245760)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape138 f g inputs siblings]
  rw [unoccupied f g 13 253952 (by decide),siblings 13 (by decide) 253952 (by decide)]
  rfl
#print axioms shape145
end AspisR1.JHh_C_Gr_M1Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_C_Gr_M1Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input146 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash146.message
def value146 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash146.result
theorem hash146 : JFp_SHADigest.digest input146=value146 := by
  have law := JHe_SHARealization.tree1 ⟨146, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash146
theorem address146 : BinMerkle32Path.nodeInput (children value139 value140)=input146 := by rfl
#print axioms address146
def tree146 : Tree := .branch tree139 tree140
theorem root146 : root JFp_SHADigest.digest tree146=value146 := by
  rw [tree146,root,root139,root140]
  exact (congrArg JFp_SHADigest.digest address146).trans hash146
#print axioms root146
theorem shape146 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 15 65536=tree146 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 15 65536)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape139 f g inputs siblings]
  rw [shape140 f g inputs siblings]
  rfl
#print axioms shape146
def input147 : Bytes := JGh_TX2_M1Roots.input177
def value147 : State := JGh_TX2_M1Roots.value177
theorem hash147 : JFp_SHADigest.digest input147=value147 := by
  have law := JHe_SHARealization.tree1 ⟨147, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash147
theorem address147 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [77,119,158,98,145,125,73,201,211,192,209,42,9,218,8,172,52,75,152,66,203,147,195,144,242,0,78,78,51,239,33,225]) value141)=input147 := by rfl
#print axioms address147
def tree147 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [77,119,158,98,145,125,73,201,211,192,209,42,9,218,8,172,52,75,152,66,203,147,195,144,242,0,78,78,51,239,33,225])) tree141
theorem root147 : root JFp_SHADigest.digest tree147=value147 := by
  rw [tree147,root,root141]
  exact (congrArg JFp_SHADigest.digest address147).trans hash147
#print axioms root147
theorem shape147 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 15 131072=tree147 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 15 131072)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 14 131072 (by decide),siblings 14 (by decide) 131072 (by decide)]
  rw [shape141 f g inputs siblings]
  rfl
#print axioms shape147
def input148 : Bytes := JGh_TX2_M1Roots.input178
def value148 : State := JGh_TX2_M1Roots.value178
theorem hash148 : JFp_SHADigest.digest input148=value148 := by
  have law := JHe_SHARealization.tree1 ⟨148, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash148
theorem address148 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [157,235,230,58,63,44,109,204,141,127,215,154,149,77,102,74,49,129,237,95,214,147,79,111,35,41,106,166,126,167,43,139]) value142)=input148 := by rfl
#print axioms address148
def tree148 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [157,235,230,58,63,44,109,204,141,127,215,154,149,77,102,74,49,129,237,95,214,147,79,111,35,41,106,166,126,167,43,139])) tree142
theorem root148 : root JFp_SHADigest.digest tree148=value148 := by
  rw [tree148,root,root142]
  exact (congrArg JFp_SHADigest.digest address148).trans hash148
#print axioms root148
theorem shape148 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 15 163840=tree148 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 15 163840)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 14 163840 (by decide),siblings 14 (by decide) 163840 (by decide)]
  rw [shape142 f g inputs siblings]
  rfl
#print axioms shape148
def input149 : Bytes := JGh_TX2_M1Roots.input179
def value149 : State := JGh_TX2_M1Roots.value179
theorem hash149 : JFp_SHADigest.digest input149=value149 := by
  have law := JHe_SHARealization.tree1 ⟨149, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash149
theorem address149 : BinMerkle32Path.nodeInput (children value143 value144)=input149 := by rfl
#print axioms address149
def tree149 : Tree := .branch tree143 tree144
theorem root149 : root JFp_SHADigest.digest tree149=value149 := by
  rw [tree149,root,root143,root144]
  exact (congrArg JFp_SHADigest.digest address149).trans hash149
#print axioms root149
theorem shape149 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 15 196608=tree149 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 15 196608)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape143 f g inputs siblings]
  rw [shape144 f g inputs siblings]
  rfl
#print axioms shape149
def input150 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash150.message
def value150 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash150.result
theorem hash150 : JFp_SHADigest.digest input150=value150 := by
  have law := JHe_SHARealization.tree1 ⟨150, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash150
theorem address150 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [103,29,162,204,20,167,88,231,167,150,223,135,176,35,230,214,140,125,223,169,142,173,29,189,226,61,203,233,25,171,3,193]) value145)=input150 := by rfl
#print axioms address150
def tree150 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [103,29,162,204,20,167,88,231,167,150,223,135,176,35,230,214,140,125,223,169,142,173,29,189,226,61,203,233,25,171,3,193])) tree145
theorem root150 : root JFp_SHADigest.digest tree150=value150 := by
  rw [tree150,root,root145]
  exact (congrArg JFp_SHADigest.digest address150).trans hash150
#print axioms root150
theorem shape150 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 15 229376=tree150 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 15 229376)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 14 229376 (by decide),siblings 14 (by decide) 229376 (by decide)]
  rw [shape145 f g inputs siblings]
  rfl
#print axioms shape150
end AspisR1.JHh_C_Gr_M1Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_C_Gr_M1Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input151 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash151.message
def value151 : State := JFp_SHADigest.output JHe_C_Gr_M1.Hash151.result
theorem hash151 : JFp_SHADigest.digest input151=value151 := by
  have law := JHe_SHARealization.tree1 ⟨151, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash151
theorem address151 : BinMerkle32Path.nodeInput (children value146 (JGc_TX2_HashBytes.state [169,24,176,242,33,202,155,23,158,103,13,74,131,251,160,53,65,59,10,90,129,75,172,213,105,163,148,32,103,32,15,160]))=input151 := by rfl
#print axioms address151
def tree151 : Tree := .branch tree146 (.supplied (JGc_TX2_HashBytes.state [169,24,176,242,33,202,155,23,158,103,13,74,131,251,160,53,65,59,10,90,129,75,172,213,105,163,148,32,103,32,15,160]))
theorem root151 : root JFp_SHADigest.digest tree151=value151 := by
  rw [tree151,root,root146]
  exact (congrArg JFp_SHADigest.digest address151).trans hash151
#print axioms root151
theorem shape151 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 16 65536=tree151 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 16 65536)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape146 f g inputs siblings]
  rw [unoccupied f g 15 98304 (by decide),siblings 15 (by decide) 98304 (by decide)]
  rfl
#print axioms shape151
def input152 : Bytes := JGh_TX2_M1Roots.input181
def value152 : State := JGh_TX2_M1Roots.value181
theorem hash152 : JFp_SHADigest.digest input152=value152 := by
  have law := JHe_SHARealization.tree1 ⟨152, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash152
theorem address152 : BinMerkle32Path.nodeInput (children value147 value148)=input152 := by rfl
#print axioms address152
def tree152 : Tree := .branch tree147 tree148
theorem root152 : root JFp_SHADigest.digest tree152=value152 := by
  rw [tree152,root,root147,root148]
  exact (congrArg JFp_SHADigest.digest address152).trans hash152
#print axioms root152
theorem shape152 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 16 131072=tree152 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 16 131072)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape147 f g inputs siblings]
  rw [shape148 f g inputs siblings]
  rfl
#print axioms shape152
def input153 : Bytes := JGh_TX2_M1Roots.input182
def value153 : State := JGh_TX2_M1Roots.value182
theorem hash153 : JFp_SHADigest.digest input153=value153 := by
  have law := JHe_SHARealization.tree1 ⟨153, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash153
theorem address153 : BinMerkle32Path.nodeInput (children value149 value150)=input153 := by rfl
#print axioms address153
def tree153 : Tree := .branch tree149 tree150
theorem root153 : root JFp_SHADigest.digest tree153=value153 := by
  rw [tree153,root,root149,root150]
  exact (congrArg JFp_SHADigest.digest address153).trans hash153
#print axioms root153
theorem shape153 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 16 196608=tree153 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 16 196608)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape149 f g inputs siblings]
  rw [shape150 f g inputs siblings]
  rfl
#print axioms shape153
end AspisR1.JHh_C_Gr_M1Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_C_Gr_M1Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input154 : Bytes := JGh_TX2_M1Roots.input183
def value154 : State := JGh_TX2_M1Roots.value183
theorem hash154 : JFp_SHADigest.digest input154=value154 := by
  have law := JHe_SHARealization.tree1 ⟨154, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash154
theorem address154 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [141,210,29,143,172,113,121,140,232,80,9,198,209,48,160,240,216,160,117,117,21,164,211,65,104,173,187,170,81,120,182,252]) value151)=input154 := by rfl
#print axioms address154
def tree154 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [141,210,29,143,172,113,121,140,232,80,9,198,209,48,160,240,216,160,117,117,21,164,211,65,104,173,187,170,81,120,182,252])) tree151
theorem root154 : root JFp_SHADigest.digest tree154=value154 := by
  rw [tree154,root,root151]
  exact (congrArg JFp_SHADigest.digest address154).trans hash154
#print axioms root154
theorem shape154 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 17 0=tree154 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 17 0)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 16 0 (by decide),siblings 16 (by decide) 0 (by decide)]
  rw [shape151 f g inputs siblings]
  rfl
#print axioms shape154
def input155 : Bytes := JGh_TX2_M1Roots.input184
def value155 : State := JGh_TX2_M1Roots.value184
theorem hash155 : JFp_SHADigest.digest input155=value155 := by
  have law := JHe_SHARealization.tree1 ⟨155, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash155
theorem address155 : BinMerkle32Path.nodeInput (children value152 value153)=input155 := by rfl
#print axioms address155
def tree155 : Tree := .branch tree152 tree153
theorem root155 : root JFp_SHADigest.digest tree155=value155 := by
  rw [tree155,root,root152,root153]
  exact (congrArg JFp_SHADigest.digest address155).trans hash155
#print axioms root155
theorem shape155 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 17 131072=tree155 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 17 131072)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape152 f g inputs siblings]
  rw [shape153 f g inputs siblings]
  rfl
#print axioms shape155
end AspisR1.JHh_C_Gr_M1Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_C_Gr_M1Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input156 : Bytes := JGh_TX2_M1Roots.input185
def value156 : State := JGh_TX2_M1Roots.value185
theorem hash156 : JFp_SHADigest.digest input156=value156 := by
  have law := JHe_SHARealization.tree1 ⟨156, by decide⟩
  dsimp only [JHe_SHAInputs1.input,JHe_SHAInputs1.expected] at law
  exact law
#print axioms hash156
theorem address156 : BinMerkle32Path.nodeInput (children value154 value155)=input156 := by rfl
#print axioms address156
def tree156 : Tree := .branch tree154 tree155
theorem root156 : root JFp_SHADigest.digest tree156=value156 := by
  rw [tree156,root,root154,root155]
  exact (congrArg JFp_SHADigest.digest address156).trans hash156
#print axioms root156
theorem shape156 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 18 0=tree156 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 18 0)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape154 f g inputs siblings]
  rw [shape155 f g inputs siblings]
  rfl
#print axioms shape156
end AspisR1.JHh_C_Gr_M1Roots
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_C_Gr_M1Root
open Aeneas Aeneas.Std
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiBuild OracleDecisionMultiTree JHh_C_Gr_M1Roots

def retainedRoot : State := JGh_TX2_M1Root.retainedRoot

theorem value_eq : value156=retainedRoot := by
  funext i
  fin_cases i <;> rfl
#print axioms value_eq

theorem source (f : Nat → Bytes) (g : Nat → Nat → State)
    (inputs : InputLaw f) (siblings : SiblingLaw g) :
    root JFp_SHADigest.digest (build indices f g 18 0)=retainedRoot := by
  rw [shape156 f g inputs siblings,root156,value_eq]
#print axioms source

theorem selected_queries : OraclePortSelectedDraft.selected
    (Port4B_KeyInstall.queries JFo_Prepared.value.queries) 0 1=indices := rfl
#print axioms selected_queries

theorem inhabited : ∃ (f : Nat → Bytes) (g : Nat → Nat → State),
    InputLaw f ∧ SiblingLaw g ∧
    root JFp_SHADigest.digest (build indices f g 18 0)=retainedRoot :=
  ⟨inputAt,siblingAt,(by intro b _;rfl),(by intro h _ b _;rfl),
    source inputAt siblingAt (by intro b _;rfl) (by intro h _ b _;rfl)⟩
#print axioms inhabited
end AspisR1.JHh_C_Gr_M1Root
end
end
