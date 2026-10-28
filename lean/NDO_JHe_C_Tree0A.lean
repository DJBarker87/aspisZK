import NDO_JGc_TX2_ByteAppend
import NDO_JGc_TX2_HashBytes
import NDO_JGe_View
import NDO_JGf_TX2_M0Root
import NDO_JHe_SHARealization
import OracleDecisionMultiBuild
section
variable [sha : AspisR1.JHe_SHARealization]
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_C_Gr_M0Roots
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
    | 65592 => JGc_TX2_HashBytes.state [138,12,78,4,29,195,175,124,49,12,183,253,137,178,1,172,57,105,147,139,13,27,199,21,103,254,125,5,89,218,213,42]
    | 93498 => JGc_TX2_HashBytes.state [0,155,210,135,10,10,36,139,250,61,153,156,199,68,178,96,3,25,83,60,150,7,110,64,212,120,34,32,128,70,85,4]
    | 147528 => JGc_TX2_HashBytes.state [30,206,97,181,53,81,203,161,54,188,202,14,118,67,232,27,234,26,123,152,61,193,146,253,243,71,30,207,164,232,190,24]
    | 159812 => JGc_TX2_HashBytes.state [26,195,186,240,93,5,49,188,135,179,131,176,52,102,146,74,221,99,76,219,108,88,144,61,125,193,25,38,125,58,141,31]
    | 183858 => JGc_TX2_HashBytes.state [40,252,149,36,166,192,162,64,101,20,54,49,63,59,166,85,31,38,36,0,99,178,228,189,116,169,252,141,90,193,181,51]
    | 192316 => JGc_TX2_HashBytes.state [197,135,76,25,172,180,98,84,70,211,112,237,137,36,20,194,104,104,114,136,240,147,181,141,121,72,73,200,110,2,159,172]
    | 193092 => JGc_TX2_HashBytes.state [221,112,50,50,72,39,34,4,52,173,152,99,96,65,187,155,71,131,8,35,206,215,205,144,48,160,238,66,13,85,203,152]
    | 209370 => JGc_TX2_HashBytes.state [98,52,222,92,145,216,45,125,153,221,152,251,15,144,137,56,230,174,11,161,151,249,216,185,201,144,36,136,166,73,211,28]
    | 216822 => JGc_TX2_HashBytes.state [60,239,18,111,191,102,204,179,135,84,19,39,39,192,93,82,21,159,129,98,135,224,200,173,184,187,89,90,164,245,183,28]
    | 245898 => JGc_TX2_HashBytes.state [2,236,210,68,67,97,179,9,220,150,3,95,165,1,185,29,159,221,4,51,208,1,32,211,224,128,53,137,65,4,60,189]
    | _ => JGc_TX2_HashBytes.state []
  | 1 => match base with
    | 65594 => JGc_TX2_HashBytes.state [129,145,123,71,112,75,255,207,218,182,51,10,70,248,80,186,22,215,227,161,95,73,153,136,175,88,40,150,245,11,93,135]
    | 93496 => JGc_TX2_HashBytes.state [6,77,240,190,14,215,62,129,49,91,41,245,106,187,182,190,199,41,143,109,39,181,18,239,169,207,77,190,62,185,232,101]
    | 147530 => JGc_TX2_HashBytes.state [171,86,16,208,136,220,221,143,53,10,68,139,211,174,170,254,152,13,118,166,208,178,197,65,145,118,216,18,233,52,60,82]
    | 159814 => JGc_TX2_HashBytes.state [248,126,21,210,211,142,137,180,125,82,222,125,142,123,90,165,35,12,113,99,134,20,208,119,121,59,66,164,58,120,127,115]
    | 183856 => JGc_TX2_HashBytes.state [20,10,255,79,9,214,152,90,126,242,155,160,41,116,223,232,3,49,161,115,34,79,44,109,72,141,100,126,207,51,141,176]
    | 192318 => JGc_TX2_HashBytes.state [6,1,204,64,31,38,61,84,24,165,208,174,223,189,74,4,143,235,84,186,217,122,203,71,143,71,240,110,239,79,13,27]
    | 193094 => JGc_TX2_HashBytes.state [111,19,141,1,38,225,65,248,212,38,27,65,9,175,117,232,105,8,170,194,129,33,180,80,1,242,239,11,227,222,81,248]
    | 209368 => JGc_TX2_HashBytes.state [17,75,22,191,103,116,8,247,251,193,12,81,68,91,193,167,193,237,72,81,121,112,92,183,215,119,32,4,8,7,113,34]
    | 216820 => JGc_TX2_HashBytes.state [198,203,234,73,173,119,179,225,134,57,111,62,249,250,244,3,81,81,144,231,109,135,167,231,203,175,0,17,199,209,221,204]
    | 245896 => JGc_TX2_HashBytes.state [250,169,77,120,228,7,6,220,115,87,209,195,16,51,10,191,223,81,107,87,210,1,161,60,20,21,81,135,25,24,132,100]
    | _ => JGc_TX2_HashBytes.state []
  | 2 => match base with
    | 65596 => JGc_TX2_HashBytes.state [113,228,45,241,12,21,223,82,189,127,50,66,112,86,41,131,49,39,172,121,205,231,86,254,118,88,129,50,88,205,75,198]
    | 93500 => JGc_TX2_HashBytes.state [170,237,127,75,233,122,51,70,203,215,35,59,216,223,49,175,17,58,145,50,79,33,120,37,250,117,78,166,106,96,202,40]
    | 147532 => JGc_TX2_HashBytes.state [90,223,103,38,163,10,29,51,156,251,237,216,23,111,164,147,90,200,6,231,84,70,65,96,193,254,203,58,211,238,139,7]
    | 159808 => JGc_TX2_HashBytes.state [164,239,132,46,197,102,247,125,165,37,99,49,87,147,68,162,92,105,189,105,44,74,146,27,210,103,23,0,30,154,233,18]
    | 183860 => JGc_TX2_HashBytes.state [113,219,88,1,248,185,66,167,21,201,234,44,1,193,119,242,149,64,217,87,214,0,169,200,148,84,216,185,197,164,151,244]
    | 192312 => JGc_TX2_HashBytes.state [131,150,20,119,138,171,247,50,130,133,151,200,22,17,142,182,50,103,254,31,237,67,123,106,214,235,120,126,203,58,12,15]
    | 193088 => JGc_TX2_HashBytes.state [153,129,24,20,176,39,22,236,211,202,212,187,140,77,94,63,250,21,206,77,77,113,181,24,141,109,242,160,198,227,5,196]
    | 209372 => JGc_TX2_HashBytes.state [101,139,27,149,235,32,119,159,21,175,34,168,214,38,192,112,138,28,226,156,191,27,122,66,141,229,44,205,255,101,185,86]
    | 216816 => JGc_TX2_HashBytes.state [97,100,140,122,23,30,20,241,117,108,230,40,3,90,18,209,195,137,51,245,94,157,2,13,40,206,120,166,203,53,10,70]
    | 245900 => JGc_TX2_HashBytes.state [14,156,11,58,98,11,10,23,106,162,4,80,205,20,195,48,179,221,204,9,0,83,249,174,34,4,190,244,166,20,144,192]
    | _ => JGc_TX2_HashBytes.state []
  | 3 => match base with
    | 65584 => JGc_TX2_HashBytes.state [237,101,153,156,115,150,6,23,215,162,34,228,173,42,146,106,223,172,140,115,117,138,77,161,26,92,89,55,88,255,0,59]
    | 93488 => JGc_TX2_HashBytes.state [37,244,135,117,26,54,233,244,102,147,224,254,200,10,248,244,195,200,20,185,169,184,56,177,168,169,22,254,134,167,69,172]
    | 147520 => JGc_TX2_HashBytes.state [159,155,131,105,178,86,59,104,185,104,3,52,240,166,65,12,166,115,194,190,140,181,58,92,75,125,4,58,182,78,182,117]
    | 159816 => JGc_TX2_HashBytes.state [184,1,99,242,168,187,235,249,27,44,146,36,138,238,109,46,110,208,60,198,44,245,5,255,142,243,124,75,122,28,81,44]
    | 183864 => JGc_TX2_HashBytes.state [249,155,11,53,79,5,46,47,174,40,100,160,232,197,150,206,57,65,60,151,77,221,228,49,146,47,224,242,31,205,112,53]
    | 192304 => JGc_TX2_HashBytes.state [238,230,76,71,245,181,227,67,63,205,182,151,40,139,104,248,128,252,163,105,140,161,180,90,61,195,7,172,203,134,85,243]
    | 193096 => JGc_TX2_HashBytes.state [236,70,66,207,227,98,249,31,237,39,77,55,123,239,84,213,237,51,12,241,116,71,72,165,63,45,61,196,132,73,13,35]
    | 209360 => JGc_TX2_HashBytes.state [91,225,147,229,114,51,191,240,38,62,23,3,232,35,207,56,1,62,142,130,179,3,146,218,181,241,176,104,168,124,104,231]
    | 216824 => JGc_TX2_HashBytes.state [145,243,79,135,184,204,125,182,43,245,47,168,35,84,132,21,100,19,63,164,130,24,235,181,69,88,56,166,229,252,70,120]
    | 245888 => JGc_TX2_HashBytes.state [252,69,117,223,75,28,193,245,113,139,104,231,98,230,139,109,224,152,128,86,124,122,36,40,153,175,49,45,182,138,161,172]
    | _ => JGc_TX2_HashBytes.state []
  | 4 => match base with
    | 65568 => JGc_TX2_HashBytes.state [236,29,86,76,30,67,12,237,81,110,150,232,163,108,233,233,80,159,68,44,137,93,213,2,246,186,157,124,230,83,136,227]
    | 93472 => JGc_TX2_HashBytes.state [247,52,6,98,251,50,13,174,91,242,73,132,225,30,14,57,46,158,63,2,190,121,132,15,58,169,20,205,208,200,105,57]
    | 147536 => JGc_TX2_HashBytes.state [47,45,200,13,66,168,117,82,224,239,90,35,215,108,210,255,88,3,40,35,217,209,147,174,210,246,44,160,81,239,153,153]
    | 159824 => JGc_TX2_HashBytes.state [146,13,29,171,138,255,137,186,12,109,8,62,51,250,197,131,20,22,189,188,183,99,33,0,28,151,225,92,193,93,19,97]
    | 183840 => JGc_TX2_HashBytes.state [179,71,254,154,5,86,67,35,162,58,89,34,52,121,77,71,180,240,121,174,98,142,50,217,93,201,208,91,199,253,90,108]
    | 192288 => JGc_TX2_HashBytes.state [38,17,228,198,172,26,2,118,104,186,59,10,202,180,122,6,153,83,58,205,40,8,165,125,33,207,147,16,114,32,156,118]
    | 193104 => JGc_TX2_HashBytes.state [174,64,125,54,103,77,213,103,170,28,57,102,173,92,85,231,178,203,38,164,60,235,247,116,32,127,10,7,79,88,232,33]
    | 209344 => JGc_TX2_HashBytes.state [162,83,182,157,31,13,19,175,77,247,91,65,123,57,95,74,245,247,220,188,222,222,38,42,24,110,87,188,135,58,50,173]
    | 216800 => JGc_TX2_HashBytes.state [146,40,112,149,161,135,34,145,67,59,110,211,60,96,206,150,59,192,248,67,117,8,78,102,40,34,154,21,23,151,238,154]
    | 245904 => JGc_TX2_HashBytes.state [148,49,202,250,248,38,32,82,139,58,215,125,191,197,113,97,118,28,250,196,119,217,110,64,141,12,92,14,240,146,144,157]
    | _ => JGc_TX2_HashBytes.state []
  | 5 => match base with
    | 65536 => JGc_TX2_HashBytes.state [216,17,255,192,221,66,225,78,57,192,131,236,153,46,142,77,41,52,179,22,166,119,175,6,80,2,94,166,171,119,89,64]
    | 93440 => JGc_TX2_HashBytes.state [204,48,251,61,224,226,231,54,110,116,192,65,229,239,85,15,141,34,33,130,96,59,83,197,192,43,247,186,251,77,95,136]
    | 147552 => JGc_TX2_HashBytes.state [204,210,70,143,235,140,144,248,219,78,146,18,143,241,159,115,100,67,99,77,124,5,73,9,122,59,54,61,178,235,1,45]
    | 159840 => JGc_TX2_HashBytes.state [92,145,193,181,163,4,241,41,44,66,156,75,123,119,113,146,69,183,16,241,54,8,84,133,199,46,217,50,3,136,195,213]
    | 183808 => JGc_TX2_HashBytes.state [177,116,4,114,61,106,88,108,118,62,192,61,211,197,68,169,43,161,77,216,92,76,54,202,145,17,143,238,105,129,100,173]
    | 192256 => JGc_TX2_HashBytes.state [231,195,10,19,115,54,82,117,227,102,218,64,54,252,89,187,223,148,244,77,235,96,151,171,64,192,43,182,10,220,40,79]
    | 193120 => JGc_TX2_HashBytes.state [151,95,38,140,31,5,121,26,212,129,37,16,148,199,129,176,150,84,199,90,102,60,240,239,124,65,170,220,30,127,98,162]
    | 209376 => JGc_TX2_HashBytes.state [241,64,215,200,101,21,188,206,149,131,130,157,92,41,217,33,232,168,191,86,174,113,121,90,134,82,2,138,192,43,11,148]
    | 216768 => JGc_TX2_HashBytes.state [154,13,206,49,223,9,254,76,182,88,42,161,203,130,30,27,176,4,101,162,115,71,35,86,137,49,8,23,137,228,38,97]
    | 245920 => JGc_TX2_HashBytes.state [246,74,169,178,195,143,37,247,203,214,169,5,137,26,200,158,2,112,37,14,0,58,128,70,240,102,164,2,132,160,95,14]
    | _ => JGc_TX2_HashBytes.state []
  | 6 => match base with
    | 65600 => JGc_TX2_HashBytes.state [6,240,144,10,89,181,146,35,19,69,34,102,224,239,82,169,126,228,144,157,213,100,223,158,185,74,215,93,123,233,23,161]
    | 93504 => JGc_TX2_HashBytes.state [90,6,145,42,210,19,190,106,99,39,107,82,176,83,131,93,159,218,108,61,236,10,133,7,20,128,169,78,170,230,90,165]
    | 147456 => JGc_TX2_HashBytes.state [196,128,247,200,205,132,186,20,133,103,68,116,144,157,48,190,208,40,165,211,155,245,88,90,127,113,249,133,5,38,245,231]
    | 159744 => JGc_TX2_HashBytes.state [2,49,107,237,24,224,109,245,28,116,185,193,147,100,59,21,17,156,87,57,186,102,113,213,3,126,197,123,26,250,39,128]
    | 183872 => JGc_TX2_HashBytes.state [136,31,229,129,117,15,123,172,12,255,204,60,56,41,146,141,133,147,183,231,229,23,88,42,114,153,55,180,204,108,193,174]
    | 192320 => JGc_TX2_HashBytes.state [34,30,57,86,102,193,213,112,204,200,212,44,184,202,213,35,17,43,57,142,205,70,168,207,70,167,54,101,73,187,97,202]
    | 193024 => JGc_TX2_HashBytes.state [92,210,92,203,65,9,235,116,179,182,0,221,48,101,150,142,75,48,236,28,93,37,5,154,73,46,86,46,88,149,55,187]
    | 209280 => JGc_TX2_HashBytes.state [205,165,38,151,111,198,79,116,206,226,67,245,236,196,187,100,133,50,31,120,57,157,51,233,222,159,161,218,172,204,11,66]
    | 216704 => JGc_TX2_HashBytes.state [226,108,77,28,131,136,7,58,77,240,220,71,105,254,22,209,107,74,73,188,176,248,183,95,174,54,121,81,95,90,24,102]
    | 245952 => JGc_TX2_HashBytes.state [87,28,17,1,43,43,239,80,58,175,254,64,102,59,168,121,219,185,145,108,206,67,71,30,115,173,159,96,166,56,54,73]
    | _ => JGc_TX2_HashBytes.state []
  | 7 => match base with
    | 65664 => JGc_TX2_HashBytes.state [77,170,189,130,235,22,61,148,149,65,163,235,1,168,255,7,23,41,163,194,92,20,52,96,214,215,10,79,81,125,23,74]
    | 93568 => JGc_TX2_HashBytes.state [220,4,163,99,213,83,228,35,211,78,46,27,57,83,108,166,235,71,20,58,174,254,18,51,47,16,101,29,62,46,59,127]
    | 147584 => JGc_TX2_HashBytes.state [8,32,93,135,247,254,167,22,175,205,245,1,51,185,169,99,158,32,144,204,248,6,73,82,86,253,11,31,112,23,182,248]
    | 159872 => JGc_TX2_HashBytes.state [237,7,29,17,196,126,123,186,28,187,171,89,156,231,137,55,83,50,16,209,36,156,194,167,84,36,109,35,86,123,184,82]
    | 183936 => JGc_TX2_HashBytes.state [164,143,95,212,102,248,18,5,14,206,35,160,137,216,216,140,138,220,155,8,95,80,232,194,90,93,3,211,167,239,202,54]
    | 192384 => JGc_TX2_HashBytes.state [112,33,7,3,28,71,221,2,47,93,159,111,101,209,164,115,182,37,12,24,179,5,186,191,241,44,19,167,238,76,32,192]
    | 193152 => JGc_TX2_HashBytes.state [74,175,62,170,208,166,232,20,189,64,80,118,215,50,80,8,224,151,209,81,20,7,185,85,124,62,24,188,176,43,92,225]
    | 209152 => JGc_TX2_HashBytes.state [218,253,65,240,172,229,138,129,76,204,176,47,148,25,169,129,220,198,33,211,14,132,216,254,101,36,143,228,205,218,132,45]
    | 216576 => JGc_TX2_HashBytes.state [92,111,165,106,142,29,249,211,6,148,240,59,145,1,129,21,239,41,72,97,151,216,109,27,177,211,241,204,132,133,92,249]
    | 245760 => JGc_TX2_HashBytes.state [15,149,178,185,103,188,80,183,213,234,175,109,95,91,156,29,122,205,226,127,154,135,172,211,157,76,137,128,192,230,142,182]
    | _ => JGc_TX2_HashBytes.state []
  | 8 => match base with
    | 65792 => JGc_TX2_HashBytes.state [113,23,49,153,65,62,50,121,121,134,77,85,4,221,172,58,119,143,25,248,30,111,211,227,9,191,95,71,39,81,225,50]
    | 93184 => JGc_TX2_HashBytes.state [17,86,79,88,53,63,109,64,216,191,11,30,55,109,89,48,69,42,142,22,51,233,130,145,169,63,100,38,75,249,74,19]
    | 147712 => JGc_TX2_HashBytes.state [226,155,182,235,137,88,156,193,14,203,121,8,103,202,235,239,155,117,229,172,214,169,41,35,14,166,228,96,191,226,79,63]
    | 160000 => JGc_TX2_HashBytes.state [126,121,251,104,220,255,47,155,0,110,75,75,75,176,125,193,113,66,44,179,9,60,208,17,238,130,66,26,194,98,247,255]
    | 184064 => JGc_TX2_HashBytes.state [158,176,11,125,66,96,99,8,73,93,247,85,166,153,219,250,17,121,222,96,4,149,255,161,250,23,46,233,243,21,255,119]
    | 192000 => JGc_TX2_HashBytes.state [207,177,176,60,127,81,118,135,169,148,236,21,219,140,173,74,233,123,232,214,172,56,152,55,156,176,4,122,1,49,209,83]
    | 193280 => JGc_TX2_HashBytes.state [65,182,123,189,84,7,216,217,132,96,18,74,118,7,3,237,94,9,129,18,202,71,166,195,20,119,229,148,187,131,19,241]
    | 208896 => JGc_TX2_HashBytes.state [151,189,242,15,48,2,126,127,42,140,208,198,249,228,165,254,222,43,136,1,116,49,161,30,227,32,117,1,201,85,56,26]
    | 216832 => JGc_TX2_HashBytes.state [46,78,225,61,74,143,106,41,11,1,157,44,41,247,155,126,43,181,1,160,152,29,224,187,122,141,106,211,167,157,239,161]
    | 246016 => JGc_TX2_HashBytes.state [8,249,218,86,52,33,101,166,203,237,91,36,157,221,19,10,53,117,89,94,91,68,66,227,193,115,151,105,136,220,126,108]
    | _ => JGc_TX2_HashBytes.state []
  | 9 => match base with
    | 66048 => JGc_TX2_HashBytes.state [23,74,195,49,213,135,245,27,57,199,58,222,148,196,183,123,71,5,192,127,140,213,208,209,54,153,86,127,135,105,132,180]
    | 93696 => JGc_TX2_HashBytes.state [247,170,236,136,32,227,215,1,30,170,171,104,222,196,102,119,141,43,224,250,73,121,228,110,63,169,195,18,64,55,103,111]
    | 147968 => JGc_TX2_HashBytes.state [190,108,13,171,84,192,94,96,227,48,105,48,244,245,190,168,224,83,16,169,249,226,55,97,180,229,154,227,86,36,50,122]
    | 160256 => JGc_TX2_HashBytes.state [157,66,177,205,179,25,156,253,216,204,238,141,248,146,126,57,146,197,187,130,191,130,41,226,29,137,114,88,159,239,90,188]
    | 183296 => JGc_TX2_HashBytes.state [79,115,19,153,165,205,224,136,61,186,168,120,162,67,201,141,134,174,172,243,21,240,241,100,42,229,53,233,153,170,42,41]
    | 191488 => JGc_TX2_HashBytes.state [148,43,99,22,57,180,71,36,176,106,37,117,42,190,120,213,40,143,126,3,58,186,68,221,194,74,60,125,229,230,106,79]
    | 192512 => JGc_TX2_HashBytes.state [207,102,135,191,134,26,82,182,249,62,205,164,72,118,227,234,90,100,188,183,151,160,216,216,200,245,4,24,126,19,178,5]
    | 209408 => JGc_TX2_HashBytes.state [136,24,60,241,94,194,126,24,120,244,56,48,145,68,42,168,200,103,87,128,189,66,104,116,209,245,141,65,97,81,150,11]
    | 216064 => JGc_TX2_HashBytes.state [236,224,3,7,229,22,125,66,186,131,47,131,187,123,43,166,14,188,255,80,197,222,226,154,83,187,231,109,201,152,99,74]
    | 246272 => JGc_TX2_HashBytes.state [129,168,53,62,31,143,67,207,71,169,96,123,137,17,208,1,3,164,237,62,64,109,62,71,117,71,184,169,224,169,104,142]
    | _ => JGc_TX2_HashBytes.state []
  | 10 => match base with
    | 66560 => JGc_TX2_HashBytes.state [152,162,255,196,212,132,122,99,218,255,12,162,24,58,6,29,109,82,79,82,141,97,174,54,239,110,201,1,108,154,177,68]
    | 92160 => JGc_TX2_HashBytes.state [241,229,149,152,170,27,18,61,206,161,98,30,225,40,233,53,46,62,50,48,254,208,247,99,208,150,81,200,50,240,48,143]
    | 148480 => JGc_TX2_HashBytes.state [207,160,0,107,107,203,186,65,189,180,20,58,15,97,7,28,17,81,82,78,101,147,184,188,37,229,216,233,181,44,255,192]
    | 160768 => JGc_TX2_HashBytes.state [123,0,162,188,126,191,227,58,109,189,247,38,102,61,157,69,230,4,19,213,18,43,156,113,160,76,253,162,235,123,98,2]
    | 182272 => JGc_TX2_HashBytes.state [26,34,190,23,233,18,66,255,141,224,173,247,208,54,188,241,221,59,100,97,57,196,21,248,129,34,192,76,118,155,221,240]
    | 190464 => JGc_TX2_HashBytes.state [187,161,232,81,61,204,163,255,108,96,207,42,203,160,95,178,216,58,192,25,156,191,241,239,172,147,29,95,154,104,197,242]
    | 193536 => JGc_TX2_HashBytes.state [112,136,211,124,72,204,53,180,236,108,229,56,210,88,160,196,172,44,115,159,237,211,216,230,73,10,77,132,61,136,48,224]
    | 209920 => JGc_TX2_HashBytes.state [68,125,166,81,87,6,116,93,85,44,114,64,254,221,200,45,38,25,196,77,234,200,255,231,247,107,222,180,48,23,31,85]
    | 215040 => JGc_TX2_HashBytes.state [77,126,21,65,26,159,97,38,195,165,185,168,141,30,194,190,83,101,161,199,214,33,229,162,241,59,159,235,156,208,67,0]
    | 246784 => JGc_TX2_HashBytes.state [119,215,118,217,83,7,90,172,138,108,205,252,152,230,120,183,250,105,16,42,20,115,89,179,235,222,70,56,78,50,213,22]
    | _ => JGc_TX2_HashBytes.state []
  | 11 => match base with
    | 67584 => JGc_TX2_HashBytes.state [164,65,78,40,106,51,231,38,125,149,75,249,27,93,238,7,155,254,36,78,118,136,30,42,179,250,247,120,7,81,21,144]
    | 90112 => JGc_TX2_HashBytes.state [211,245,58,70,112,158,59,164,73,134,77,204,94,119,107,22,183,105,32,45,41,61,170,17,107,25,88,255,149,122,164,95]
    | 149504 => JGc_TX2_HashBytes.state [202,64,14,6,35,96,78,97,222,124,133,255,162,222,235,186,63,243,32,144,64,134,253,43,104,226,220,66,124,185,92,7]
    | 161792 => JGc_TX2_HashBytes.state [247,131,116,212,93,146,215,2,194,179,95,254,35,17,63,19,206,90,55,80,187,155,124,170,167,224,151,27,162,66,130,234]
    | 180224 => JGc_TX2_HashBytes.state [210,253,93,83,135,24,182,107,129,24,45,138,60,15,178,254,10,77,18,68,97,47,12,113,104,75,135,148,129,15,201,143]
    | 188416 => JGc_TX2_HashBytes.state [108,30,109,110,34,215,172,38,88,37,207,120,123,70,8,40,222,202,101,229,33,117,10,142,69,118,38,35,142,15,136,99]
    | 194560 => JGc_TX2_HashBytes.state [163,133,73,137,234,254,224,77,43,180,89,181,80,182,68,145,168,49,120,172,255,240,170,6,191,185,169,251,210,212,116,243]
    | 210944 => JGc_TX2_HashBytes.state [129,75,194,226,75,93,208,230,67,98,126,175,55,174,113,122,34,52,245,123,168,194,155,56,57,111,31,104,119,113,135,71]
    | 212992 => JGc_TX2_HashBytes.state [56,117,174,192,243,180,43,166,2,52,80,21,16,203,229,105,85,214,216,157,123,230,248,209,219,21,217,60,60,150,184,141]
    | 247808 => JGc_TX2_HashBytes.state [109,231,155,150,47,42,48,122,18,218,72,65,211,238,180,205,145,47,143,73,158,94,97,67,253,155,2,166,178,50,203,27]
    | _ => JGc_TX2_HashBytes.state []
  | 12 => match base with
    | 69632 => JGc_TX2_HashBytes.state [254,14,130,135,247,205,115,79,107,166,89,198,117,201,141,89,5,159,55,163,8,155,248,77,113,14,97,138,39,216,58,208]
    | 94208 => JGc_TX2_HashBytes.state [66,225,29,27,146,87,4,138,36,32,56,196,112,123,143,15,189,101,254,171,108,124,109,6,10,176,21,23,227,251,248,124]
    | 151552 => JGc_TX2_HashBytes.state [211,48,75,83,168,253,130,42,18,106,192,164,216,10,63,11,154,197,231,229,193,137,184,83,8,108,208,85,178,162,241,238]
    | 155648 => JGc_TX2_HashBytes.state [188,195,79,74,213,254,47,21,205,195,209,166,40,141,13,9,97,84,152,93,102,191,158,16,165,158,96,183,21,248,100,55]
    | 184320 => JGc_TX2_HashBytes.state [187,76,51,74,59,158,50,38,87,85,221,77,230,156,105,93,240,119,203,74,247,195,29,178,103,62,94,105,26,121,227,113]
    | 204800 => JGc_TX2_HashBytes.state [73,20,30,234,180,192,147,217,52,97,111,104,183,231,180,130,207,5,13,223,218,43,82,64,97,51,35,212,32,222,55,133]
    | 217088 => JGc_TX2_HashBytes.state [216,39,125,52,179,150,49,41,23,46,71,20,106,158,77,0,176,105,197,0,58,234,126,198,61,27,243,66,155,192,133,151]
    | 249856 => JGc_TX2_HashBytes.state [24,83,241,162,249,154,230,253,165,145,84,5,188,201,216,39,216,112,35,240,228,235,23,16,186,131,61,83,162,137,67,145]
    | _ => JGc_TX2_HashBytes.state []
  | 13 => match base with
    | 73728 => JGc_TX2_HashBytes.state [223,231,93,243,187,222,217,220,41,38,7,106,101,167,239,80,245,56,246,60,210,149,142,25,64,43,210,121,95,194,190,127]
    | 81920 => JGc_TX2_HashBytes.state [229,54,3,47,115,163,190,8,7,45,5,100,244,76,80,249,22,225,43,200,84,178,81,224,91,144,25,21,23,167,131,241]
    | 196608 => JGc_TX2_HashBytes.state [213,15,157,39,47,184,77,71,127,84,62,42,216,50,94,250,30,227,120,165,40,142,232,125,140,191,184,70,132,206,159,228]
    | 221184 => JGc_TX2_HashBytes.state [144,204,223,168,76,216,166,74,227,194,185,212,243,3,52,220,59,216,34,129,248,243,249,25,126,67,141,62,64,65,71,59]
    | 253952 => JGc_TX2_HashBytes.state [78,208,3,215,108,77,215,153,252,92,186,74,30,93,232,95,87,47,70,138,104,13,138,115,161,80,31,90,248,143,34,113]
    | _ => JGc_TX2_HashBytes.state []
  | 14 => match base with
    | 131072 => JGc_TX2_HashBytes.state [76,205,219,41,141,231,162,252,144,59,33,119,50,181,0,227,188,209,249,74,188,31,19,122,76,172,71,94,11,48,185,91]
    | 163840 => JGc_TX2_HashBytes.state [195,209,74,206,189,24,33,14,245,28,250,102,99,222,20,28,120,118,240,28,23,39,12,127,80,80,115,112,100,54,252,25]
    | 229376 => JGc_TX2_HashBytes.state [118,94,98,240,13,109,219,74,220,141,201,122,136,79,63,121,122,39,87,235,183,208,228,91,25,215,28,91,198,59,225,224]
    | _ => JGc_TX2_HashBytes.state []
  | 15 => match base with
    | 98304 => JGc_TX2_HashBytes.state [252,122,11,56,39,253,242,99,6,187,217,125,119,182,47,156,200,119,4,163,152,112,165,102,7,195,55,25,110,238,3,173]
    | _ => JGc_TX2_HashBytes.state []
  | 16 => match base with
    | 0 => JGc_TX2_HashBytes.state [186,70,164,226,215,82,40,99,140,117,51,93,72,25,161,89,123,6,162,192,130,252,253,134,91,166,4,240,224,19,155,103]
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
end AspisR1.JHe_C_Gr_M0Roots
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_C_Gr_M0Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input000 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash000.message
def value000 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash000.result
theorem hash000 : JFp_SHADigest.digest input000=value000 := by
  have law := JHe_SHARealization.tree0 ⟨0, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash000
def tree000 : Tree := .opened input000
theorem root000 : root JFp_SHADigest.digest tree000=value000 := hash000
#print axioms root000
def input001 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash001.message
def value001 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash001.result
theorem hash001 : JFp_SHADigest.digest input001=value001 := by
  have law := JHe_SHARealization.tree0 ⟨1, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash001
def tree001 : Tree := .opened input001
theorem root001 : root JFp_SHADigest.digest tree001=value001 := hash001
#print axioms root001
def input002 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash002.message
def value002 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash002.result
theorem hash002 : JFp_SHADigest.digest input002=value002 := by
  have law := JHe_SHARealization.tree0 ⟨2, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash002
def tree002 : Tree := .opened input002
theorem root002 : root JFp_SHADigest.digest tree002=value002 := hash002
#print axioms root002
def input003 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash003.message
def value003 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash003.result
theorem hash003 : JFp_SHADigest.digest input003=value003 := by
  have law := JHe_SHARealization.tree0 ⟨3, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash003
def tree003 : Tree := .opened input003
theorem root003 : root JFp_SHADigest.digest tree003=value003 := hash003
#print axioms root003
def input004 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash004.message
def value004 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash004.result
theorem hash004 : JFp_SHADigest.digest input004=value004 := by
  have law := JHe_SHARealization.tree0 ⟨4, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash004
def tree004 : Tree := .opened input004
theorem root004 : root JFp_SHADigest.digest tree004=value004 := hash004
#print axioms root004
def input005 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash005.message
def value005 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash005.result
theorem hash005 : JFp_SHADigest.digest input005=value005 := by
  have law := JHe_SHARealization.tree0 ⟨5, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash005
def tree005 : Tree := .opened input005
theorem root005 : root JFp_SHADigest.digest tree005=value005 := hash005
#print axioms root005
def input006 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash006.message
def value006 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash006.result
theorem hash006 : JFp_SHADigest.digest input006=value006 := by
  have law := JHe_SHARealization.tree0 ⟨6, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash006
def tree006 : Tree := .opened input006
theorem root006 : root JFp_SHADigest.digest tree006=value006 := hash006
#print axioms root006
def input007 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash007.message
def value007 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash007.result
theorem hash007 : JFp_SHADigest.digest input007=value007 := by
  have law := JHe_SHARealization.tree0 ⟨7, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash007
def tree007 : Tree := .opened input007
theorem root007 : root JFp_SHADigest.digest tree007=value007 := hash007
#print axioms root007
def input008 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash008.message
def value008 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash008.result
theorem hash008 : JFp_SHADigest.digest input008=value008 := by
  have law := JHe_SHARealization.tree0 ⟨8, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash008
def tree008 : Tree := .opened input008
theorem root008 : root JFp_SHADigest.digest tree008=value008 := hash008
#print axioms root008
def input009 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash009.message
def value009 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash009.result
theorem hash009 : JFp_SHADigest.digest input009=value009 := by
  have law := JHe_SHARealization.tree0 ⟨9, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
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
end AspisR1.JHe_C_Gr_M0Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_C_Gr_M0Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input010 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash010.message
def value010 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash010.result
theorem hash010 : JFp_SHADigest.digest input010=value010 := by
  have law := JHe_SHARealization.tree0 ⟨10, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash010
theorem address010 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [138,12,78,4,29,195,175,124,49,12,183,253,137,178,1,172,57,105,147,139,13,27,199,21,103,254,125,5,89,218,213,42]) value006)=input010 := by rfl
#print axioms address010
def tree010 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [138,12,78,4,29,195,175,124,49,12,183,253,137,178,1,172,57,105,147,139,13,27,199,21,103,254,125,5,89,218,213,42])) tree006
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
def input011 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash011.message
def value011 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash011.result
theorem hash011 : JFp_SHADigest.digest input011=value011 := by
  have law := JHe_SHARealization.tree0 ⟨11, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash011
theorem address011 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [0,155,210,135,10,10,36,139,250,61,153,156,199,68,178,96,3,25,83,60,150,7,110,64,212,120,34,32,128,70,85,4]) value000)=input011 := by rfl
#print axioms address011
def tree011 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [0,155,210,135,10,10,36,139,250,61,153,156,199,68,178,96,3,25,83,60,150,7,110,64,212,120,34,32,128,70,85,4])) tree000
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
def input012 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash012.message
def value012 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash012.result
theorem hash012 : JFp_SHADigest.digest input012=value012 := by
  have law := JHe_SHARealization.tree0 ⟨12, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash012
theorem address012 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [30,206,97,181,53,81,203,161,54,188,202,14,118,67,232,27,234,26,123,152,61,193,146,253,243,71,30,207,164,232,190,24]) value001)=input012 := by rfl
#print axioms address012
def tree012 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [30,206,97,181,53,81,203,161,54,188,202,14,118,67,232,27,234,26,123,152,61,193,146,253,243,71,30,207,164,232,190,24])) tree001
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
def input013 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash013.message
def value013 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash013.result
theorem hash013 : JFp_SHADigest.digest input013=value013 := by
  have law := JHe_SHARealization.tree0 ⟨13, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash013
theorem address013 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [26,195,186,240,93,5,49,188,135,179,131,176,52,102,146,74,221,99,76,219,108,88,144,61,125,193,25,38,125,58,141,31]) value009)=input013 := by rfl
#print axioms address013
def tree013 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [26,195,186,240,93,5,49,188,135,179,131,176,52,102,146,74,221,99,76,219,108,88,144,61,125,193,25,38,125,58,141,31])) tree009
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
def input014 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash014.message
def value014 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash014.result
theorem hash014 : JFp_SHADigest.digest input014=value014 := by
  have law := JHe_SHARealization.tree0 ⟨14, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash014
theorem address014 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [40,252,149,36,166,192,162,64,101,20,54,49,63,59,166,85,31,38,36,0,99,178,228,189,116,169,252,141,90,193,181,51]) value007)=input014 := by rfl
#print axioms address014
def tree014 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [40,252,149,36,166,192,162,64,101,20,54,49,63,59,166,85,31,38,36,0,99,178,228,189,116,169,252,141,90,193,181,51])) tree007
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
def input015 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash015.message
def value015 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash015.result
theorem hash015 : JFp_SHADigest.digest input015=value015 := by
  have law := JHe_SHARealization.tree0 ⟨15, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash015
theorem address015 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [197,135,76,25,172,180,98,84,70,211,112,237,137,36,20,194,104,104,114,136,240,147,181,141,121,72,73,200,110,2,159,172]) value005)=input015 := by rfl
#print axioms address015
def tree015 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [197,135,76,25,172,180,98,84,70,211,112,237,137,36,20,194,104,104,114,136,240,147,181,141,121,72,73,200,110,2,159,172])) tree005
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
def input016 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash016.message
def value016 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash016.result
theorem hash016 : JFp_SHADigest.digest input016=value016 := by
  have law := JHe_SHARealization.tree0 ⟨16, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash016
theorem address016 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [221,112,50,50,72,39,34,4,52,173,152,99,96,65,187,155,71,131,8,35,206,215,205,144,48,160,238,66,13,85,203,152]) value008)=input016 := by rfl
#print axioms address016
def tree016 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [221,112,50,50,72,39,34,4,52,173,152,99,96,65,187,155,71,131,8,35,206,215,205,144,48,160,238,66,13,85,203,152])) tree008
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
def input017 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash017.message
def value017 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash017.result
theorem hash017 : JFp_SHADigest.digest input017=value017 := by
  have law := JHe_SHARealization.tree0 ⟨17, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash017
theorem address017 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [98,52,222,92,145,216,45,125,153,221,152,251,15,144,137,56,230,174,11,161,151,249,216,185,201,144,36,136,166,73,211,28]) value004)=input017 := by rfl
#print axioms address017
def tree017 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [98,52,222,92,145,216,45,125,153,221,152,251,15,144,137,56,230,174,11,161,151,249,216,185,201,144,36,136,166,73,211,28])) tree004
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
def input018 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash018.message
def value018 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash018.result
theorem hash018 : JFp_SHADigest.digest input018=value018 := by
  have law := JHe_SHARealization.tree0 ⟨18, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash018
theorem address018 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [60,239,18,111,191,102,204,179,135,84,19,39,39,192,93,82,21,159,129,98,135,224,200,173,184,187,89,90,164,245,183,28]) value002)=input018 := by rfl
#print axioms address018
def tree018 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [60,239,18,111,191,102,204,179,135,84,19,39,39,192,93,82,21,159,129,98,135,224,200,173,184,187,89,90,164,245,183,28])) tree002
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
def input019 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash019.message
def value019 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash019.result
theorem hash019 : JFp_SHADigest.digest input019=value019 := by
  have law := JHe_SHARealization.tree0 ⟨19, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash019
theorem address019 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [2,236,210,68,67,97,179,9,220,150,3,95,165,1,185,29,159,221,4,51,208,1,32,211,224,128,53,137,65,4,60,189]) value003)=input019 := by rfl
#print axioms address019
def tree019 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [2,236,210,68,67,97,179,9,220,150,3,95,165,1,185,29,159,221,4,51,208,1,32,211,224,128,53,137,65,4,60,189])) tree003
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
end AspisR1.JHe_C_Gr_M0Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_C_Gr_M0Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input020 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash020.message
def value020 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash020.result
theorem hash020 : JFp_SHADigest.digest input020=value020 := by
  have law := JHe_SHARealization.tree0 ⟨20, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash020
theorem address020 : BinMerkle32Path.nodeInput (children value010 (JGc_TX2_HashBytes.state [129,145,123,71,112,75,255,207,218,182,51,10,70,248,80,186,22,215,227,161,95,73,153,136,175,88,40,150,245,11,93,135]))=input020 := by rfl
#print axioms address020
def tree020 : Tree := .branch tree010 (.supplied (JGc_TX2_HashBytes.state [129,145,123,71,112,75,255,207,218,182,51,10,70,248,80,186,22,215,227,161,95,73,153,136,175,88,40,150,245,11,93,135]))
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
def input021 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash021.message
def value021 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash021.result
theorem hash021 : JFp_SHADigest.digest input021=value021 := by
  have law := JHe_SHARealization.tree0 ⟨21, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash021
theorem address021 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [6,77,240,190,14,215,62,129,49,91,41,245,106,187,182,190,199,41,143,109,39,181,18,239,169,207,77,190,62,185,232,101]) value011)=input021 := by rfl
#print axioms address021
def tree021 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [6,77,240,190,14,215,62,129,49,91,41,245,106,187,182,190,199,41,143,109,39,181,18,239,169,207,77,190,62,185,232,101])) tree011
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
def input022 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash022.message
def value022 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash022.result
theorem hash022 : JFp_SHADigest.digest input022=value022 := by
  have law := JHe_SHARealization.tree0 ⟨22, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash022
theorem address022 : BinMerkle32Path.nodeInput (children value012 (JGc_TX2_HashBytes.state [171,86,16,208,136,220,221,143,53,10,68,139,211,174,170,254,152,13,118,166,208,178,197,65,145,118,216,18,233,52,60,82]))=input022 := by rfl
#print axioms address022
def tree022 : Tree := .branch tree012 (.supplied (JGc_TX2_HashBytes.state [171,86,16,208,136,220,221,143,53,10,68,139,211,174,170,254,152,13,118,166,208,178,197,65,145,118,216,18,233,52,60,82]))
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
def input023 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash023.message
def value023 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash023.result
theorem hash023 : JFp_SHADigest.digest input023=value023 := by
  have law := JHe_SHARealization.tree0 ⟨23, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash023
theorem address023 : BinMerkle32Path.nodeInput (children value013 (JGc_TX2_HashBytes.state [248,126,21,210,211,142,137,180,125,82,222,125,142,123,90,165,35,12,113,99,134,20,208,119,121,59,66,164,58,120,127,115]))=input023 := by rfl
#print axioms address023
def tree023 : Tree := .branch tree013 (.supplied (JGc_TX2_HashBytes.state [248,126,21,210,211,142,137,180,125,82,222,125,142,123,90,165,35,12,113,99,134,20,208,119,121,59,66,164,58,120,127,115]))
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
def input024 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash024.message
def value024 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash024.result
theorem hash024 : JFp_SHADigest.digest input024=value024 := by
  have law := JHe_SHARealization.tree0 ⟨24, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash024
theorem address024 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [20,10,255,79,9,214,152,90,126,242,155,160,41,116,223,232,3,49,161,115,34,79,44,109,72,141,100,126,207,51,141,176]) value014)=input024 := by rfl
#print axioms address024
def tree024 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [20,10,255,79,9,214,152,90,126,242,155,160,41,116,223,232,3,49,161,115,34,79,44,109,72,141,100,126,207,51,141,176])) tree014
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
def input025 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash025.message
def value025 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash025.result
theorem hash025 : JFp_SHADigest.digest input025=value025 := by
  have law := JHe_SHARealization.tree0 ⟨25, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash025
theorem address025 : BinMerkle32Path.nodeInput (children value015 (JGc_TX2_HashBytes.state [6,1,204,64,31,38,61,84,24,165,208,174,223,189,74,4,143,235,84,186,217,122,203,71,143,71,240,110,239,79,13,27]))=input025 := by rfl
#print axioms address025
def tree025 : Tree := .branch tree015 (.supplied (JGc_TX2_HashBytes.state [6,1,204,64,31,38,61,84,24,165,208,174,223,189,74,4,143,235,84,186,217,122,203,71,143,71,240,110,239,79,13,27]))
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
def input026 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash026.message
def value026 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash026.result
theorem hash026 : JFp_SHADigest.digest input026=value026 := by
  have law := JHe_SHARealization.tree0 ⟨26, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash026
theorem address026 : BinMerkle32Path.nodeInput (children value016 (JGc_TX2_HashBytes.state [111,19,141,1,38,225,65,248,212,38,27,65,9,175,117,232,105,8,170,194,129,33,180,80,1,242,239,11,227,222,81,248]))=input026 := by rfl
#print axioms address026
def tree026 : Tree := .branch tree016 (.supplied (JGc_TX2_HashBytes.state [111,19,141,1,38,225,65,248,212,38,27,65,9,175,117,232,105,8,170,194,129,33,180,80,1,242,239,11,227,222,81,248]))
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
def input027 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash027.message
def value027 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash027.result
theorem hash027 : JFp_SHADigest.digest input027=value027 := by
  have law := JHe_SHARealization.tree0 ⟨27, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash027
theorem address027 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [17,75,22,191,103,116,8,247,251,193,12,81,68,91,193,167,193,237,72,81,121,112,92,183,215,119,32,4,8,7,113,34]) value017)=input027 := by rfl
#print axioms address027
def tree027 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [17,75,22,191,103,116,8,247,251,193,12,81,68,91,193,167,193,237,72,81,121,112,92,183,215,119,32,4,8,7,113,34])) tree017
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
def input028 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash028.message
def value028 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash028.result
theorem hash028 : JFp_SHADigest.digest input028=value028 := by
  have law := JHe_SHARealization.tree0 ⟨28, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash028
theorem address028 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [198,203,234,73,173,119,179,225,134,57,111,62,249,250,244,3,81,81,144,231,109,135,167,231,203,175,0,17,199,209,221,204]) value018)=input028 := by rfl
#print axioms address028
def tree028 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [198,203,234,73,173,119,179,225,134,57,111,62,249,250,244,3,81,81,144,231,109,135,167,231,203,175,0,17,199,209,221,204])) tree018
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
def input029 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash029.message
def value029 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash029.result
theorem hash029 : JFp_SHADigest.digest input029=value029 := by
  have law := JHe_SHARealization.tree0 ⟨29, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash029
theorem address029 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [250,169,77,120,228,7,6,220,115,87,209,195,16,51,10,191,223,81,107,87,210,1,161,60,20,21,81,135,25,24,132,100]) value019)=input029 := by rfl
#print axioms address029
def tree029 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [250,169,77,120,228,7,6,220,115,87,209,195,16,51,10,191,223,81,107,87,210,1,161,60,20,21,81,135,25,24,132,100])) tree019
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
end AspisR1.JHe_C_Gr_M0Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_C_Gr_M0Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input030 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash030.message
def value030 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash030.result
theorem hash030 : JFp_SHADigest.digest input030=value030 := by
  have law := JHe_SHARealization.tree0 ⟨30, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash030
theorem address030 : BinMerkle32Path.nodeInput (children value020 (JGc_TX2_HashBytes.state [113,228,45,241,12,21,223,82,189,127,50,66,112,86,41,131,49,39,172,121,205,231,86,254,118,88,129,50,88,205,75,198]))=input030 := by rfl
#print axioms address030
def tree030 : Tree := .branch tree020 (.supplied (JGc_TX2_HashBytes.state [113,228,45,241,12,21,223,82,189,127,50,66,112,86,41,131,49,39,172,121,205,231,86,254,118,88,129,50,88,205,75,198]))
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
def input031 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash031.message
def value031 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash031.result
theorem hash031 : JFp_SHADigest.digest input031=value031 := by
  have law := JHe_SHARealization.tree0 ⟨31, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash031
theorem address031 : BinMerkle32Path.nodeInput (children value021 (JGc_TX2_HashBytes.state [170,237,127,75,233,122,51,70,203,215,35,59,216,223,49,175,17,58,145,50,79,33,120,37,250,117,78,166,106,96,202,40]))=input031 := by rfl
#print axioms address031
def tree031 : Tree := .branch tree021 (.supplied (JGc_TX2_HashBytes.state [170,237,127,75,233,122,51,70,203,215,35,59,216,223,49,175,17,58,145,50,79,33,120,37,250,117,78,166,106,96,202,40]))
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
def input032 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash032.message
def value032 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash032.result
theorem hash032 : JFp_SHADigest.digest input032=value032 := by
  have law := JHe_SHARealization.tree0 ⟨32, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash032
theorem address032 : BinMerkle32Path.nodeInput (children value022 (JGc_TX2_HashBytes.state [90,223,103,38,163,10,29,51,156,251,237,216,23,111,164,147,90,200,6,231,84,70,65,96,193,254,203,58,211,238,139,7]))=input032 := by rfl
#print axioms address032
def tree032 : Tree := .branch tree022 (.supplied (JGc_TX2_HashBytes.state [90,223,103,38,163,10,29,51,156,251,237,216,23,111,164,147,90,200,6,231,84,70,65,96,193,254,203,58,211,238,139,7]))
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
def input033 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash033.message
def value033 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash033.result
theorem hash033 : JFp_SHADigest.digest input033=value033 := by
  have law := JHe_SHARealization.tree0 ⟨33, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash033
theorem address033 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [164,239,132,46,197,102,247,125,165,37,99,49,87,147,68,162,92,105,189,105,44,74,146,27,210,103,23,0,30,154,233,18]) value023)=input033 := by rfl
#print axioms address033
def tree033 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [164,239,132,46,197,102,247,125,165,37,99,49,87,147,68,162,92,105,189,105,44,74,146,27,210,103,23,0,30,154,233,18])) tree023
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
def input034 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash034.message
def value034 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash034.result
theorem hash034 : JFp_SHADigest.digest input034=value034 := by
  have law := JHe_SHARealization.tree0 ⟨34, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash034
theorem address034 : BinMerkle32Path.nodeInput (children value024 (JGc_TX2_HashBytes.state [113,219,88,1,248,185,66,167,21,201,234,44,1,193,119,242,149,64,217,87,214,0,169,200,148,84,216,185,197,164,151,244]))=input034 := by rfl
#print axioms address034
def tree034 : Tree := .branch tree024 (.supplied (JGc_TX2_HashBytes.state [113,219,88,1,248,185,66,167,21,201,234,44,1,193,119,242,149,64,217,87,214,0,169,200,148,84,216,185,197,164,151,244]))
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
def input035 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash035.message
def value035 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash035.result
theorem hash035 : JFp_SHADigest.digest input035=value035 := by
  have law := JHe_SHARealization.tree0 ⟨35, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash035
theorem address035 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [131,150,20,119,138,171,247,50,130,133,151,200,22,17,142,182,50,103,254,31,237,67,123,106,214,235,120,126,203,58,12,15]) value025)=input035 := by rfl
#print axioms address035
def tree035 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [131,150,20,119,138,171,247,50,130,133,151,200,22,17,142,182,50,103,254,31,237,67,123,106,214,235,120,126,203,58,12,15])) tree025
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
def input036 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash036.message
def value036 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash036.result
theorem hash036 : JFp_SHADigest.digest input036=value036 := by
  have law := JHe_SHARealization.tree0 ⟨36, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash036
theorem address036 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [153,129,24,20,176,39,22,236,211,202,212,187,140,77,94,63,250,21,206,77,77,113,181,24,141,109,242,160,198,227,5,196]) value026)=input036 := by rfl
#print axioms address036
def tree036 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [153,129,24,20,176,39,22,236,211,202,212,187,140,77,94,63,250,21,206,77,77,113,181,24,141,109,242,160,198,227,5,196])) tree026
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
def input037 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash037.message
def value037 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash037.result
theorem hash037 : JFp_SHADigest.digest input037=value037 := by
  have law := JHe_SHARealization.tree0 ⟨37, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash037
theorem address037 : BinMerkle32Path.nodeInput (children value027 (JGc_TX2_HashBytes.state [101,139,27,149,235,32,119,159,21,175,34,168,214,38,192,112,138,28,226,156,191,27,122,66,141,229,44,205,255,101,185,86]))=input037 := by rfl
#print axioms address037
def tree037 : Tree := .branch tree027 (.supplied (JGc_TX2_HashBytes.state [101,139,27,149,235,32,119,159,21,175,34,168,214,38,192,112,138,28,226,156,191,27,122,66,141,229,44,205,255,101,185,86]))
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
def input038 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash038.message
def value038 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash038.result
theorem hash038 : JFp_SHADigest.digest input038=value038 := by
  have law := JHe_SHARealization.tree0 ⟨38, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash038
theorem address038 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [97,100,140,122,23,30,20,241,117,108,230,40,3,90,18,209,195,137,51,245,94,157,2,13,40,206,120,166,203,53,10,70]) value028)=input038 := by rfl
#print axioms address038
def tree038 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [97,100,140,122,23,30,20,241,117,108,230,40,3,90,18,209,195,137,51,245,94,157,2,13,40,206,120,166,203,53,10,70])) tree028
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
def input039 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash039.message
def value039 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash039.result
theorem hash039 : JFp_SHADigest.digest input039=value039 := by
  have law := JHe_SHARealization.tree0 ⟨39, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash039
theorem address039 : BinMerkle32Path.nodeInput (children value029 (JGc_TX2_HashBytes.state [14,156,11,58,98,11,10,23,106,162,4,80,205,20,195,48,179,221,204,9,0,83,249,174,34,4,190,244,166,20,144,192]))=input039 := by rfl
#print axioms address039
def tree039 : Tree := .branch tree029 (.supplied (JGc_TX2_HashBytes.state [14,156,11,58,98,11,10,23,106,162,4,80,205,20,195,48,179,221,204,9,0,83,249,174,34,4,190,244,166,20,144,192]))
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
end AspisR1.JHe_C_Gr_M0Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_C_Gr_M0Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input040 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash040.message
def value040 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash040.result
theorem hash040 : JFp_SHADigest.digest input040=value040 := by
  have law := JHe_SHARealization.tree0 ⟨40, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash040
theorem address040 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [237,101,153,156,115,150,6,23,215,162,34,228,173,42,146,106,223,172,140,115,117,138,77,161,26,92,89,55,88,255,0,59]) value030)=input040 := by rfl
#print axioms address040
def tree040 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [237,101,153,156,115,150,6,23,215,162,34,228,173,42,146,106,223,172,140,115,117,138,77,161,26,92,89,55,88,255,0,59])) tree030
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
def input041 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash041.message
def value041 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash041.result
theorem hash041 : JFp_SHADigest.digest input041=value041 := by
  have law := JHe_SHARealization.tree0 ⟨41, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash041
theorem address041 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [37,244,135,117,26,54,233,244,102,147,224,254,200,10,248,244,195,200,20,185,169,184,56,177,168,169,22,254,134,167,69,172]) value031)=input041 := by rfl
#print axioms address041
def tree041 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [37,244,135,117,26,54,233,244,102,147,224,254,200,10,248,244,195,200,20,185,169,184,56,177,168,169,22,254,134,167,69,172])) tree031
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
def input042 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash042.message
def value042 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash042.result
theorem hash042 : JFp_SHADigest.digest input042=value042 := by
  have law := JHe_SHARealization.tree0 ⟨42, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash042
theorem address042 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [159,155,131,105,178,86,59,104,185,104,3,52,240,166,65,12,166,115,194,190,140,181,58,92,75,125,4,58,182,78,182,117]) value032)=input042 := by rfl
#print axioms address042
def tree042 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [159,155,131,105,178,86,59,104,185,104,3,52,240,166,65,12,166,115,194,190,140,181,58,92,75,125,4,58,182,78,182,117])) tree032
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
def input043 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash043.message
def value043 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash043.result
theorem hash043 : JFp_SHADigest.digest input043=value043 := by
  have law := JHe_SHARealization.tree0 ⟨43, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash043
theorem address043 : BinMerkle32Path.nodeInput (children value033 (JGc_TX2_HashBytes.state [184,1,99,242,168,187,235,249,27,44,146,36,138,238,109,46,110,208,60,198,44,245,5,255,142,243,124,75,122,28,81,44]))=input043 := by rfl
#print axioms address043
def tree043 : Tree := .branch tree033 (.supplied (JGc_TX2_HashBytes.state [184,1,99,242,168,187,235,249,27,44,146,36,138,238,109,46,110,208,60,198,44,245,5,255,142,243,124,75,122,28,81,44]))
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
def input044 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash044.message
def value044 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash044.result
theorem hash044 : JFp_SHADigest.digest input044=value044 := by
  have law := JHe_SHARealization.tree0 ⟨44, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash044
theorem address044 : BinMerkle32Path.nodeInput (children value034 (JGc_TX2_HashBytes.state [249,155,11,53,79,5,46,47,174,40,100,160,232,197,150,206,57,65,60,151,77,221,228,49,146,47,224,242,31,205,112,53]))=input044 := by rfl
#print axioms address044
def tree044 : Tree := .branch tree034 (.supplied (JGc_TX2_HashBytes.state [249,155,11,53,79,5,46,47,174,40,100,160,232,197,150,206,57,65,60,151,77,221,228,49,146,47,224,242,31,205,112,53]))
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
def input045 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash045.message
def value045 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash045.result
theorem hash045 : JFp_SHADigest.digest input045=value045 := by
  have law := JHe_SHARealization.tree0 ⟨45, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash045
theorem address045 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [238,230,76,71,245,181,227,67,63,205,182,151,40,139,104,248,128,252,163,105,140,161,180,90,61,195,7,172,203,134,85,243]) value035)=input045 := by rfl
#print axioms address045
def tree045 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [238,230,76,71,245,181,227,67,63,205,182,151,40,139,104,248,128,252,163,105,140,161,180,90,61,195,7,172,203,134,85,243])) tree035
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
def input046 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash046.message
def value046 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash046.result
theorem hash046 : JFp_SHADigest.digest input046=value046 := by
  have law := JHe_SHARealization.tree0 ⟨46, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash046
theorem address046 : BinMerkle32Path.nodeInput (children value036 (JGc_TX2_HashBytes.state [236,70,66,207,227,98,249,31,237,39,77,55,123,239,84,213,237,51,12,241,116,71,72,165,63,45,61,196,132,73,13,35]))=input046 := by rfl
#print axioms address046
def tree046 : Tree := .branch tree036 (.supplied (JGc_TX2_HashBytes.state [236,70,66,207,227,98,249,31,237,39,77,55,123,239,84,213,237,51,12,241,116,71,72,165,63,45,61,196,132,73,13,35]))
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
def input047 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash047.message
def value047 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash047.result
theorem hash047 : JFp_SHADigest.digest input047=value047 := by
  have law := JHe_SHARealization.tree0 ⟨47, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash047
theorem address047 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [91,225,147,229,114,51,191,240,38,62,23,3,232,35,207,56,1,62,142,130,179,3,146,218,181,241,176,104,168,124,104,231]) value037)=input047 := by rfl
#print axioms address047
def tree047 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [91,225,147,229,114,51,191,240,38,62,23,3,232,35,207,56,1,62,142,130,179,3,146,218,181,241,176,104,168,124,104,231])) tree037
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
def input048 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash048.message
def value048 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash048.result
theorem hash048 : JFp_SHADigest.digest input048=value048 := by
  have law := JHe_SHARealization.tree0 ⟨48, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash048
theorem address048 : BinMerkle32Path.nodeInput (children value038 (JGc_TX2_HashBytes.state [145,243,79,135,184,204,125,182,43,245,47,168,35,84,132,21,100,19,63,164,130,24,235,181,69,88,56,166,229,252,70,120]))=input048 := by rfl
#print axioms address048
def tree048 : Tree := .branch tree038 (.supplied (JGc_TX2_HashBytes.state [145,243,79,135,184,204,125,182,43,245,47,168,35,84,132,21,100,19,63,164,130,24,235,181,69,88,56,166,229,252,70,120]))
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
def input049 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash049.message
def value049 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash049.result
theorem hash049 : JFp_SHADigest.digest input049=value049 := by
  have law := JHe_SHARealization.tree0 ⟨49, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash049
theorem address049 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [252,69,117,223,75,28,193,245,113,139,104,231,98,230,139,109,224,152,128,86,124,122,36,40,153,175,49,45,182,138,161,172]) value039)=input049 := by rfl
#print axioms address049
def tree049 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [252,69,117,223,75,28,193,245,113,139,104,231,98,230,139,109,224,152,128,86,124,122,36,40,153,175,49,45,182,138,161,172])) tree039
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
end AspisR1.JHe_C_Gr_M0Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_C_Gr_M0Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input050 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash050.message
def value050 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash050.result
theorem hash050 : JFp_SHADigest.digest input050=value050 := by
  have law := JHe_SHARealization.tree0 ⟨50, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash050
theorem address050 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [236,29,86,76,30,67,12,237,81,110,150,232,163,108,233,233,80,159,68,44,137,93,213,2,246,186,157,124,230,83,136,227]) value040)=input050 := by rfl
#print axioms address050
def tree050 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [236,29,86,76,30,67,12,237,81,110,150,232,163,108,233,233,80,159,68,44,137,93,213,2,246,186,157,124,230,83,136,227])) tree040
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
def input051 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash051.message
def value051 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash051.result
theorem hash051 : JFp_SHADigest.digest input051=value051 := by
  have law := JHe_SHARealization.tree0 ⟨51, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash051
theorem address051 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [247,52,6,98,251,50,13,174,91,242,73,132,225,30,14,57,46,158,63,2,190,121,132,15,58,169,20,205,208,200,105,57]) value041)=input051 := by rfl
#print axioms address051
def tree051 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [247,52,6,98,251,50,13,174,91,242,73,132,225,30,14,57,46,158,63,2,190,121,132,15,58,169,20,205,208,200,105,57])) tree041
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
def input052 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash052.message
def value052 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash052.result
theorem hash052 : JFp_SHADigest.digest input052=value052 := by
  have law := JHe_SHARealization.tree0 ⟨52, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash052
theorem address052 : BinMerkle32Path.nodeInput (children value042 (JGc_TX2_HashBytes.state [47,45,200,13,66,168,117,82,224,239,90,35,215,108,210,255,88,3,40,35,217,209,147,174,210,246,44,160,81,239,153,153]))=input052 := by rfl
#print axioms address052
def tree052 : Tree := .branch tree042 (.supplied (JGc_TX2_HashBytes.state [47,45,200,13,66,168,117,82,224,239,90,35,215,108,210,255,88,3,40,35,217,209,147,174,210,246,44,160,81,239,153,153]))
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
def input053 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash053.message
def value053 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash053.result
theorem hash053 : JFp_SHADigest.digest input053=value053 := by
  have law := JHe_SHARealization.tree0 ⟨53, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash053
theorem address053 : BinMerkle32Path.nodeInput (children value043 (JGc_TX2_HashBytes.state [146,13,29,171,138,255,137,186,12,109,8,62,51,250,197,131,20,22,189,188,183,99,33,0,28,151,225,92,193,93,19,97]))=input053 := by rfl
#print axioms address053
def tree053 : Tree := .branch tree043 (.supplied (JGc_TX2_HashBytes.state [146,13,29,171,138,255,137,186,12,109,8,62,51,250,197,131,20,22,189,188,183,99,33,0,28,151,225,92,193,93,19,97]))
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
def input054 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash054.message
def value054 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash054.result
theorem hash054 : JFp_SHADigest.digest input054=value054 := by
  have law := JHe_SHARealization.tree0 ⟨54, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash054
theorem address054 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [179,71,254,154,5,86,67,35,162,58,89,34,52,121,77,71,180,240,121,174,98,142,50,217,93,201,208,91,199,253,90,108]) value044)=input054 := by rfl
#print axioms address054
def tree054 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [179,71,254,154,5,86,67,35,162,58,89,34,52,121,77,71,180,240,121,174,98,142,50,217,93,201,208,91,199,253,90,108])) tree044
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
def input055 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash055.message
def value055 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash055.result
theorem hash055 : JFp_SHADigest.digest input055=value055 := by
  have law := JHe_SHARealization.tree0 ⟨55, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash055
theorem address055 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [38,17,228,198,172,26,2,118,104,186,59,10,202,180,122,6,153,83,58,205,40,8,165,125,33,207,147,16,114,32,156,118]) value045)=input055 := by rfl
#print axioms address055
def tree055 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [38,17,228,198,172,26,2,118,104,186,59,10,202,180,122,6,153,83,58,205,40,8,165,125,33,207,147,16,114,32,156,118])) tree045
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
def input056 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash056.message
def value056 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash056.result
theorem hash056 : JFp_SHADigest.digest input056=value056 := by
  have law := JHe_SHARealization.tree0 ⟨56, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash056
theorem address056 : BinMerkle32Path.nodeInput (children value046 (JGc_TX2_HashBytes.state [174,64,125,54,103,77,213,103,170,28,57,102,173,92,85,231,178,203,38,164,60,235,247,116,32,127,10,7,79,88,232,33]))=input056 := by rfl
#print axioms address056
def tree056 : Tree := .branch tree046 (.supplied (JGc_TX2_HashBytes.state [174,64,125,54,103,77,213,103,170,28,57,102,173,92,85,231,178,203,38,164,60,235,247,116,32,127,10,7,79,88,232,33]))
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
def input057 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash057.message
def value057 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash057.result
theorem hash057 : JFp_SHADigest.digest input057=value057 := by
  have law := JHe_SHARealization.tree0 ⟨57, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash057
theorem address057 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [162,83,182,157,31,13,19,175,77,247,91,65,123,57,95,74,245,247,220,188,222,222,38,42,24,110,87,188,135,58,50,173]) value047)=input057 := by rfl
#print axioms address057
def tree057 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [162,83,182,157,31,13,19,175,77,247,91,65,123,57,95,74,245,247,220,188,222,222,38,42,24,110,87,188,135,58,50,173])) tree047
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
def input058 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash058.message
def value058 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash058.result
theorem hash058 : JFp_SHADigest.digest input058=value058 := by
  have law := JHe_SHARealization.tree0 ⟨58, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash058
theorem address058 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [146,40,112,149,161,135,34,145,67,59,110,211,60,96,206,150,59,192,248,67,117,8,78,102,40,34,154,21,23,151,238,154]) value048)=input058 := by rfl
#print axioms address058
def tree058 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [146,40,112,149,161,135,34,145,67,59,110,211,60,96,206,150,59,192,248,67,117,8,78,102,40,34,154,21,23,151,238,154])) tree048
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
def input059 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash059.message
def value059 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash059.result
theorem hash059 : JFp_SHADigest.digest input059=value059 := by
  have law := JHe_SHARealization.tree0 ⟨59, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash059
theorem address059 : BinMerkle32Path.nodeInput (children value049 (JGc_TX2_HashBytes.state [148,49,202,250,248,38,32,82,139,58,215,125,191,197,113,97,118,28,250,196,119,217,110,64,141,12,92,14,240,146,144,157]))=input059 := by rfl
#print axioms address059
def tree059 : Tree := .branch tree049 (.supplied (JGc_TX2_HashBytes.state [148,49,202,250,248,38,32,82,139,58,215,125,191,197,113,97,118,28,250,196,119,217,110,64,141,12,92,14,240,146,144,157]))
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
end AspisR1.JHe_C_Gr_M0Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_C_Gr_M0Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input060 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash060.message
def value060 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash060.result
theorem hash060 : JFp_SHADigest.digest input060=value060 := by
  have law := JHe_SHARealization.tree0 ⟨60, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash060
theorem address060 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [216,17,255,192,221,66,225,78,57,192,131,236,153,46,142,77,41,52,179,22,166,119,175,6,80,2,94,166,171,119,89,64]) value050)=input060 := by rfl
#print axioms address060
def tree060 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [216,17,255,192,221,66,225,78,57,192,131,236,153,46,142,77,41,52,179,22,166,119,175,6,80,2,94,166,171,119,89,64])) tree050
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
def input061 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash061.message
def value061 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash061.result
theorem hash061 : JFp_SHADigest.digest input061=value061 := by
  have law := JHe_SHARealization.tree0 ⟨61, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash061
theorem address061 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [204,48,251,61,224,226,231,54,110,116,192,65,229,239,85,15,141,34,33,130,96,59,83,197,192,43,247,186,251,77,95,136]) value051)=input061 := by rfl
#print axioms address061
def tree061 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [204,48,251,61,224,226,231,54,110,116,192,65,229,239,85,15,141,34,33,130,96,59,83,197,192,43,247,186,251,77,95,136])) tree051
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
def input062 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash062.message
def value062 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash062.result
theorem hash062 : JFp_SHADigest.digest input062=value062 := by
  have law := JHe_SHARealization.tree0 ⟨62, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash062
theorem address062 : BinMerkle32Path.nodeInput (children value052 (JGc_TX2_HashBytes.state [204,210,70,143,235,140,144,248,219,78,146,18,143,241,159,115,100,67,99,77,124,5,73,9,122,59,54,61,178,235,1,45]))=input062 := by rfl
#print axioms address062
def tree062 : Tree := .branch tree052 (.supplied (JGc_TX2_HashBytes.state [204,210,70,143,235,140,144,248,219,78,146,18,143,241,159,115,100,67,99,77,124,5,73,9,122,59,54,61,178,235,1,45]))
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
def input063 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash063.message
def value063 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash063.result
theorem hash063 : JFp_SHADigest.digest input063=value063 := by
  have law := JHe_SHARealization.tree0 ⟨63, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash063
theorem address063 : BinMerkle32Path.nodeInput (children value053 (JGc_TX2_HashBytes.state [92,145,193,181,163,4,241,41,44,66,156,75,123,119,113,146,69,183,16,241,54,8,84,133,199,46,217,50,3,136,195,213]))=input063 := by rfl
#print axioms address063
def tree063 : Tree := .branch tree053 (.supplied (JGc_TX2_HashBytes.state [92,145,193,181,163,4,241,41,44,66,156,75,123,119,113,146,69,183,16,241,54,8,84,133,199,46,217,50,3,136,195,213]))
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
def input064 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash064.message
def value064 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash064.result
theorem hash064 : JFp_SHADigest.digest input064=value064 := by
  have law := JHe_SHARealization.tree0 ⟨64, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash064
theorem address064 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [177,116,4,114,61,106,88,108,118,62,192,61,211,197,68,169,43,161,77,216,92,76,54,202,145,17,143,238,105,129,100,173]) value054)=input064 := by rfl
#print axioms address064
def tree064 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [177,116,4,114,61,106,88,108,118,62,192,61,211,197,68,169,43,161,77,216,92,76,54,202,145,17,143,238,105,129,100,173])) tree054
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
def input065 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash065.message
def value065 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash065.result
theorem hash065 : JFp_SHADigest.digest input065=value065 := by
  have law := JHe_SHARealization.tree0 ⟨65, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash065
theorem address065 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [231,195,10,19,115,54,82,117,227,102,218,64,54,252,89,187,223,148,244,77,235,96,151,171,64,192,43,182,10,220,40,79]) value055)=input065 := by rfl
#print axioms address065
def tree065 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [231,195,10,19,115,54,82,117,227,102,218,64,54,252,89,187,223,148,244,77,235,96,151,171,64,192,43,182,10,220,40,79])) tree055
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
def input066 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash066.message
def value066 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash066.result
theorem hash066 : JFp_SHADigest.digest input066=value066 := by
  have law := JHe_SHARealization.tree0 ⟨66, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash066
theorem address066 : BinMerkle32Path.nodeInput (children value056 (JGc_TX2_HashBytes.state [151,95,38,140,31,5,121,26,212,129,37,16,148,199,129,176,150,84,199,90,102,60,240,239,124,65,170,220,30,127,98,162]))=input066 := by rfl
#print axioms address066
def tree066 : Tree := .branch tree056 (.supplied (JGc_TX2_HashBytes.state [151,95,38,140,31,5,121,26,212,129,37,16,148,199,129,176,150,84,199,90,102,60,240,239,124,65,170,220,30,127,98,162]))
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
def input067 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash067.message
def value067 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash067.result
theorem hash067 : JFp_SHADigest.digest input067=value067 := by
  have law := JHe_SHARealization.tree0 ⟨67, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash067
theorem address067 : BinMerkle32Path.nodeInput (children value057 (JGc_TX2_HashBytes.state [241,64,215,200,101,21,188,206,149,131,130,157,92,41,217,33,232,168,191,86,174,113,121,90,134,82,2,138,192,43,11,148]))=input067 := by rfl
#print axioms address067
def tree067 : Tree := .branch tree057 (.supplied (JGc_TX2_HashBytes.state [241,64,215,200,101,21,188,206,149,131,130,157,92,41,217,33,232,168,191,86,174,113,121,90,134,82,2,138,192,43,11,148]))
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
def input068 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash068.message
def value068 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash068.result
theorem hash068 : JFp_SHADigest.digest input068=value068 := by
  have law := JHe_SHARealization.tree0 ⟨68, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash068
theorem address068 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [154,13,206,49,223,9,254,76,182,88,42,161,203,130,30,27,176,4,101,162,115,71,35,86,137,49,8,23,137,228,38,97]) value058)=input068 := by rfl
#print axioms address068
def tree068 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [154,13,206,49,223,9,254,76,182,88,42,161,203,130,30,27,176,4,101,162,115,71,35,86,137,49,8,23,137,228,38,97])) tree058
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
def input069 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash069.message
def value069 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash069.result
theorem hash069 : JFp_SHADigest.digest input069=value069 := by
  have law := JHe_SHARealization.tree0 ⟨69, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash069
theorem address069 : BinMerkle32Path.nodeInput (children value059 (JGc_TX2_HashBytes.state [246,74,169,178,195,143,37,247,203,214,169,5,137,26,200,158,2,112,37,14,0,58,128,70,240,102,164,2,132,160,95,14]))=input069 := by rfl
#print axioms address069
def tree069 : Tree := .branch tree059 (.supplied (JGc_TX2_HashBytes.state [246,74,169,178,195,143,37,247,203,214,169,5,137,26,200,158,2,112,37,14,0,58,128,70,240,102,164,2,132,160,95,14]))
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
end AspisR1.JHe_C_Gr_M0Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_C_Gr_M0Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input070 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash070.message
def value070 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash070.result
theorem hash070 : JFp_SHADigest.digest input070=value070 := by
  have law := JHe_SHARealization.tree0 ⟨70, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash070
theorem address070 : BinMerkle32Path.nodeInput (children value060 (JGc_TX2_HashBytes.state [6,240,144,10,89,181,146,35,19,69,34,102,224,239,82,169,126,228,144,157,213,100,223,158,185,74,215,93,123,233,23,161]))=input070 := by rfl
#print axioms address070
def tree070 : Tree := .branch tree060 (.supplied (JGc_TX2_HashBytes.state [6,240,144,10,89,181,146,35,19,69,34,102,224,239,82,169,126,228,144,157,213,100,223,158,185,74,215,93,123,233,23,161]))
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
def input071 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash071.message
def value071 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash071.result
theorem hash071 : JFp_SHADigest.digest input071=value071 := by
  have law := JHe_SHARealization.tree0 ⟨71, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash071
theorem address071 : BinMerkle32Path.nodeInput (children value061 (JGc_TX2_HashBytes.state [90,6,145,42,210,19,190,106,99,39,107,82,176,83,131,93,159,218,108,61,236,10,133,7,20,128,169,78,170,230,90,165]))=input071 := by rfl
#print axioms address071
def tree071 : Tree := .branch tree061 (.supplied (JGc_TX2_HashBytes.state [90,6,145,42,210,19,190,106,99,39,107,82,176,83,131,93,159,218,108,61,236,10,133,7,20,128,169,78,170,230,90,165]))
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
def input072 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash072.message
def value072 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash072.result
theorem hash072 : JFp_SHADigest.digest input072=value072 := by
  have law := JHe_SHARealization.tree0 ⟨72, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash072
theorem address072 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [196,128,247,200,205,132,186,20,133,103,68,116,144,157,48,190,208,40,165,211,155,245,88,90,127,113,249,133,5,38,245,231]) value062)=input072 := by rfl
#print axioms address072
def tree072 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [196,128,247,200,205,132,186,20,133,103,68,116,144,157,48,190,208,40,165,211,155,245,88,90,127,113,249,133,5,38,245,231])) tree062
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
def input073 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash073.message
def value073 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash073.result
theorem hash073 : JFp_SHADigest.digest input073=value073 := by
  have law := JHe_SHARealization.tree0 ⟨73, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash073
theorem address073 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [2,49,107,237,24,224,109,245,28,116,185,193,147,100,59,21,17,156,87,57,186,102,113,213,3,126,197,123,26,250,39,128]) value063)=input073 := by rfl
#print axioms address073
def tree073 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [2,49,107,237,24,224,109,245,28,116,185,193,147,100,59,21,17,156,87,57,186,102,113,213,3,126,197,123,26,250,39,128])) tree063
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
def input074 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash074.message
def value074 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash074.result
theorem hash074 : JFp_SHADigest.digest input074=value074 := by
  have law := JHe_SHARealization.tree0 ⟨74, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash074
theorem address074 : BinMerkle32Path.nodeInput (children value064 (JGc_TX2_HashBytes.state [136,31,229,129,117,15,123,172,12,255,204,60,56,41,146,141,133,147,183,231,229,23,88,42,114,153,55,180,204,108,193,174]))=input074 := by rfl
#print axioms address074
def tree074 : Tree := .branch tree064 (.supplied (JGc_TX2_HashBytes.state [136,31,229,129,117,15,123,172,12,255,204,60,56,41,146,141,133,147,183,231,229,23,88,42,114,153,55,180,204,108,193,174]))
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
def input075 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash075.message
def value075 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash075.result
theorem hash075 : JFp_SHADigest.digest input075=value075 := by
  have law := JHe_SHARealization.tree0 ⟨75, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash075
theorem address075 : BinMerkle32Path.nodeInput (children value065 (JGc_TX2_HashBytes.state [34,30,57,86,102,193,213,112,204,200,212,44,184,202,213,35,17,43,57,142,205,70,168,207,70,167,54,101,73,187,97,202]))=input075 := by rfl
#print axioms address075
def tree075 : Tree := .branch tree065 (.supplied (JGc_TX2_HashBytes.state [34,30,57,86,102,193,213,112,204,200,212,44,184,202,213,35,17,43,57,142,205,70,168,207,70,167,54,101,73,187,97,202]))
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
def input076 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash076.message
def value076 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash076.result
theorem hash076 : JFp_SHADigest.digest input076=value076 := by
  have law := JHe_SHARealization.tree0 ⟨76, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash076
theorem address076 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [92,210,92,203,65,9,235,116,179,182,0,221,48,101,150,142,75,48,236,28,93,37,5,154,73,46,86,46,88,149,55,187]) value066)=input076 := by rfl
#print axioms address076
def tree076 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [92,210,92,203,65,9,235,116,179,182,0,221,48,101,150,142,75,48,236,28,93,37,5,154,73,46,86,46,88,149,55,187])) tree066
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
def input077 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash077.message
def value077 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash077.result
theorem hash077 : JFp_SHADigest.digest input077=value077 := by
  have law := JHe_SHARealization.tree0 ⟨77, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash077
theorem address077 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [205,165,38,151,111,198,79,116,206,226,67,245,236,196,187,100,133,50,31,120,57,157,51,233,222,159,161,218,172,204,11,66]) value067)=input077 := by rfl
#print axioms address077
def tree077 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [205,165,38,151,111,198,79,116,206,226,67,245,236,196,187,100,133,50,31,120,57,157,51,233,222,159,161,218,172,204,11,66])) tree067
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
def input078 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash078.message
def value078 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash078.result
theorem hash078 : JFp_SHADigest.digest input078=value078 := by
  have law := JHe_SHARealization.tree0 ⟨78, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash078
theorem address078 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [226,108,77,28,131,136,7,58,77,240,220,71,105,254,22,209,107,74,73,188,176,248,183,95,174,54,121,81,95,90,24,102]) value068)=input078 := by rfl
#print axioms address078
def tree078 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [226,108,77,28,131,136,7,58,77,240,220,71,105,254,22,209,107,74,73,188,176,248,183,95,174,54,121,81,95,90,24,102])) tree068
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
def input079 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash079.message
def value079 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash079.result
theorem hash079 : JFp_SHADigest.digest input079=value079 := by
  have law := JHe_SHARealization.tree0 ⟨79, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash079
theorem address079 : BinMerkle32Path.nodeInput (children value069 (JGc_TX2_HashBytes.state [87,28,17,1,43,43,239,80,58,175,254,64,102,59,168,121,219,185,145,108,206,67,71,30,115,173,159,96,166,56,54,73]))=input079 := by rfl
#print axioms address079
def tree079 : Tree := .branch tree069 (.supplied (JGc_TX2_HashBytes.state [87,28,17,1,43,43,239,80,58,175,254,64,102,59,168,121,219,185,145,108,206,67,71,30,115,173,159,96,166,56,54,73]))
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
end AspisR1.JHe_C_Gr_M0Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_C_Gr_M0Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input080 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash080.message
def value080 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash080.result
theorem hash080 : JFp_SHADigest.digest input080=value080 := by
  have law := JHe_SHARealization.tree0 ⟨80, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash080
theorem address080 : BinMerkle32Path.nodeInput (children value070 (JGc_TX2_HashBytes.state [77,170,189,130,235,22,61,148,149,65,163,235,1,168,255,7,23,41,163,194,92,20,52,96,214,215,10,79,81,125,23,74]))=input080 := by rfl
#print axioms address080
def tree080 : Tree := .branch tree070 (.supplied (JGc_TX2_HashBytes.state [77,170,189,130,235,22,61,148,149,65,163,235,1,168,255,7,23,41,163,194,92,20,52,96,214,215,10,79,81,125,23,74]))
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
def input081 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash081.message
def value081 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash081.result
theorem hash081 : JFp_SHADigest.digest input081=value081 := by
  have law := JHe_SHARealization.tree0 ⟨81, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash081
theorem address081 : BinMerkle32Path.nodeInput (children value071 (JGc_TX2_HashBytes.state [220,4,163,99,213,83,228,35,211,78,46,27,57,83,108,166,235,71,20,58,174,254,18,51,47,16,101,29,62,46,59,127]))=input081 := by rfl
#print axioms address081
def tree081 : Tree := .branch tree071 (.supplied (JGc_TX2_HashBytes.state [220,4,163,99,213,83,228,35,211,78,46,27,57,83,108,166,235,71,20,58,174,254,18,51,47,16,101,29,62,46,59,127]))
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
def input082 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash082.message
def value082 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash082.result
theorem hash082 : JFp_SHADigest.digest input082=value082 := by
  have law := JHe_SHARealization.tree0 ⟨82, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash082
theorem address082 : BinMerkle32Path.nodeInput (children value072 (JGc_TX2_HashBytes.state [8,32,93,135,247,254,167,22,175,205,245,1,51,185,169,99,158,32,144,204,248,6,73,82,86,253,11,31,112,23,182,248]))=input082 := by rfl
#print axioms address082
def tree082 : Tree := .branch tree072 (.supplied (JGc_TX2_HashBytes.state [8,32,93,135,247,254,167,22,175,205,245,1,51,185,169,99,158,32,144,204,248,6,73,82,86,253,11,31,112,23,182,248]))
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
def input083 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash083.message
def value083 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash083.result
theorem hash083 : JFp_SHADigest.digest input083=value083 := by
  have law := JHe_SHARealization.tree0 ⟨83, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash083
theorem address083 : BinMerkle32Path.nodeInput (children value073 (JGc_TX2_HashBytes.state [237,7,29,17,196,126,123,186,28,187,171,89,156,231,137,55,83,50,16,209,36,156,194,167,84,36,109,35,86,123,184,82]))=input083 := by rfl
#print axioms address083
def tree083 : Tree := .branch tree073 (.supplied (JGc_TX2_HashBytes.state [237,7,29,17,196,126,123,186,28,187,171,89,156,231,137,55,83,50,16,209,36,156,194,167,84,36,109,35,86,123,184,82]))
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
def input084 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash084.message
def value084 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash084.result
theorem hash084 : JFp_SHADigest.digest input084=value084 := by
  have law := JHe_SHARealization.tree0 ⟨84, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash084
theorem address084 : BinMerkle32Path.nodeInput (children value074 (JGc_TX2_HashBytes.state [164,143,95,212,102,248,18,5,14,206,35,160,137,216,216,140,138,220,155,8,95,80,232,194,90,93,3,211,167,239,202,54]))=input084 := by rfl
#print axioms address084
def tree084 : Tree := .branch tree074 (.supplied (JGc_TX2_HashBytes.state [164,143,95,212,102,248,18,5,14,206,35,160,137,216,216,140,138,220,155,8,95,80,232,194,90,93,3,211,167,239,202,54]))
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
def input085 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash085.message
def value085 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash085.result
theorem hash085 : JFp_SHADigest.digest input085=value085 := by
  have law := JHe_SHARealization.tree0 ⟨85, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash085
theorem address085 : BinMerkle32Path.nodeInput (children value075 (JGc_TX2_HashBytes.state [112,33,7,3,28,71,221,2,47,93,159,111,101,209,164,115,182,37,12,24,179,5,186,191,241,44,19,167,238,76,32,192]))=input085 := by rfl
#print axioms address085
def tree085 : Tree := .branch tree075 (.supplied (JGc_TX2_HashBytes.state [112,33,7,3,28,71,221,2,47,93,159,111,101,209,164,115,182,37,12,24,179,5,186,191,241,44,19,167,238,76,32,192]))
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
def input086 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash086.message
def value086 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash086.result
theorem hash086 : JFp_SHADigest.digest input086=value086 := by
  have law := JHe_SHARealization.tree0 ⟨86, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash086
theorem address086 : BinMerkle32Path.nodeInput (children value076 (JGc_TX2_HashBytes.state [74,175,62,170,208,166,232,20,189,64,80,118,215,50,80,8,224,151,209,81,20,7,185,85,124,62,24,188,176,43,92,225]))=input086 := by rfl
#print axioms address086
def tree086 : Tree := .branch tree076 (.supplied (JGc_TX2_HashBytes.state [74,175,62,170,208,166,232,20,189,64,80,118,215,50,80,8,224,151,209,81,20,7,185,85,124,62,24,188,176,43,92,225]))
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
def input087 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash087.message
def value087 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash087.result
theorem hash087 : JFp_SHADigest.digest input087=value087 := by
  have law := JHe_SHARealization.tree0 ⟨87, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash087
theorem address087 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [218,253,65,240,172,229,138,129,76,204,176,47,148,25,169,129,220,198,33,211,14,132,216,254,101,36,143,228,205,218,132,45]) value077)=input087 := by rfl
#print axioms address087
def tree087 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [218,253,65,240,172,229,138,129,76,204,176,47,148,25,169,129,220,198,33,211,14,132,216,254,101,36,143,228,205,218,132,45])) tree077
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
def input088 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash088.message
def value088 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash088.result
theorem hash088 : JFp_SHADigest.digest input088=value088 := by
  have law := JHe_SHARealization.tree0 ⟨88, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash088
theorem address088 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [92,111,165,106,142,29,249,211,6,148,240,59,145,1,129,21,239,41,72,97,151,216,109,27,177,211,241,204,132,133,92,249]) value078)=input088 := by rfl
#print axioms address088
def tree088 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [92,111,165,106,142,29,249,211,6,148,240,59,145,1,129,21,239,41,72,97,151,216,109,27,177,211,241,204,132,133,92,249])) tree078
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
def input089 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash089.message
def value089 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash089.result
theorem hash089 : JFp_SHADigest.digest input089=value089 := by
  have law := JHe_SHARealization.tree0 ⟨89, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash089
theorem address089 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [15,149,178,185,103,188,80,183,213,234,175,109,95,91,156,29,122,205,226,127,154,135,172,211,157,76,137,128,192,230,142,182]) value079)=input089 := by rfl
#print axioms address089
def tree089 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [15,149,178,185,103,188,80,183,213,234,175,109,95,91,156,29,122,205,226,127,154,135,172,211,157,76,137,128,192,230,142,182])) tree079
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
end AspisR1.JHe_C_Gr_M0Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_C_Gr_M0Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input090 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash090.message
def value090 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash090.result
theorem hash090 : JFp_SHADigest.digest input090=value090 := by
  have law := JHe_SHARealization.tree0 ⟨90, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash090
theorem address090 : BinMerkle32Path.nodeInput (children value080 (JGc_TX2_HashBytes.state [113,23,49,153,65,62,50,121,121,134,77,85,4,221,172,58,119,143,25,248,30,111,211,227,9,191,95,71,39,81,225,50]))=input090 := by rfl
#print axioms address090
def tree090 : Tree := .branch tree080 (.supplied (JGc_TX2_HashBytes.state [113,23,49,153,65,62,50,121,121,134,77,85,4,221,172,58,119,143,25,248,30,111,211,227,9,191,95,71,39,81,225,50]))
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
def input091 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash091.message
def value091 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash091.result
theorem hash091 : JFp_SHADigest.digest input091=value091 := by
  have law := JHe_SHARealization.tree0 ⟨91, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash091
theorem address091 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [17,86,79,88,53,63,109,64,216,191,11,30,55,109,89,48,69,42,142,22,51,233,130,145,169,63,100,38,75,249,74,19]) value081)=input091 := by rfl
#print axioms address091
def tree091 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [17,86,79,88,53,63,109,64,216,191,11,30,55,109,89,48,69,42,142,22,51,233,130,145,169,63,100,38,75,249,74,19])) tree081
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
def input092 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash092.message
def value092 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash092.result
theorem hash092 : JFp_SHADigest.digest input092=value092 := by
  have law := JHe_SHARealization.tree0 ⟨92, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash092
theorem address092 : BinMerkle32Path.nodeInput (children value082 (JGc_TX2_HashBytes.state [226,155,182,235,137,88,156,193,14,203,121,8,103,202,235,239,155,117,229,172,214,169,41,35,14,166,228,96,191,226,79,63]))=input092 := by rfl
#print axioms address092
def tree092 : Tree := .branch tree082 (.supplied (JGc_TX2_HashBytes.state [226,155,182,235,137,88,156,193,14,203,121,8,103,202,235,239,155,117,229,172,214,169,41,35,14,166,228,96,191,226,79,63]))
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
def input093 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash093.message
def value093 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash093.result
theorem hash093 : JFp_SHADigest.digest input093=value093 := by
  have law := JHe_SHARealization.tree0 ⟨93, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash093
theorem address093 : BinMerkle32Path.nodeInput (children value083 (JGc_TX2_HashBytes.state [126,121,251,104,220,255,47,155,0,110,75,75,75,176,125,193,113,66,44,179,9,60,208,17,238,130,66,26,194,98,247,255]))=input093 := by rfl
#print axioms address093
def tree093 : Tree := .branch tree083 (.supplied (JGc_TX2_HashBytes.state [126,121,251,104,220,255,47,155,0,110,75,75,75,176,125,193,113,66,44,179,9,60,208,17,238,130,66,26,194,98,247,255]))
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
def input094 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash094.message
def value094 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash094.result
theorem hash094 : JFp_SHADigest.digest input094=value094 := by
  have law := JHe_SHARealization.tree0 ⟨94, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash094
theorem address094 : BinMerkle32Path.nodeInput (children value084 (JGc_TX2_HashBytes.state [158,176,11,125,66,96,99,8,73,93,247,85,166,153,219,250,17,121,222,96,4,149,255,161,250,23,46,233,243,21,255,119]))=input094 := by rfl
#print axioms address094
def tree094 : Tree := .branch tree084 (.supplied (JGc_TX2_HashBytes.state [158,176,11,125,66,96,99,8,73,93,247,85,166,153,219,250,17,121,222,96,4,149,255,161,250,23,46,233,243,21,255,119]))
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
def input095 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash095.message
def value095 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash095.result
theorem hash095 : JFp_SHADigest.digest input095=value095 := by
  have law := JHe_SHARealization.tree0 ⟨95, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash095
theorem address095 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [207,177,176,60,127,81,118,135,169,148,236,21,219,140,173,74,233,123,232,214,172,56,152,55,156,176,4,122,1,49,209,83]) value085)=input095 := by rfl
#print axioms address095
def tree095 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [207,177,176,60,127,81,118,135,169,148,236,21,219,140,173,74,233,123,232,214,172,56,152,55,156,176,4,122,1,49,209,83])) tree085
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
def input096 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash096.message
def value096 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash096.result
theorem hash096 : JFp_SHADigest.digest input096=value096 := by
  have law := JHe_SHARealization.tree0 ⟨96, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash096
theorem address096 : BinMerkle32Path.nodeInput (children value086 (JGc_TX2_HashBytes.state [65,182,123,189,84,7,216,217,132,96,18,74,118,7,3,237,94,9,129,18,202,71,166,195,20,119,229,148,187,131,19,241]))=input096 := by rfl
#print axioms address096
def tree096 : Tree := .branch tree086 (.supplied (JGc_TX2_HashBytes.state [65,182,123,189,84,7,216,217,132,96,18,74,118,7,3,237,94,9,129,18,202,71,166,195,20,119,229,148,187,131,19,241]))
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
def input097 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash097.message
def value097 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash097.result
theorem hash097 : JFp_SHADigest.digest input097=value097 := by
  have law := JHe_SHARealization.tree0 ⟨97, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash097
theorem address097 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [151,189,242,15,48,2,126,127,42,140,208,198,249,228,165,254,222,43,136,1,116,49,161,30,227,32,117,1,201,85,56,26]) value087)=input097 := by rfl
#print axioms address097
def tree097 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [151,189,242,15,48,2,126,127,42,140,208,198,249,228,165,254,222,43,136,1,116,49,161,30,227,32,117,1,201,85,56,26])) tree087
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
def input098 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash098.message
def value098 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash098.result
theorem hash098 : JFp_SHADigest.digest input098=value098 := by
  have law := JHe_SHARealization.tree0 ⟨98, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash098
theorem address098 : BinMerkle32Path.nodeInput (children value088 (JGc_TX2_HashBytes.state [46,78,225,61,74,143,106,41,11,1,157,44,41,247,155,126,43,181,1,160,152,29,224,187,122,141,106,211,167,157,239,161]))=input098 := by rfl
#print axioms address098
def tree098 : Tree := .branch tree088 (.supplied (JGc_TX2_HashBytes.state [46,78,225,61,74,143,106,41,11,1,157,44,41,247,155,126,43,181,1,160,152,29,224,187,122,141,106,211,167,157,239,161]))
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
def input099 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash099.message
def value099 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash099.result
theorem hash099 : JFp_SHADigest.digest input099=value099 := by
  have law := JHe_SHARealization.tree0 ⟨99, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash099
theorem address099 : BinMerkle32Path.nodeInput (children value089 (JGc_TX2_HashBytes.state [8,249,218,86,52,33,101,166,203,237,91,36,157,221,19,10,53,117,89,94,91,68,66,227,193,115,151,105,136,220,126,108]))=input099 := by rfl
#print axioms address099
def tree099 : Tree := .branch tree089 (.supplied (JGc_TX2_HashBytes.state [8,249,218,86,52,33,101,166,203,237,91,36,157,221,19,10,53,117,89,94,91,68,66,227,193,115,151,105,136,220,126,108]))
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
end AspisR1.JHe_C_Gr_M0Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_C_Gr_M0Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input100 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash100.message
def value100 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash100.result
theorem hash100 : JFp_SHADigest.digest input100=value100 := by
  have law := JHe_SHARealization.tree0 ⟨100, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash100
theorem address100 : BinMerkle32Path.nodeInput (children value090 (JGc_TX2_HashBytes.state [23,74,195,49,213,135,245,27,57,199,58,222,148,196,183,123,71,5,192,127,140,213,208,209,54,153,86,127,135,105,132,180]))=input100 := by rfl
#print axioms address100
def tree100 : Tree := .branch tree090 (.supplied (JGc_TX2_HashBytes.state [23,74,195,49,213,135,245,27,57,199,58,222,148,196,183,123,71,5,192,127,140,213,208,209,54,153,86,127,135,105,132,180]))
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
def input101 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash101.message
def value101 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash101.result
theorem hash101 : JFp_SHADigest.digest input101=value101 := by
  have law := JHe_SHARealization.tree0 ⟨101, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash101
theorem address101 : BinMerkle32Path.nodeInput (children value091 (JGc_TX2_HashBytes.state [247,170,236,136,32,227,215,1,30,170,171,104,222,196,102,119,141,43,224,250,73,121,228,110,63,169,195,18,64,55,103,111]))=input101 := by rfl
#print axioms address101
def tree101 : Tree := .branch tree091 (.supplied (JGc_TX2_HashBytes.state [247,170,236,136,32,227,215,1,30,170,171,104,222,196,102,119,141,43,224,250,73,121,228,110,63,169,195,18,64,55,103,111]))
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
def input102 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash102.message
def value102 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash102.result
theorem hash102 : JFp_SHADigest.digest input102=value102 := by
  have law := JHe_SHARealization.tree0 ⟨102, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash102
theorem address102 : BinMerkle32Path.nodeInput (children value092 (JGc_TX2_HashBytes.state [190,108,13,171,84,192,94,96,227,48,105,48,244,245,190,168,224,83,16,169,249,226,55,97,180,229,154,227,86,36,50,122]))=input102 := by rfl
#print axioms address102
def tree102 : Tree := .branch tree092 (.supplied (JGc_TX2_HashBytes.state [190,108,13,171,84,192,94,96,227,48,105,48,244,245,190,168,224,83,16,169,249,226,55,97,180,229,154,227,86,36,50,122]))
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
def input103 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash103.message
def value103 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash103.result
theorem hash103 : JFp_SHADigest.digest input103=value103 := by
  have law := JHe_SHARealization.tree0 ⟨103, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash103
theorem address103 : BinMerkle32Path.nodeInput (children value093 (JGc_TX2_HashBytes.state [157,66,177,205,179,25,156,253,216,204,238,141,248,146,126,57,146,197,187,130,191,130,41,226,29,137,114,88,159,239,90,188]))=input103 := by rfl
#print axioms address103
def tree103 : Tree := .branch tree093 (.supplied (JGc_TX2_HashBytes.state [157,66,177,205,179,25,156,253,216,204,238,141,248,146,126,57,146,197,187,130,191,130,41,226,29,137,114,88,159,239,90,188]))
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
def input104 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash104.message
def value104 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash104.result
theorem hash104 : JFp_SHADigest.digest input104=value104 := by
  have law := JHe_SHARealization.tree0 ⟨104, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash104
theorem address104 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [79,115,19,153,165,205,224,136,61,186,168,120,162,67,201,141,134,174,172,243,21,240,241,100,42,229,53,233,153,170,42,41]) value094)=input104 := by rfl
#print axioms address104
def tree104 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [79,115,19,153,165,205,224,136,61,186,168,120,162,67,201,141,134,174,172,243,21,240,241,100,42,229,53,233,153,170,42,41])) tree094
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
def input105 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash105.message
def value105 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash105.result
theorem hash105 : JFp_SHADigest.digest input105=value105 := by
  have law := JHe_SHARealization.tree0 ⟨105, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash105
theorem address105 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [148,43,99,22,57,180,71,36,176,106,37,117,42,190,120,213,40,143,126,3,58,186,68,221,194,74,60,125,229,230,106,79]) value095)=input105 := by rfl
#print axioms address105
def tree105 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [148,43,99,22,57,180,71,36,176,106,37,117,42,190,120,213,40,143,126,3,58,186,68,221,194,74,60,125,229,230,106,79])) tree095
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
def input106 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash106.message
def value106 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash106.result
theorem hash106 : JFp_SHADigest.digest input106=value106 := by
  have law := JHe_SHARealization.tree0 ⟨106, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash106
theorem address106 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [207,102,135,191,134,26,82,182,249,62,205,164,72,118,227,234,90,100,188,183,151,160,216,216,200,245,4,24,126,19,178,5]) value096)=input106 := by rfl
#print axioms address106
def tree106 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [207,102,135,191,134,26,82,182,249,62,205,164,72,118,227,234,90,100,188,183,151,160,216,216,200,245,4,24,126,19,178,5])) tree096
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
def input107 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash107.message
def value107 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash107.result
theorem hash107 : JFp_SHADigest.digest input107=value107 := by
  have law := JHe_SHARealization.tree0 ⟨107, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash107
theorem address107 : BinMerkle32Path.nodeInput (children value097 (JGc_TX2_HashBytes.state [136,24,60,241,94,194,126,24,120,244,56,48,145,68,42,168,200,103,87,128,189,66,104,116,209,245,141,65,97,81,150,11]))=input107 := by rfl
#print axioms address107
def tree107 : Tree := .branch tree097 (.supplied (JGc_TX2_HashBytes.state [136,24,60,241,94,194,126,24,120,244,56,48,145,68,42,168,200,103,87,128,189,66,104,116,209,245,141,65,97,81,150,11]))
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
def input108 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash108.message
def value108 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash108.result
theorem hash108 : JFp_SHADigest.digest input108=value108 := by
  have law := JHe_SHARealization.tree0 ⟨108, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash108
theorem address108 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [236,224,3,7,229,22,125,66,186,131,47,131,187,123,43,166,14,188,255,80,197,222,226,154,83,187,231,109,201,152,99,74]) value098)=input108 := by rfl
#print axioms address108
def tree108 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [236,224,3,7,229,22,125,66,186,131,47,131,187,123,43,166,14,188,255,80,197,222,226,154,83,187,231,109,201,152,99,74])) tree098
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
def input109 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash109.message
def value109 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash109.result
theorem hash109 : JFp_SHADigest.digest input109=value109 := by
  have law := JHe_SHARealization.tree0 ⟨109, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash109
theorem address109 : BinMerkle32Path.nodeInput (children value099 (JGc_TX2_HashBytes.state [129,168,53,62,31,143,67,207,71,169,96,123,137,17,208,1,3,164,237,62,64,109,62,71,117,71,184,169,224,169,104,142]))=input109 := by rfl
#print axioms address109
def tree109 : Tree := .branch tree099 (.supplied (JGc_TX2_HashBytes.state [129,168,53,62,31,143,67,207,71,169,96,123,137,17,208,1,3,164,237,62,64,109,62,71,117,71,184,169,224,169,104,142]))
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
end AspisR1.JHe_C_Gr_M0Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_C_Gr_M0Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input110 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash110.message
def value110 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash110.result
theorem hash110 : JFp_SHADigest.digest input110=value110 := by
  have law := JHe_SHARealization.tree0 ⟨110, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash110
theorem address110 : BinMerkle32Path.nodeInput (children value100 (JGc_TX2_HashBytes.state [152,162,255,196,212,132,122,99,218,255,12,162,24,58,6,29,109,82,79,82,141,97,174,54,239,110,201,1,108,154,177,68]))=input110 := by rfl
#print axioms address110
def tree110 : Tree := .branch tree100 (.supplied (JGc_TX2_HashBytes.state [152,162,255,196,212,132,122,99,218,255,12,162,24,58,6,29,109,82,79,82,141,97,174,54,239,110,201,1,108,154,177,68]))
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
def input111 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash111.message
def value111 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash111.result
theorem hash111 : JFp_SHADigest.digest input111=value111 := by
  have law := JHe_SHARealization.tree0 ⟨111, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash111
theorem address111 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [241,229,149,152,170,27,18,61,206,161,98,30,225,40,233,53,46,62,50,48,254,208,247,99,208,150,81,200,50,240,48,143]) value101)=input111 := by rfl
#print axioms address111
def tree111 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [241,229,149,152,170,27,18,61,206,161,98,30,225,40,233,53,46,62,50,48,254,208,247,99,208,150,81,200,50,240,48,143])) tree101
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
def input112 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash112.message
def value112 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash112.result
theorem hash112 : JFp_SHADigest.digest input112=value112 := by
  have law := JHe_SHARealization.tree0 ⟨112, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash112
theorem address112 : BinMerkle32Path.nodeInput (children value102 (JGc_TX2_HashBytes.state [207,160,0,107,107,203,186,65,189,180,20,58,15,97,7,28,17,81,82,78,101,147,184,188,37,229,216,233,181,44,255,192]))=input112 := by rfl
#print axioms address112
def tree112 : Tree := .branch tree102 (.supplied (JGc_TX2_HashBytes.state [207,160,0,107,107,203,186,65,189,180,20,58,15,97,7,28,17,81,82,78,101,147,184,188,37,229,216,233,181,44,255,192]))
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
def input113 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash113.message
def value113 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash113.result
theorem hash113 : JFp_SHADigest.digest input113=value113 := by
  have law := JHe_SHARealization.tree0 ⟨113, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash113
theorem address113 : BinMerkle32Path.nodeInput (children value103 (JGc_TX2_HashBytes.state [123,0,162,188,126,191,227,58,109,189,247,38,102,61,157,69,230,4,19,213,18,43,156,113,160,76,253,162,235,123,98,2]))=input113 := by rfl
#print axioms address113
def tree113 : Tree := .branch tree103 (.supplied (JGc_TX2_HashBytes.state [123,0,162,188,126,191,227,58,109,189,247,38,102,61,157,69,230,4,19,213,18,43,156,113,160,76,253,162,235,123,98,2]))
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
def input114 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash114.message
def value114 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash114.result
theorem hash114 : JFp_SHADigest.digest input114=value114 := by
  have law := JHe_SHARealization.tree0 ⟨114, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash114
theorem address114 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [26,34,190,23,233,18,66,255,141,224,173,247,208,54,188,241,221,59,100,97,57,196,21,248,129,34,192,76,118,155,221,240]) value104)=input114 := by rfl
#print axioms address114
def tree114 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [26,34,190,23,233,18,66,255,141,224,173,247,208,54,188,241,221,59,100,97,57,196,21,248,129,34,192,76,118,155,221,240])) tree104
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
def input115 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash115.message
def value115 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash115.result
theorem hash115 : JFp_SHADigest.digest input115=value115 := by
  have law := JHe_SHARealization.tree0 ⟨115, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash115
theorem address115 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [187,161,232,81,61,204,163,255,108,96,207,42,203,160,95,178,216,58,192,25,156,191,241,239,172,147,29,95,154,104,197,242]) value105)=input115 := by rfl
#print axioms address115
def tree115 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [187,161,232,81,61,204,163,255,108,96,207,42,203,160,95,178,216,58,192,25,156,191,241,239,172,147,29,95,154,104,197,242])) tree105
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
def input116 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash116.message
def value116 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash116.result
theorem hash116 : JFp_SHADigest.digest input116=value116 := by
  have law := JHe_SHARealization.tree0 ⟨116, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash116
theorem address116 : BinMerkle32Path.nodeInput (children value106 (JGc_TX2_HashBytes.state [112,136,211,124,72,204,53,180,236,108,229,56,210,88,160,196,172,44,115,159,237,211,216,230,73,10,77,132,61,136,48,224]))=input116 := by rfl
#print axioms address116
def tree116 : Tree := .branch tree106 (.supplied (JGc_TX2_HashBytes.state [112,136,211,124,72,204,53,180,236,108,229,56,210,88,160,196,172,44,115,159,237,211,216,230,73,10,77,132,61,136,48,224]))
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
def input117 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash117.message
def value117 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash117.result
theorem hash117 : JFp_SHADigest.digest input117=value117 := by
  have law := JHe_SHARealization.tree0 ⟨117, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash117
theorem address117 : BinMerkle32Path.nodeInput (children value107 (JGc_TX2_HashBytes.state [68,125,166,81,87,6,116,93,85,44,114,64,254,221,200,45,38,25,196,77,234,200,255,231,247,107,222,180,48,23,31,85]))=input117 := by rfl
#print axioms address117
def tree117 : Tree := .branch tree107 (.supplied (JGc_TX2_HashBytes.state [68,125,166,81,87,6,116,93,85,44,114,64,254,221,200,45,38,25,196,77,234,200,255,231,247,107,222,180,48,23,31,85]))
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
def input118 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash118.message
def value118 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash118.result
theorem hash118 : JFp_SHADigest.digest input118=value118 := by
  have law := JHe_SHARealization.tree0 ⟨118, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash118
theorem address118 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [77,126,21,65,26,159,97,38,195,165,185,168,141,30,194,190,83,101,161,199,214,33,229,162,241,59,159,235,156,208,67,0]) value108)=input118 := by rfl
#print axioms address118
def tree118 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [77,126,21,65,26,159,97,38,195,165,185,168,141,30,194,190,83,101,161,199,214,33,229,162,241,59,159,235,156,208,67,0])) tree108
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
def input119 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash119.message
def value119 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash119.result
theorem hash119 : JFp_SHADigest.digest input119=value119 := by
  have law := JHe_SHARealization.tree0 ⟨119, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash119
theorem address119 : BinMerkle32Path.nodeInput (children value109 (JGc_TX2_HashBytes.state [119,215,118,217,83,7,90,172,138,108,205,252,152,230,120,183,250,105,16,42,20,115,89,179,235,222,70,56,78,50,213,22]))=input119 := by rfl
#print axioms address119
def tree119 : Tree := .branch tree109 (.supplied (JGc_TX2_HashBytes.state [119,215,118,217,83,7,90,172,138,108,205,252,152,230,120,183,250,105,16,42,20,115,89,179,235,222,70,56,78,50,213,22]))
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
end AspisR1.JHe_C_Gr_M0Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_C_Gr_M0Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input120 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash120.message
def value120 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash120.result
theorem hash120 : JFp_SHADigest.digest input120=value120 := by
  have law := JHe_SHARealization.tree0 ⟨120, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash120
theorem address120 : BinMerkle32Path.nodeInput (children value110 (JGc_TX2_HashBytes.state [164,65,78,40,106,51,231,38,125,149,75,249,27,93,238,7,155,254,36,78,118,136,30,42,179,250,247,120,7,81,21,144]))=input120 := by rfl
#print axioms address120
def tree120 : Tree := .branch tree110 (.supplied (JGc_TX2_HashBytes.state [164,65,78,40,106,51,231,38,125,149,75,249,27,93,238,7,155,254,36,78,118,136,30,42,179,250,247,120,7,81,21,144]))
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
def input121 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash121.message
def value121 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash121.result
theorem hash121 : JFp_SHADigest.digest input121=value121 := by
  have law := JHe_SHARealization.tree0 ⟨121, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash121
theorem address121 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [211,245,58,70,112,158,59,164,73,134,77,204,94,119,107,22,183,105,32,45,41,61,170,17,107,25,88,255,149,122,164,95]) value111)=input121 := by rfl
#print axioms address121
def tree121 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [211,245,58,70,112,158,59,164,73,134,77,204,94,119,107,22,183,105,32,45,41,61,170,17,107,25,88,255,149,122,164,95])) tree111
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
def input122 : Bytes := JGf_TX2_M0Roots.input150
def value122 : State := JGf_TX2_M0Roots.value150
theorem hash122 : JFp_SHADigest.digest input122=value122 := by
  have law := JHe_SHARealization.tree0 ⟨122, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash122
theorem address122 : BinMerkle32Path.nodeInput (children value112 (JGc_TX2_HashBytes.state [202,64,14,6,35,96,78,97,222,124,133,255,162,222,235,186,63,243,32,144,64,134,253,43,104,226,220,66,124,185,92,7]))=input122 := by rfl
#print axioms address122
def tree122 : Tree := .branch tree112 (.supplied (JGc_TX2_HashBytes.state [202,64,14,6,35,96,78,97,222,124,133,255,162,222,235,186,63,243,32,144,64,134,253,43,104,226,220,66,124,185,92,7]))
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
def input123 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash123.message
def value123 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash123.result
theorem hash123 : JFp_SHADigest.digest input123=value123 := by
  have law := JHe_SHARealization.tree0 ⟨123, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash123
theorem address123 : BinMerkle32Path.nodeInput (children value113 (JGc_TX2_HashBytes.state [247,131,116,212,93,146,215,2,194,179,95,254,35,17,63,19,206,90,55,80,187,155,124,170,167,224,151,27,162,66,130,234]))=input123 := by rfl
#print axioms address123
def tree123 : Tree := .branch tree113 (.supplied (JGc_TX2_HashBytes.state [247,131,116,212,93,146,215,2,194,179,95,254,35,17,63,19,206,90,55,80,187,155,124,170,167,224,151,27,162,66,130,234]))
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
def input124 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash124.message
def value124 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash124.result
theorem hash124 : JFp_SHADigest.digest input124=value124 := by
  have law := JHe_SHARealization.tree0 ⟨124, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash124
theorem address124 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [210,253,93,83,135,24,182,107,129,24,45,138,60,15,178,254,10,77,18,68,97,47,12,113,104,75,135,148,129,15,201,143]) value114)=input124 := by rfl
#print axioms address124
def tree124 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [210,253,93,83,135,24,182,107,129,24,45,138,60,15,178,254,10,77,18,68,97,47,12,113,104,75,135,148,129,15,201,143])) tree114
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
def input125 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash125.message
def value125 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash125.result
theorem hash125 : JFp_SHADigest.digest input125=value125 := by
  have law := JHe_SHARealization.tree0 ⟨125, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash125
theorem address125 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [108,30,109,110,34,215,172,38,88,37,207,120,123,70,8,40,222,202,101,229,33,117,10,142,69,118,38,35,142,15,136,99]) value115)=input125 := by rfl
#print axioms address125
def tree125 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [108,30,109,110,34,215,172,38,88,37,207,120,123,70,8,40,222,202,101,229,33,117,10,142,69,118,38,35,142,15,136,99])) tree115
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
def input126 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash126.message
def value126 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash126.result
theorem hash126 : JFp_SHADigest.digest input126=value126 := by
  have law := JHe_SHARealization.tree0 ⟨126, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash126
theorem address126 : BinMerkle32Path.nodeInput (children value116 (JGc_TX2_HashBytes.state [163,133,73,137,234,254,224,77,43,180,89,181,80,182,68,145,168,49,120,172,255,240,170,6,191,185,169,251,210,212,116,243]))=input126 := by rfl
#print axioms address126
def tree126 : Tree := .branch tree116 (.supplied (JGc_TX2_HashBytes.state [163,133,73,137,234,254,224,77,43,180,89,181,80,182,68,145,168,49,120,172,255,240,170,6,191,185,169,251,210,212,116,243]))
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
def input127 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash127.message
def value127 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash127.result
theorem hash127 : JFp_SHADigest.digest input127=value127 := by
  have law := JHe_SHARealization.tree0 ⟨127, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash127
theorem address127 : BinMerkle32Path.nodeInput (children value117 (JGc_TX2_HashBytes.state [129,75,194,226,75,93,208,230,67,98,126,175,55,174,113,122,34,52,245,123,168,194,155,56,57,111,31,104,119,113,135,71]))=input127 := by rfl
#print axioms address127
def tree127 : Tree := .branch tree117 (.supplied (JGc_TX2_HashBytes.state [129,75,194,226,75,93,208,230,67,98,126,175,55,174,113,122,34,52,245,123,168,194,155,56,57,111,31,104,119,113,135,71]))
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
def input128 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash128.message
def value128 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash128.result
theorem hash128 : JFp_SHADigest.digest input128=value128 := by
  have law := JHe_SHARealization.tree0 ⟨128, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash128
theorem address128 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [56,117,174,192,243,180,43,166,2,52,80,21,16,203,229,105,85,214,216,157,123,230,248,209,219,21,217,60,60,150,184,141]) value118)=input128 := by rfl
#print axioms address128
def tree128 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [56,117,174,192,243,180,43,166,2,52,80,21,16,203,229,105,85,214,216,157,123,230,248,209,219,21,217,60,60,150,184,141])) tree118
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
def input129 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash129.message
def value129 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash129.result
theorem hash129 : JFp_SHADigest.digest input129=value129 := by
  have law := JHe_SHARealization.tree0 ⟨129, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash129
theorem address129 : BinMerkle32Path.nodeInput (children value119 (JGc_TX2_HashBytes.state [109,231,155,150,47,42,48,122,18,218,72,65,211,238,180,205,145,47,143,73,158,94,97,67,253,155,2,166,178,50,203,27]))=input129 := by rfl
#print axioms address129
def tree129 : Tree := .branch tree119 (.supplied (JGc_TX2_HashBytes.state [109,231,155,150,47,42,48,122,18,218,72,65,211,238,180,205,145,47,143,73,158,94,97,67,253,155,2,166,178,50,203,27]))
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
end AspisR1.JHe_C_Gr_M0Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_C_Gr_M0Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input130 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash130.message
def value130 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash130.result
theorem hash130 : JFp_SHADigest.digest input130=value130 := by
  have law := JHe_SHARealization.tree0 ⟨130, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash130
theorem address130 : BinMerkle32Path.nodeInput (children value120 (JGc_TX2_HashBytes.state [254,14,130,135,247,205,115,79,107,166,89,198,117,201,141,89,5,159,55,163,8,155,248,77,113,14,97,138,39,216,58,208]))=input130 := by rfl
#print axioms address130
def tree130 : Tree := .branch tree120 (.supplied (JGc_TX2_HashBytes.state [254,14,130,135,247,205,115,79,107,166,89,198,117,201,141,89,5,159,55,163,8,155,248,77,113,14,97,138,39,216,58,208]))
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
def input131 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash131.message
def value131 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash131.result
theorem hash131 : JFp_SHADigest.digest input131=value131 := by
  have law := JHe_SHARealization.tree0 ⟨131, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash131
theorem address131 : BinMerkle32Path.nodeInput (children value121 (JGc_TX2_HashBytes.state [66,225,29,27,146,87,4,138,36,32,56,196,112,123,143,15,189,101,254,171,108,124,109,6,10,176,21,23,227,251,248,124]))=input131 := by rfl
#print axioms address131
def tree131 : Tree := .branch tree121 (.supplied (JGc_TX2_HashBytes.state [66,225,29,27,146,87,4,138,36,32,56,196,112,123,143,15,189,101,254,171,108,124,109,6,10,176,21,23,227,251,248,124]))
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
def input132 : Bytes := JGf_TX2_M0Roots.input161
def value132 : State := JGf_TX2_M0Roots.value161
theorem hash132 : JFp_SHADigest.digest input132=value132 := by
  have law := JHe_SHARealization.tree0 ⟨132, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash132
theorem address132 : BinMerkle32Path.nodeInput (children value122 (JGc_TX2_HashBytes.state [211,48,75,83,168,253,130,42,18,106,192,164,216,10,63,11,154,197,231,229,193,137,184,83,8,108,208,85,178,162,241,238]))=input132 := by rfl
#print axioms address132
def tree132 : Tree := .branch tree122 (.supplied (JGc_TX2_HashBytes.state [211,48,75,83,168,253,130,42,18,106,192,164,216,10,63,11,154,197,231,229,193,137,184,83,8,108,208,85,178,162,241,238]))
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
def input133 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash133.message
def value133 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash133.result
theorem hash133 : JFp_SHADigest.digest input133=value133 := by
  have law := JHe_SHARealization.tree0 ⟨133, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash133
theorem address133 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [188,195,79,74,213,254,47,21,205,195,209,166,40,141,13,9,97,84,152,93,102,191,158,16,165,158,96,183,21,248,100,55]) value123)=input133 := by rfl
#print axioms address133
def tree133 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [188,195,79,74,213,254,47,21,205,195,209,166,40,141,13,9,97,84,152,93,102,191,158,16,165,158,96,183,21,248,100,55])) tree123
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
def input134 : Bytes := JGf_TX2_M0Roots.input164
def value134 : State := JGf_TX2_M0Roots.value164
theorem hash134 : JFp_SHADigest.digest input134=value134 := by
  have law := JHe_SHARealization.tree0 ⟨134, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash134
theorem address134 : BinMerkle32Path.nodeInput (children value124 (JGc_TX2_HashBytes.state [187,76,51,74,59,158,50,38,87,85,221,77,230,156,105,93,240,119,203,74,247,195,29,178,103,62,94,105,26,121,227,113]))=input134 := by rfl
#print axioms address134
def tree134 : Tree := .branch tree124 (.supplied (JGc_TX2_HashBytes.state [187,76,51,74,59,158,50,38,87,85,221,77,230,156,105,93,240,119,203,74,247,195,29,178,103,62,94,105,26,121,227,113]))
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
def input135 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash135.message
def value135 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash135.result
theorem hash135 : JFp_SHADigest.digest input135=value135 := by
  have law := JHe_SHARealization.tree0 ⟨135, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
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
def input136 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash136.message
def value136 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash136.result
theorem hash136 : JFp_SHADigest.digest input136=value136 := by
  have law := JHe_SHARealization.tree0 ⟨136, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash136
theorem address136 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [73,20,30,234,180,192,147,217,52,97,111,104,183,231,180,130,207,5,13,223,218,43,82,64,97,51,35,212,32,222,55,133]) value127)=input136 := by rfl
#print axioms address136
def tree136 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [73,20,30,234,180,192,147,217,52,97,111,104,183,231,180,130,207,5,13,223,218,43,82,64,97,51,35,212,32,222,55,133])) tree127
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
def input137 : Bytes := JGf_TX2_M0Roots.input165
def value137 : State := JGf_TX2_M0Roots.value165
theorem hash137 : JFp_SHADigest.digest input137=value137 := by
  have law := JHe_SHARealization.tree0 ⟨137, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash137
theorem address137 : BinMerkle32Path.nodeInput (children value128 (JGc_TX2_HashBytes.state [216,39,125,52,179,150,49,41,23,46,71,20,106,158,77,0,176,105,197,0,58,234,126,198,61,27,243,66,155,192,133,151]))=input137 := by rfl
#print axioms address137
def tree137 : Tree := .branch tree128 (.supplied (JGc_TX2_HashBytes.state [216,39,125,52,179,150,49,41,23,46,71,20,106,158,77,0,176,105,197,0,58,234,126,198,61,27,243,66,155,192,133,151]))
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
def input138 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash138.message
def value138 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash138.result
theorem hash138 : JFp_SHADigest.digest input138=value138 := by
  have law := JHe_SHARealization.tree0 ⟨138, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash138
theorem address138 : BinMerkle32Path.nodeInput (children value129 (JGc_TX2_HashBytes.state [24,83,241,162,249,154,230,253,165,145,84,5,188,201,216,39,216,112,35,240,228,235,23,16,186,131,61,83,162,137,67,145]))=input138 := by rfl
#print axioms address138
def tree138 : Tree := .branch tree129 (.supplied (JGc_TX2_HashBytes.state [24,83,241,162,249,154,230,253,165,145,84,5,188,201,216,39,216,112,35,240,228,235,23,16,186,131,61,83,162,137,67,145]))
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
end AspisR1.JHe_C_Gr_M0Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_C_Gr_M0Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input139 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash139.message
def value139 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash139.result
theorem hash139 : JFp_SHADigest.digest input139=value139 := by
  have law := JHe_SHARealization.tree0 ⟨139, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash139
theorem address139 : BinMerkle32Path.nodeInput (children value130 (JGc_TX2_HashBytes.state [223,231,93,243,187,222,217,220,41,38,7,106,101,167,239,80,245,56,246,60,210,149,142,25,64,43,210,121,95,194,190,127]))=input139 := by rfl
#print axioms address139
def tree139 : Tree := .branch tree130 (.supplied (JGc_TX2_HashBytes.state [223,231,93,243,187,222,217,220,41,38,7,106,101,167,239,80,245,56,246,60,210,149,142,25,64,43,210,121,95,194,190,127]))
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
def input140 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash140.message
def value140 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash140.result
theorem hash140 : JFp_SHADigest.digest input140=value140 := by
  have law := JHe_SHARealization.tree0 ⟨140, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash140
theorem address140 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [229,54,3,47,115,163,190,8,7,45,5,100,244,76,80,249,22,225,43,200,84,178,81,224,91,144,25,21,23,167,131,241]) value131)=input140 := by rfl
#print axioms address140
def tree140 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [229,54,3,47,115,163,190,8,7,45,5,100,244,76,80,249,22,225,43,200,84,178,81,224,91,144,25,21,23,167,131,241])) tree131
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
def input141 : Bytes := JGf_TX2_M0Roots.input171
def value141 : State := JGf_TX2_M0Roots.value171
theorem hash141 : JFp_SHADigest.digest input141=value141 := by
  have law := JHe_SHARealization.tree0 ⟨141, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
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
def input142 : Bytes := JGf_TX2_M0Roots.input173
def value142 : State := JGf_TX2_M0Roots.value173
theorem hash142 : JFp_SHADigest.digest input142=value142 := by
  have law := JHe_SHARealization.tree0 ⟨142, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
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
def input143 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash143.message
def value143 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash143.result
theorem hash143 : JFp_SHADigest.digest input143=value143 := by
  have law := JHe_SHARealization.tree0 ⟨143, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash143
theorem address143 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [213,15,157,39,47,184,77,71,127,84,62,42,216,50,94,250,30,227,120,165,40,142,232,125,140,191,184,70,132,206,159,228]) value136)=input143 := by rfl
#print axioms address143
def tree143 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [213,15,157,39,47,184,77,71,127,84,62,42,216,50,94,250,30,227,120,165,40,142,232,125,140,191,184,70,132,206,159,228])) tree136
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
def input144 : Bytes := JGf_TX2_M0Roots.input174
def value144 : State := JGf_TX2_M0Roots.value174
theorem hash144 : JFp_SHADigest.digest input144=value144 := by
  have law := JHe_SHARealization.tree0 ⟨144, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash144
theorem address144 : BinMerkle32Path.nodeInput (children value137 (JGc_TX2_HashBytes.state [144,204,223,168,76,216,166,74,227,194,185,212,243,3,52,220,59,216,34,129,248,243,249,25,126,67,141,62,64,65,71,59]))=input144 := by rfl
#print axioms address144
def tree144 : Tree := .branch tree137 (.supplied (JGc_TX2_HashBytes.state [144,204,223,168,76,216,166,74,227,194,185,212,243,3,52,220,59,216,34,129,248,243,249,25,126,67,141,62,64,65,71,59]))
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
def input145 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash145.message
def value145 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash145.result
theorem hash145 : JFp_SHADigest.digest input145=value145 := by
  have law := JHe_SHARealization.tree0 ⟨145, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash145
theorem address145 : BinMerkle32Path.nodeInput (children value138 (JGc_TX2_HashBytes.state [78,208,3,215,108,77,215,153,252,92,186,74,30,93,232,95,87,47,70,138,104,13,138,115,161,80,31,90,248,143,34,113]))=input145 := by rfl
#print axioms address145
def tree145 : Tree := .branch tree138 (.supplied (JGc_TX2_HashBytes.state [78,208,3,215,108,77,215,153,252,92,186,74,30,93,232,95,87,47,70,138,104,13,138,115,161,80,31,90,248,143,34,113]))
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
end AspisR1.JHe_C_Gr_M0Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_C_Gr_M0Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input146 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash146.message
def value146 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash146.result
theorem hash146 : JFp_SHADigest.digest input146=value146 := by
  have law := JHe_SHARealization.tree0 ⟨146, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
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
def input147 : Bytes := JGf_TX2_M0Roots.input177
def value147 : State := JGf_TX2_M0Roots.value177
theorem hash147 : JFp_SHADigest.digest input147=value147 := by
  have law := JHe_SHARealization.tree0 ⟨147, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash147
theorem address147 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [76,205,219,41,141,231,162,252,144,59,33,119,50,181,0,227,188,209,249,74,188,31,19,122,76,172,71,94,11,48,185,91]) value141)=input147 := by rfl
#print axioms address147
def tree147 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [76,205,219,41,141,231,162,252,144,59,33,119,50,181,0,227,188,209,249,74,188,31,19,122,76,172,71,94,11,48,185,91])) tree141
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
def input148 : Bytes := JGf_TX2_M0Roots.input178
def value148 : State := JGf_TX2_M0Roots.value178
theorem hash148 : JFp_SHADigest.digest input148=value148 := by
  have law := JHe_SHARealization.tree0 ⟨148, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash148
theorem address148 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [195,209,74,206,189,24,33,14,245,28,250,102,99,222,20,28,120,118,240,28,23,39,12,127,80,80,115,112,100,54,252,25]) value142)=input148 := by rfl
#print axioms address148
def tree148 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [195,209,74,206,189,24,33,14,245,28,250,102,99,222,20,28,120,118,240,28,23,39,12,127,80,80,115,112,100,54,252,25])) tree142
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
def input149 : Bytes := JGf_TX2_M0Roots.input179
def value149 : State := JGf_TX2_M0Roots.value179
theorem hash149 : JFp_SHADigest.digest input149=value149 := by
  have law := JHe_SHARealization.tree0 ⟨149, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
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
def input150 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash150.message
def value150 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash150.result
theorem hash150 : JFp_SHADigest.digest input150=value150 := by
  have law := JHe_SHARealization.tree0 ⟨150, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash150
theorem address150 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [118,94,98,240,13,109,219,74,220,141,201,122,136,79,63,121,122,39,87,235,183,208,228,91,25,215,28,91,198,59,225,224]) value145)=input150 := by rfl
#print axioms address150
def tree150 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [118,94,98,240,13,109,219,74,220,141,201,122,136,79,63,121,122,39,87,235,183,208,228,91,25,215,28,91,198,59,225,224])) tree145
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
end AspisR1.JHe_C_Gr_M0Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_C_Gr_M0Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input151 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash151.message
def value151 : State := JFp_SHADigest.output JHe_C_Gr_M0.Hash151.result
theorem hash151 : JFp_SHADigest.digest input151=value151 := by
  have law := JHe_SHARealization.tree0 ⟨151, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash151
theorem address151 : BinMerkle32Path.nodeInput (children value146 (JGc_TX2_HashBytes.state [252,122,11,56,39,253,242,99,6,187,217,125,119,182,47,156,200,119,4,163,152,112,165,102,7,195,55,25,110,238,3,173]))=input151 := by rfl
#print axioms address151
def tree151 : Tree := .branch tree146 (.supplied (JGc_TX2_HashBytes.state [252,122,11,56,39,253,242,99,6,187,217,125,119,182,47,156,200,119,4,163,152,112,165,102,7,195,55,25,110,238,3,173]))
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
def input152 : Bytes := JGf_TX2_M0Roots.input181
def value152 : State := JGf_TX2_M0Roots.value181
theorem hash152 : JFp_SHADigest.digest input152=value152 := by
  have law := JHe_SHARealization.tree0 ⟨152, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
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
def input153 : Bytes := JGf_TX2_M0Roots.input182
def value153 : State := JGf_TX2_M0Roots.value182
theorem hash153 : JFp_SHADigest.digest input153=value153 := by
  have law := JHe_SHARealization.tree0 ⟨153, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
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
end AspisR1.JHe_C_Gr_M0Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_C_Gr_M0Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input154 : Bytes := JGf_TX2_M0Roots.input183
def value154 : State := JGf_TX2_M0Roots.value183
theorem hash154 : JFp_SHADigest.digest input154=value154 := by
  have law := JHe_SHARealization.tree0 ⟨154, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
  exact law
#print axioms hash154
theorem address154 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [186,70,164,226,215,82,40,99,140,117,51,93,72,25,161,89,123,6,162,192,130,252,253,134,91,166,4,240,224,19,155,103]) value151)=input154 := by rfl
#print axioms address154
def tree154 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [186,70,164,226,215,82,40,99,140,117,51,93,72,25,161,89,123,6,162,192,130,252,253,134,91,166,4,240,224,19,155,103])) tree151
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
def input155 : Bytes := JGf_TX2_M0Roots.input184
def value155 : State := JGf_TX2_M0Roots.value184
theorem hash155 : JFp_SHADigest.digest input155=value155 := by
  have law := JHe_SHARealization.tree0 ⟨155, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
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
end AspisR1.JHe_C_Gr_M0Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_C_Gr_M0Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input156 : Bytes := JGf_TX2_M0Roots.input185
def value156 : State := JGf_TX2_M0Roots.value185
theorem hash156 : JFp_SHADigest.digest input156=value156 := by
  have law := JHe_SHARealization.tree0 ⟨156, by decide⟩
  dsimp only [JHe_SHAInputs0.input,JHe_SHAInputs0.expected] at law
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
end AspisR1.JHe_C_Gr_M0Roots
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_C_Gr_M0Root
open Aeneas Aeneas.Std
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiBuild OracleDecisionMultiTree JHe_C_Gr_M0Roots

def retainedRoot : State := JGf_TX2_M0Root.retainedRoot

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
    (Port4B_KeyInstall.queries JFo_Prepared.value.queries) 0 0=indices := rfl
#print axioms selected_queries

theorem inhabited : ∃ (f : Nat → Bytes) (g : Nat → Nat → State),
    InputLaw f ∧ SiblingLaw g ∧
    root JFp_SHADigest.digest (build indices f g 18 0)=retainedRoot :=
  ⟨inputAt,siblingAt,(by intro b _;rfl),(by intro h _ b _;rfl),
    source inputAt siblingAt (by intro b _;rfl) (by intro h _ b _;rfl)⟩
#print axioms inhabited
end AspisR1.JHe_C_Gr_M0Root
end
end
