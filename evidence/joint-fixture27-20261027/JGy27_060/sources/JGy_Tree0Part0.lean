import JGc_TX2_HashBytes
import OracleDecisionMultiBuild
import JGy_Certs0_00
import JGy_Certs0_01
import JGy_Certs0_02
import JGy_Certs0_03
import JGc_TX2_ByteAppend
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGy_Gr_M0Roots
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
end AspisR1.JGy_Gr_M0Roots
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JGy_Gr_M0Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input000 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash000.message
def value000 : State := JFp_SHADigest.output JGy_Gr_M0.Hash000.result
theorem cast000_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash000.B00.input).map Fin.val=JGy_Gr_M0.Hash000.B00.input := by rfl
#print axioms cast000_0
theorem cast000_1 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash000.B01.input).map Fin.val=JGy_Gr_M0.Hash000.B01.input := by rfl
#print axioms cast000_1
theorem cast000_2 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash000.B02.input).map Fin.val=JGy_Gr_M0.Hash000.B02.input := by rfl
#print axioms cast000_2
theorem cast000_3 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash000.B03.input).map Fin.val=JGy_Gr_M0.Hash000.B03.input := by rfl
#print axioms cast000_3
theorem cast000_4 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash000.B04.input).map Fin.val=JGy_Gr_M0.Hash000.B04.input := by rfl
#print axioms cast000_4
theorem cast000_5 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash000.B05.input).map Fin.val=JGy_Gr_M0.Hash000.B05.input := by rfl
#print axioms cast000_5
theorem cast000_6 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash000.B06.input).map Fin.val=JGy_Gr_M0.Hash000.B06.input := by rfl
#print axioms cast000_6
theorem cast000_7 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash000.B07.input).map Fin.val=JGy_Gr_M0.Hash000.B07.input := by rfl
#print axioms cast000_7
theorem tail000 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash000.tail).map Fin.val=JGy_Gr_M0.Hash000.tail := by rfl
#print axioms tail000
theorem numeric000 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash000.message).map Fin.val=JGy_Gr_M0.Hash000.message := by
  simp only [JGy_Gr_M0.Hash000.message,JGy_Gr_M0.Hash000.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast000_0,cast000_1,cast000_2,cast000_3,cast000_4,cast000_5,cast000_6,cast000_7,tail000]
#print axioms numeric000
theorem hash000 : JFp_SHADigest.digest input000=value000 := by
  unfold input000 JFp_SHADigest.digest
  rw [numeric000,JGy_Gr_M0.Hash000.checked]
  rfl
#print axioms hash000
def tree000 : Tree := .opened input000
theorem root000 : root JFp_SHADigest.digest tree000=value000 := hash000
#print axioms root000
def input001 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash001.message
def value001 : State := JFp_SHADigest.output JGy_Gr_M0.Hash001.result
theorem cast001_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash001.B00.input).map Fin.val=JGy_Gr_M0.Hash001.B00.input := by rfl
#print axioms cast001_0
theorem cast001_1 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash001.B01.input).map Fin.val=JGy_Gr_M0.Hash001.B01.input := by rfl
#print axioms cast001_1
theorem cast001_2 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash001.B02.input).map Fin.val=JGy_Gr_M0.Hash001.B02.input := by rfl
#print axioms cast001_2
theorem cast001_3 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash001.B03.input).map Fin.val=JGy_Gr_M0.Hash001.B03.input := by rfl
#print axioms cast001_3
theorem cast001_4 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash001.B04.input).map Fin.val=JGy_Gr_M0.Hash001.B04.input := by rfl
#print axioms cast001_4
theorem cast001_5 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash001.B05.input).map Fin.val=JGy_Gr_M0.Hash001.B05.input := by rfl
#print axioms cast001_5
theorem cast001_6 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash001.B06.input).map Fin.val=JGy_Gr_M0.Hash001.B06.input := by rfl
#print axioms cast001_6
theorem cast001_7 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash001.B07.input).map Fin.val=JGy_Gr_M0.Hash001.B07.input := by rfl
#print axioms cast001_7
theorem tail001 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash001.tail).map Fin.val=JGy_Gr_M0.Hash001.tail := by rfl
#print axioms tail001
theorem numeric001 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash001.message).map Fin.val=JGy_Gr_M0.Hash001.message := by
  simp only [JGy_Gr_M0.Hash001.message,JGy_Gr_M0.Hash001.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast001_0,cast001_1,cast001_2,cast001_3,cast001_4,cast001_5,cast001_6,cast001_7,tail001]
#print axioms numeric001
theorem hash001 : JFp_SHADigest.digest input001=value001 := by
  unfold input001 JFp_SHADigest.digest
  rw [numeric001,JGy_Gr_M0.Hash001.checked]
  rfl
#print axioms hash001
def tree001 : Tree := .opened input001
theorem root001 : root JFp_SHADigest.digest tree001=value001 := hash001
#print axioms root001
def input002 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash002.message
def value002 : State := JFp_SHADigest.output JGy_Gr_M0.Hash002.result
theorem cast002_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash002.B00.input).map Fin.val=JGy_Gr_M0.Hash002.B00.input := by rfl
#print axioms cast002_0
theorem cast002_1 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash002.B01.input).map Fin.val=JGy_Gr_M0.Hash002.B01.input := by rfl
#print axioms cast002_1
theorem cast002_2 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash002.B02.input).map Fin.val=JGy_Gr_M0.Hash002.B02.input := by rfl
#print axioms cast002_2
theorem cast002_3 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash002.B03.input).map Fin.val=JGy_Gr_M0.Hash002.B03.input := by rfl
#print axioms cast002_3
theorem cast002_4 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash002.B04.input).map Fin.val=JGy_Gr_M0.Hash002.B04.input := by rfl
#print axioms cast002_4
theorem cast002_5 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash002.B05.input).map Fin.val=JGy_Gr_M0.Hash002.B05.input := by rfl
#print axioms cast002_5
theorem cast002_6 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash002.B06.input).map Fin.val=JGy_Gr_M0.Hash002.B06.input := by rfl
#print axioms cast002_6
theorem cast002_7 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash002.B07.input).map Fin.val=JGy_Gr_M0.Hash002.B07.input := by rfl
#print axioms cast002_7
theorem tail002 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash002.tail).map Fin.val=JGy_Gr_M0.Hash002.tail := by rfl
#print axioms tail002
theorem numeric002 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash002.message).map Fin.val=JGy_Gr_M0.Hash002.message := by
  simp only [JGy_Gr_M0.Hash002.message,JGy_Gr_M0.Hash002.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast002_0,cast002_1,cast002_2,cast002_3,cast002_4,cast002_5,cast002_6,cast002_7,tail002]
#print axioms numeric002
theorem hash002 : JFp_SHADigest.digest input002=value002 := by
  unfold input002 JFp_SHADigest.digest
  rw [numeric002,JGy_Gr_M0.Hash002.checked]
  rfl
#print axioms hash002
def tree002 : Tree := .opened input002
theorem root002 : root JFp_SHADigest.digest tree002=value002 := hash002
#print axioms root002
def input003 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash003.message
def value003 : State := JFp_SHADigest.output JGy_Gr_M0.Hash003.result
theorem cast003_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash003.B00.input).map Fin.val=JGy_Gr_M0.Hash003.B00.input := by rfl
#print axioms cast003_0
theorem cast003_1 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash003.B01.input).map Fin.val=JGy_Gr_M0.Hash003.B01.input := by rfl
#print axioms cast003_1
theorem cast003_2 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash003.B02.input).map Fin.val=JGy_Gr_M0.Hash003.B02.input := by rfl
#print axioms cast003_2
theorem cast003_3 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash003.B03.input).map Fin.val=JGy_Gr_M0.Hash003.B03.input := by rfl
#print axioms cast003_3
theorem cast003_4 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash003.B04.input).map Fin.val=JGy_Gr_M0.Hash003.B04.input := by rfl
#print axioms cast003_4
theorem cast003_5 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash003.B05.input).map Fin.val=JGy_Gr_M0.Hash003.B05.input := by rfl
#print axioms cast003_5
theorem cast003_6 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash003.B06.input).map Fin.val=JGy_Gr_M0.Hash003.B06.input := by rfl
#print axioms cast003_6
theorem cast003_7 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash003.B07.input).map Fin.val=JGy_Gr_M0.Hash003.B07.input := by rfl
#print axioms cast003_7
theorem tail003 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash003.tail).map Fin.val=JGy_Gr_M0.Hash003.tail := by rfl
#print axioms tail003
theorem numeric003 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash003.message).map Fin.val=JGy_Gr_M0.Hash003.message := by
  simp only [JGy_Gr_M0.Hash003.message,JGy_Gr_M0.Hash003.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast003_0,cast003_1,cast003_2,cast003_3,cast003_4,cast003_5,cast003_6,cast003_7,tail003]
#print axioms numeric003
theorem hash003 : JFp_SHADigest.digest input003=value003 := by
  unfold input003 JFp_SHADigest.digest
  rw [numeric003,JGy_Gr_M0.Hash003.checked]
  rfl
#print axioms hash003
def tree003 : Tree := .opened input003
theorem root003 : root JFp_SHADigest.digest tree003=value003 := hash003
#print axioms root003
def input004 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash004.message
def value004 : State := JFp_SHADigest.output JGy_Gr_M0.Hash004.result
theorem cast004_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash004.B00.input).map Fin.val=JGy_Gr_M0.Hash004.B00.input := by rfl
#print axioms cast004_0
theorem cast004_1 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash004.B01.input).map Fin.val=JGy_Gr_M0.Hash004.B01.input := by rfl
#print axioms cast004_1
theorem cast004_2 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash004.B02.input).map Fin.val=JGy_Gr_M0.Hash004.B02.input := by rfl
#print axioms cast004_2
theorem cast004_3 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash004.B03.input).map Fin.val=JGy_Gr_M0.Hash004.B03.input := by rfl
#print axioms cast004_3
theorem cast004_4 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash004.B04.input).map Fin.val=JGy_Gr_M0.Hash004.B04.input := by rfl
#print axioms cast004_4
theorem cast004_5 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash004.B05.input).map Fin.val=JGy_Gr_M0.Hash004.B05.input := by rfl
#print axioms cast004_5
theorem cast004_6 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash004.B06.input).map Fin.val=JGy_Gr_M0.Hash004.B06.input := by rfl
#print axioms cast004_6
theorem cast004_7 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash004.B07.input).map Fin.val=JGy_Gr_M0.Hash004.B07.input := by rfl
#print axioms cast004_7
theorem tail004 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash004.tail).map Fin.val=JGy_Gr_M0.Hash004.tail := by rfl
#print axioms tail004
theorem numeric004 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash004.message).map Fin.val=JGy_Gr_M0.Hash004.message := by
  simp only [JGy_Gr_M0.Hash004.message,JGy_Gr_M0.Hash004.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast004_0,cast004_1,cast004_2,cast004_3,cast004_4,cast004_5,cast004_6,cast004_7,tail004]
#print axioms numeric004
theorem hash004 : JFp_SHADigest.digest input004=value004 := by
  unfold input004 JFp_SHADigest.digest
  rw [numeric004,JGy_Gr_M0.Hash004.checked]
  rfl
#print axioms hash004
def tree004 : Tree := .opened input004
theorem root004 : root JFp_SHADigest.digest tree004=value004 := hash004
#print axioms root004
def input005 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash005.message
def value005 : State := JFp_SHADigest.output JGy_Gr_M0.Hash005.result
theorem cast005_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash005.B00.input).map Fin.val=JGy_Gr_M0.Hash005.B00.input := by rfl
#print axioms cast005_0
theorem cast005_1 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash005.B01.input).map Fin.val=JGy_Gr_M0.Hash005.B01.input := by rfl
#print axioms cast005_1
theorem cast005_2 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash005.B02.input).map Fin.val=JGy_Gr_M0.Hash005.B02.input := by rfl
#print axioms cast005_2
theorem cast005_3 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash005.B03.input).map Fin.val=JGy_Gr_M0.Hash005.B03.input := by rfl
#print axioms cast005_3
theorem cast005_4 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash005.B04.input).map Fin.val=JGy_Gr_M0.Hash005.B04.input := by rfl
#print axioms cast005_4
theorem cast005_5 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash005.B05.input).map Fin.val=JGy_Gr_M0.Hash005.B05.input := by rfl
#print axioms cast005_5
theorem cast005_6 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash005.B06.input).map Fin.val=JGy_Gr_M0.Hash005.B06.input := by rfl
#print axioms cast005_6
theorem cast005_7 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash005.B07.input).map Fin.val=JGy_Gr_M0.Hash005.B07.input := by rfl
#print axioms cast005_7
theorem tail005 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash005.tail).map Fin.val=JGy_Gr_M0.Hash005.tail := by rfl
#print axioms tail005
theorem numeric005 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash005.message).map Fin.val=JGy_Gr_M0.Hash005.message := by
  simp only [JGy_Gr_M0.Hash005.message,JGy_Gr_M0.Hash005.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast005_0,cast005_1,cast005_2,cast005_3,cast005_4,cast005_5,cast005_6,cast005_7,tail005]
#print axioms numeric005
theorem hash005 : JFp_SHADigest.digest input005=value005 := by
  unfold input005 JFp_SHADigest.digest
  rw [numeric005,JGy_Gr_M0.Hash005.checked]
  rfl
#print axioms hash005
def tree005 : Tree := .opened input005
theorem root005 : root JFp_SHADigest.digest tree005=value005 := hash005
#print axioms root005
def input006 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash006.message
def value006 : State := JFp_SHADigest.output JGy_Gr_M0.Hash006.result
theorem cast006_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash006.B00.input).map Fin.val=JGy_Gr_M0.Hash006.B00.input := by rfl
#print axioms cast006_0
theorem cast006_1 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash006.B01.input).map Fin.val=JGy_Gr_M0.Hash006.B01.input := by rfl
#print axioms cast006_1
theorem cast006_2 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash006.B02.input).map Fin.val=JGy_Gr_M0.Hash006.B02.input := by rfl
#print axioms cast006_2
theorem cast006_3 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash006.B03.input).map Fin.val=JGy_Gr_M0.Hash006.B03.input := by rfl
#print axioms cast006_3
theorem cast006_4 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash006.B04.input).map Fin.val=JGy_Gr_M0.Hash006.B04.input := by rfl
#print axioms cast006_4
theorem cast006_5 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash006.B05.input).map Fin.val=JGy_Gr_M0.Hash006.B05.input := by rfl
#print axioms cast006_5
theorem cast006_6 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash006.B06.input).map Fin.val=JGy_Gr_M0.Hash006.B06.input := by rfl
#print axioms cast006_6
theorem cast006_7 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash006.B07.input).map Fin.val=JGy_Gr_M0.Hash006.B07.input := by rfl
#print axioms cast006_7
theorem tail006 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash006.tail).map Fin.val=JGy_Gr_M0.Hash006.tail := by rfl
#print axioms tail006
theorem numeric006 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash006.message).map Fin.val=JGy_Gr_M0.Hash006.message := by
  simp only [JGy_Gr_M0.Hash006.message,JGy_Gr_M0.Hash006.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast006_0,cast006_1,cast006_2,cast006_3,cast006_4,cast006_5,cast006_6,cast006_7,tail006]
#print axioms numeric006
theorem hash006 : JFp_SHADigest.digest input006=value006 := by
  unfold input006 JFp_SHADigest.digest
  rw [numeric006,JGy_Gr_M0.Hash006.checked]
  rfl
#print axioms hash006
def tree006 : Tree := .opened input006
theorem root006 : root JFp_SHADigest.digest tree006=value006 := hash006
#print axioms root006
def input007 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash007.message
def value007 : State := JFp_SHADigest.output JGy_Gr_M0.Hash007.result
theorem cast007_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash007.B00.input).map Fin.val=JGy_Gr_M0.Hash007.B00.input := by rfl
#print axioms cast007_0
theorem cast007_1 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash007.B01.input).map Fin.val=JGy_Gr_M0.Hash007.B01.input := by rfl
#print axioms cast007_1
theorem cast007_2 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash007.B02.input).map Fin.val=JGy_Gr_M0.Hash007.B02.input := by rfl
#print axioms cast007_2
theorem cast007_3 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash007.B03.input).map Fin.val=JGy_Gr_M0.Hash007.B03.input := by rfl
#print axioms cast007_3
theorem cast007_4 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash007.B04.input).map Fin.val=JGy_Gr_M0.Hash007.B04.input := by rfl
#print axioms cast007_4
theorem cast007_5 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash007.B05.input).map Fin.val=JGy_Gr_M0.Hash007.B05.input := by rfl
#print axioms cast007_5
theorem cast007_6 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash007.B06.input).map Fin.val=JGy_Gr_M0.Hash007.B06.input := by rfl
#print axioms cast007_6
theorem cast007_7 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash007.B07.input).map Fin.val=JGy_Gr_M0.Hash007.B07.input := by rfl
#print axioms cast007_7
theorem tail007 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash007.tail).map Fin.val=JGy_Gr_M0.Hash007.tail := by rfl
#print axioms tail007
theorem numeric007 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash007.message).map Fin.val=JGy_Gr_M0.Hash007.message := by
  simp only [JGy_Gr_M0.Hash007.message,JGy_Gr_M0.Hash007.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast007_0,cast007_1,cast007_2,cast007_3,cast007_4,cast007_5,cast007_6,cast007_7,tail007]
#print axioms numeric007
theorem hash007 : JFp_SHADigest.digest input007=value007 := by
  unfold input007 JFp_SHADigest.digest
  rw [numeric007,JGy_Gr_M0.Hash007.checked]
  rfl
#print axioms hash007
def tree007 : Tree := .opened input007
theorem root007 : root JFp_SHADigest.digest tree007=value007 := hash007
#print axioms root007
def input008 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash008.message
def value008 : State := JFp_SHADigest.output JGy_Gr_M0.Hash008.result
theorem cast008_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash008.B00.input).map Fin.val=JGy_Gr_M0.Hash008.B00.input := by rfl
#print axioms cast008_0
theorem cast008_1 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash008.B01.input).map Fin.val=JGy_Gr_M0.Hash008.B01.input := by rfl
#print axioms cast008_1
theorem cast008_2 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash008.B02.input).map Fin.val=JGy_Gr_M0.Hash008.B02.input := by rfl
#print axioms cast008_2
theorem cast008_3 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash008.B03.input).map Fin.val=JGy_Gr_M0.Hash008.B03.input := by rfl
#print axioms cast008_3
theorem cast008_4 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash008.B04.input).map Fin.val=JGy_Gr_M0.Hash008.B04.input := by rfl
#print axioms cast008_4
theorem cast008_5 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash008.B05.input).map Fin.val=JGy_Gr_M0.Hash008.B05.input := by rfl
#print axioms cast008_5
theorem cast008_6 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash008.B06.input).map Fin.val=JGy_Gr_M0.Hash008.B06.input := by rfl
#print axioms cast008_6
theorem cast008_7 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash008.B07.input).map Fin.val=JGy_Gr_M0.Hash008.B07.input := by rfl
#print axioms cast008_7
theorem tail008 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash008.tail).map Fin.val=JGy_Gr_M0.Hash008.tail := by rfl
#print axioms tail008
theorem numeric008 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash008.message).map Fin.val=JGy_Gr_M0.Hash008.message := by
  simp only [JGy_Gr_M0.Hash008.message,JGy_Gr_M0.Hash008.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast008_0,cast008_1,cast008_2,cast008_3,cast008_4,cast008_5,cast008_6,cast008_7,tail008]
#print axioms numeric008
theorem hash008 : JFp_SHADigest.digest input008=value008 := by
  unfold input008 JFp_SHADigest.digest
  rw [numeric008,JGy_Gr_M0.Hash008.checked]
  rfl
#print axioms hash008
def tree008 : Tree := .opened input008
theorem root008 : root JFp_SHADigest.digest tree008=value008 := hash008
#print axioms root008
def input009 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash009.message
def value009 : State := JFp_SHADigest.output JGy_Gr_M0.Hash009.result
theorem cast009_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash009.B00.input).map Fin.val=JGy_Gr_M0.Hash009.B00.input := by rfl
#print axioms cast009_0
theorem cast009_1 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash009.B01.input).map Fin.val=JGy_Gr_M0.Hash009.B01.input := by rfl
#print axioms cast009_1
theorem cast009_2 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash009.B02.input).map Fin.val=JGy_Gr_M0.Hash009.B02.input := by rfl
#print axioms cast009_2
theorem cast009_3 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash009.B03.input).map Fin.val=JGy_Gr_M0.Hash009.B03.input := by rfl
#print axioms cast009_3
theorem cast009_4 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash009.B04.input).map Fin.val=JGy_Gr_M0.Hash009.B04.input := by rfl
#print axioms cast009_4
theorem cast009_5 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash009.B05.input).map Fin.val=JGy_Gr_M0.Hash009.B05.input := by rfl
#print axioms cast009_5
theorem cast009_6 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash009.B06.input).map Fin.val=JGy_Gr_M0.Hash009.B06.input := by rfl
#print axioms cast009_6
theorem cast009_7 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash009.B07.input).map Fin.val=JGy_Gr_M0.Hash009.B07.input := by rfl
#print axioms cast009_7
theorem tail009 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash009.tail).map Fin.val=JGy_Gr_M0.Hash009.tail := by rfl
#print axioms tail009
theorem numeric009 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash009.message).map Fin.val=JGy_Gr_M0.Hash009.message := by
  simp only [JGy_Gr_M0.Hash009.message,JGy_Gr_M0.Hash009.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast009_0,cast009_1,cast009_2,cast009_3,cast009_4,cast009_5,cast009_6,cast009_7,tail009]
#print axioms numeric009
theorem hash009 : JFp_SHADigest.digest input009=value009 := by
  unfold input009 JFp_SHADigest.digest
  rw [numeric009,JGy_Gr_M0.Hash009.checked]
  rfl
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
end AspisR1.JGy_Gr_M0Roots
end
