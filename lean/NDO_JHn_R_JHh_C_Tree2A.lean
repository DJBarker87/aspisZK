import NDO_JGc_TX2_ByteAppend
import NDO_JGc_TX2_HashBytes
import NDO_JGc_TX2_M2Root
import NDO_JGe_View
import NDO_JHe_SHARealization
import OracleDecisionMultiBuild
section
variable [sha : AspisR1.JHe_SHARealization]
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_C_Gr_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def indices : List Nat := [23374,36882,54205,61474,52342,48079,16398,45964,48273,39953]
def bases (height : Nat) : List Nat := match height with
  | 0 => [16399,23375,36883,39952,45965,48078,48272,52343,54204,61475]
  | 1 => [16396,23372,36880,39954,45966,48076,48274,52340,54206,61472]
  | 2 => [16392,23368,36884,39956,45960,48072,48276,52336,54200,61476]
  | 3 => [16384,23360,36888,39960,45952,48064,48280,52344,54192,61480]
  | 4 => [16400,23376,36864,39936,45968,48080,48256,52320,54176,61488]
  | 5 => [16416,23392,36896,39968,45984,48096,48288,52288,54144,61440]
  | 6 => [16448,23296,36928,40000,46016,48000,48320,52224,54208,61504]
  | 7 => [16512,23424,36992,40064,45824,47872,48128,52352,54016,61568]
  | 8 => [16640,23040,37120,40192,45568,47616,48384,52480,53760,61696]
  | 9 => [16896,22528,37376,40448,45056,47104,48640,52736,53248,61952]
  | 10 => [17408,23552,37888,38912,46080,51200,54272,62464]
  | 11 => [18432,20480,49152,55296,63488]
  | 12 => [32768,40960,57344]
  | 13 => [24576]
  | 14 => [0]
  | 15 => []
  | 16 => [65536]
  | 17 => [131072]
  | _ => []
def siblingAt (height base : Nat) : State := match height with
  | 0 => match base with
    | 16399 => JGc_TX2_HashBytes.state [59,19,2,0,169,92,95,200,80,218,215,254,63,229,202,59,255,62,34,152,178,252,191,0,154,18,160,100,127,195,236,140]
    | 23375 => JGc_TX2_HashBytes.state [157,250,64,85,13,19,77,148,29,212,154,20,167,121,250,170,228,41,109,0,8,18,69,253,189,146,93,22,157,14,22,87]
    | 36883 => JGc_TX2_HashBytes.state [200,118,125,216,76,197,168,252,66,166,175,172,159,132,202,150,238,183,109,182,215,230,204,48,38,187,56,127,4,148,156,91]
    | 39952 => JGc_TX2_HashBytes.state [212,242,126,73,163,36,230,105,69,72,183,184,38,238,26,19,12,17,111,26,165,123,45,242,32,167,200,96,233,228,57,69]
    | 45965 => JGc_TX2_HashBytes.state [82,191,91,24,205,192,231,67,121,98,110,223,12,88,203,10,225,19,214,220,215,156,248,27,81,185,96,114,168,9,78,14]
    | 48078 => JGc_TX2_HashBytes.state [133,193,193,242,18,135,93,234,189,30,36,64,27,220,184,7,144,101,221,10,71,70,1,222,233,39,21,21,157,144,185,165]
    | 48272 => JGc_TX2_HashBytes.state [98,207,122,12,13,116,247,26,12,101,199,43,169,75,183,42,84,151,241,175,190,14,219,79,255,20,41,230,147,83,213,218]
    | 52343 => JGc_TX2_HashBytes.state [80,151,219,68,228,150,38,180,212,171,144,75,12,109,31,147,55,20,109,143,198,101,8,244,28,178,249,159,227,18,96,225]
    | 54204 => JGc_TX2_HashBytes.state [52,8,95,13,105,245,56,139,100,239,201,233,12,0,102,84,64,208,206,160,240,46,2,104,110,111,39,205,28,111,190,253]
    | 61475 => JGc_TX2_HashBytes.state [58,245,80,88,37,211,128,187,23,227,240,163,220,232,101,152,153,152,109,88,252,196,25,246,154,119,211,100,33,86,172,156]
    | _ => JGc_TX2_HashBytes.state []
  | 1 => match base with
    | 16396 => JGc_TX2_HashBytes.state [179,57,66,105,91,88,148,117,98,202,23,143,65,232,228,202,11,120,180,169,158,103,229,95,32,200,194,222,112,210,131,3]
    | 23372 => JGc_TX2_HashBytes.state [107,125,164,219,26,17,227,219,9,238,70,117,237,24,14,190,244,82,156,147,101,254,180,116,45,28,98,62,32,57,198,231]
    | 36880 => JGc_TX2_HashBytes.state [47,141,216,252,197,166,70,210,81,178,177,38,252,245,63,138,90,15,229,137,148,184,253,55,25,241,20,143,57,249,114,136]
    | 39954 => JGc_TX2_HashBytes.state [149,82,100,53,22,189,226,92,234,12,68,130,93,161,194,244,133,5,197,140,65,188,52,164,91,170,182,75,33,104,183,190]
    | 45966 => JGc_TX2_HashBytes.state [153,116,202,141,139,28,14,167,146,44,161,154,154,150,133,164,1,97,251,129,67,238,209,205,47,38,121,56,63,172,240,59]
    | 48076 => JGc_TX2_HashBytes.state [59,32,195,3,19,154,209,61,43,191,156,113,54,238,181,159,13,241,5,114,216,99,9,206,156,21,132,19,133,169,28,149]
    | 48274 => JGc_TX2_HashBytes.state [160,150,74,176,230,87,55,149,137,239,129,40,128,128,155,164,228,20,84,10,90,170,136,112,178,54,174,236,18,211,106,20]
    | 52340 => JGc_TX2_HashBytes.state [228,12,216,182,13,245,17,244,56,172,67,209,165,228,216,245,36,207,219,252,76,56,80,233,32,172,129,152,94,206,186,32]
    | 54206 => JGc_TX2_HashBytes.state [188,221,111,216,18,217,30,136,2,223,90,61,66,1,162,238,11,64,13,125,84,37,35,58,104,178,136,54,100,76,168,41]
    | 61472 => JGc_TX2_HashBytes.state [41,72,84,86,132,77,231,158,173,214,235,170,124,62,85,192,227,36,17,210,21,206,189,190,89,89,69,162,196,143,89,105]
    | _ => JGc_TX2_HashBytes.state []
  | 2 => match base with
    | 16392 => JGc_TX2_HashBytes.state [194,245,184,247,117,235,145,13,126,50,69,25,98,255,22,215,181,195,177,122,110,168,180,137,116,143,124,181,73,28,5,69]
    | 23368 => JGc_TX2_HashBytes.state [254,249,253,171,105,7,200,164,192,146,148,22,234,243,156,193,204,205,200,27,131,103,94,225,10,168,70,82,231,124,252,35]
    | 36884 => JGc_TX2_HashBytes.state [186,93,169,162,221,9,97,47,195,23,151,178,51,170,82,124,130,6,105,43,70,227,136,131,203,240,135,148,160,124,113,200]
    | 39956 => JGc_TX2_HashBytes.state [117,14,241,103,80,121,161,108,21,104,179,229,107,125,84,31,189,134,142,185,135,253,55,234,139,89,193,114,221,115,46,128]
    | 45960 => JGc_TX2_HashBytes.state [252,199,160,112,92,68,47,54,9,188,58,105,45,11,24,100,63,52,109,70,105,61,240,30,194,73,210,110,30,137,146,5]
    | 48072 => JGc_TX2_HashBytes.state [235,50,176,191,189,100,44,247,120,2,40,116,130,231,48,6,150,118,123,187,248,252,9,165,185,26,191,183,209,65,102,221]
    | 48276 => JGc_TX2_HashBytes.state [220,245,95,204,173,38,219,209,33,203,132,173,44,78,7,132,64,185,24,223,162,215,156,66,211,174,245,196,96,216,230,66]
    | 52336 => JGc_TX2_HashBytes.state [106,76,243,247,175,186,175,214,242,19,159,62,63,228,244,231,157,110,252,193,106,75,125,234,209,149,240,59,55,204,191,128]
    | 54200 => JGc_TX2_HashBytes.state [236,64,23,201,253,208,86,58,10,82,89,203,137,84,53,121,112,94,44,47,16,0,83,247,169,8,40,153,151,170,22,238]
    | 61476 => JGc_TX2_HashBytes.state [202,189,29,169,70,123,183,226,47,76,15,140,170,67,27,238,204,183,171,51,116,132,60,183,181,124,58,4,43,84,219,250]
    | _ => JGc_TX2_HashBytes.state []
  | 3 => match base with
    | 16384 => JGc_TX2_HashBytes.state [249,97,95,72,195,239,230,133,231,204,195,159,197,242,53,210,181,126,161,238,155,106,151,110,88,108,146,232,8,121,248,62]
    | 23360 => JGc_TX2_HashBytes.state [179,62,84,67,145,245,19,145,0,76,183,216,254,164,78,100,235,197,149,22,181,176,111,192,90,35,170,224,190,165,169,130]
    | 36888 => JGc_TX2_HashBytes.state [169,21,194,86,169,83,68,57,145,59,224,82,4,255,183,95,137,88,198,233,243,230,177,89,132,186,175,162,5,209,79,171]
    | 39960 => JGc_TX2_HashBytes.state [249,125,104,173,124,225,131,121,245,201,10,19,165,30,103,92,67,162,190,80,0,142,172,114,183,72,182,186,237,7,60,125]
    | 45952 => JGc_TX2_HashBytes.state [195,11,91,13,242,157,237,14,230,48,53,152,68,28,146,173,39,23,72,54,22,225,121,215,107,229,54,60,170,68,238,72]
    | 48064 => JGc_TX2_HashBytes.state [179,112,196,108,44,160,62,125,194,38,29,185,108,215,4,140,11,246,68,159,82,31,45,80,100,31,239,92,243,120,250,219]
    | 48280 => JGc_TX2_HashBytes.state [62,167,250,165,65,31,182,78,176,251,194,75,161,83,115,3,81,118,25,197,64,0,255,47,232,78,185,56,42,93,69,86]
    | 52344 => JGc_TX2_HashBytes.state [57,54,77,49,101,42,95,108,7,193,128,156,160,108,172,205,176,94,234,119,178,60,14,61,107,83,83,99,46,128,55,36]
    | 54192 => JGc_TX2_HashBytes.state [162,78,44,26,160,83,123,134,218,232,6,213,29,159,101,194,116,107,147,229,122,88,91,82,166,42,5,120,181,179,197,167]
    | 61480 => JGc_TX2_HashBytes.state [16,233,214,196,219,235,118,177,214,211,77,23,126,52,140,234,128,247,206,133,105,180,135,29,2,2,189,128,41,90,9,193]
    | _ => JGc_TX2_HashBytes.state []
  | 4 => match base with
    | 16400 => JGc_TX2_HashBytes.state [65,234,38,73,66,178,230,20,65,121,30,37,225,239,162,80,19,158,198,194,173,16,25,109,108,151,246,72,8,249,139,52]
    | 23376 => JGc_TX2_HashBytes.state [160,196,206,167,250,112,3,28,143,138,174,230,166,61,96,100,21,194,32,169,75,99,235,184,138,126,251,198,150,238,190,52]
    | 36864 => JGc_TX2_HashBytes.state [116,149,89,253,254,19,246,16,170,116,173,230,189,196,143,72,229,205,60,207,4,27,195,29,163,34,89,116,252,50,119,14]
    | 39936 => JGc_TX2_HashBytes.state [55,78,39,200,76,202,7,1,140,171,82,253,129,15,177,0,61,7,55,23,33,240,211,141,37,123,101,117,182,39,64,187]
    | 45968 => JGc_TX2_HashBytes.state [214,125,42,28,128,37,83,168,43,239,170,218,176,52,50,65,50,39,88,130,133,76,132,84,182,217,3,23,118,224,99,151]
    | 48080 => JGc_TX2_HashBytes.state [59,77,103,151,197,77,27,177,181,138,84,152,90,178,108,53,229,207,203,146,23,110,171,197,65,83,20,196,13,21,172,117]
    | 48256 => JGc_TX2_HashBytes.state [121,155,170,137,92,23,153,245,180,227,87,14,77,237,32,32,201,175,78,100,37,206,227,60,30,169,227,45,145,173,245,195]
    | 52320 => JGc_TX2_HashBytes.state [77,20,168,204,126,214,237,104,69,211,193,212,69,14,169,89,19,73,26,130,68,35,49,151,26,120,232,187,43,24,108,230]
    | 54176 => JGc_TX2_HashBytes.state [219,113,206,154,96,101,14,206,79,208,91,12,62,43,111,15,159,175,162,128,58,189,130,180,129,14,209,29,246,135,107,199]
    | 61488 => JGc_TX2_HashBytes.state [179,218,162,212,20,131,120,109,52,129,111,92,132,18,158,30,184,98,130,212,185,233,158,145,127,59,221,46,0,214,80,21]
    | _ => JGc_TX2_HashBytes.state []
  | 5 => match base with
    | 16416 => JGc_TX2_HashBytes.state [125,62,11,58,152,121,161,20,87,123,59,146,157,58,136,241,164,159,33,232,66,172,208,243,124,111,180,225,182,173,183,11]
    | 23392 => JGc_TX2_HashBytes.state [108,85,227,67,255,107,240,217,131,85,181,219,24,10,252,188,214,141,198,133,159,73,116,15,37,35,242,27,251,66,11,3]
    | 36896 => JGc_TX2_HashBytes.state [20,69,131,244,4,224,142,147,45,30,160,115,55,150,86,41,62,233,146,3,5,126,120,19,244,204,58,53,181,84,196,197]
    | 39968 => JGc_TX2_HashBytes.state [46,207,213,156,44,97,223,5,239,95,131,76,225,10,249,132,169,237,91,238,24,122,79,76,77,172,35,29,240,46,161,81]
    | 45984 => JGc_TX2_HashBytes.state [95,12,139,86,115,166,43,216,121,70,107,251,72,70,51,33,19,180,64,129,152,241,136,194,104,235,4,19,207,59,71,38]
    | 48096 => JGc_TX2_HashBytes.state [96,144,30,173,153,163,192,34,238,70,42,254,168,235,204,203,30,126,228,206,111,202,34,173,110,50,39,31,76,7,91,117]
    | 48288 => JGc_TX2_HashBytes.state [193,40,69,139,235,218,184,141,95,6,104,82,149,17,63,148,181,126,57,142,185,25,231,88,16,185,114,171,2,44,236,81]
    | 52288 => JGc_TX2_HashBytes.state [108,244,30,13,4,164,224,60,6,70,5,194,113,19,224,179,103,199,233,246,124,170,2,80,220,146,148,253,253,191,218,219]
    | 54144 => JGc_TX2_HashBytes.state [77,83,165,84,145,44,241,189,189,116,178,122,62,239,124,255,41,4,75,96,207,188,221,80,196,143,108,51,218,23,202,213]
    | 61440 => JGc_TX2_HashBytes.state [111,137,193,249,230,246,19,197,115,7,165,255,66,184,205,55,249,202,250,176,180,214,60,254,61,126,78,118,255,181,149,35]
    | _ => JGc_TX2_HashBytes.state []
  | 6 => match base with
    | 16448 => JGc_TX2_HashBytes.state [12,35,6,54,189,41,166,74,28,227,63,181,204,131,135,75,78,199,125,83,131,232,162,74,16,255,240,44,226,253,152,131]
    | 23296 => JGc_TX2_HashBytes.state [34,202,202,246,204,161,168,147,72,248,145,59,46,233,17,80,67,226,203,239,118,214,122,140,141,112,234,72,115,236,35,119]
    | 36928 => JGc_TX2_HashBytes.state [233,186,25,148,101,33,33,145,191,159,134,50,19,208,18,164,241,22,203,112,242,116,2,159,74,87,212,75,68,12,27,203]
    | 40000 => JGc_TX2_HashBytes.state [172,95,38,161,233,39,109,98,162,182,95,62,119,94,97,67,209,214,59,41,199,165,99,92,109,80,89,57,162,40,2,101]
    | 46016 => JGc_TX2_HashBytes.state [103,108,72,109,95,12,246,45,50,177,228,166,118,36,249,156,201,210,30,254,219,199,140,75,105,48,211,178,152,240,35,25]
    | 48000 => JGc_TX2_HashBytes.state [76,138,139,110,125,144,229,21,210,24,82,54,6,198,0,84,11,57,149,77,118,158,174,117,16,240,50,61,167,224,164,114]
    | 48320 => JGc_TX2_HashBytes.state [92,18,27,186,69,57,105,145,26,193,234,90,166,206,223,1,124,10,44,87,174,35,213,59,133,136,95,93,181,15,102,76]
    | 52224 => JGc_TX2_HashBytes.state [221,19,169,114,80,134,201,224,126,254,210,16,35,216,131,101,98,130,177,176,105,17,245,221,225,119,36,214,154,102,135,54]
    | 54208 => JGc_TX2_HashBytes.state [109,164,95,10,124,67,109,255,131,97,215,20,161,76,7,61,239,85,118,134,154,43,70,21,176,103,66,1,84,203,21,178]
    | 61504 => JGc_TX2_HashBytes.state [189,12,56,31,97,219,222,72,85,148,145,20,206,134,123,106,158,78,125,165,158,116,184,132,122,139,219,64,2,74,255,189]
    | _ => JGc_TX2_HashBytes.state []
  | 7 => match base with
    | 16512 => JGc_TX2_HashBytes.state [40,66,57,248,171,64,19,248,144,29,218,123,161,176,117,253,56,239,96,55,49,89,217,26,77,172,100,4,82,114,8,47]
    | 23424 => JGc_TX2_HashBytes.state [120,18,210,66,139,22,89,122,216,63,152,111,19,111,250,236,51,117,22,85,177,55,233,164,124,98,214,151,43,78,253,217]
    | 36992 => JGc_TX2_HashBytes.state [103,178,124,35,134,30,155,148,34,121,100,244,172,217,64,95,40,79,185,187,244,242,175,24,223,94,11,7,90,165,205,4]
    | 40064 => JGc_TX2_HashBytes.state [226,197,181,101,101,106,77,175,222,109,224,228,95,177,222,195,21,159,182,213,81,131,239,8,141,115,209,130,107,39,67,196]
    | 45824 => JGc_TX2_HashBytes.state [79,228,52,63,17,238,145,181,34,187,241,201,144,85,1,72,189,253,175,235,150,239,202,216,171,117,100,210,208,107,207,133]
    | 47872 => JGc_TX2_HashBytes.state [86,120,3,16,14,90,106,11,180,182,86,253,48,54,60,51,178,176,131,60,37,248,185,4,109,125,236,97,241,128,96,4]
    | 48128 => JGc_TX2_HashBytes.state [220,66,240,11,224,86,73,210,202,251,58,129,19,14,221,86,179,240,73,49,122,95,40,107,25,132,18,187,64,22,193,243]
    | 52352 => JGc_TX2_HashBytes.state [238,251,240,139,222,162,82,13,5,62,14,101,72,222,153,31,136,216,181,124,9,170,18,210,98,111,201,200,121,154,149,146]
    | 54016 => JGc_TX2_HashBytes.state [84,69,130,187,250,41,60,93,211,73,58,43,46,132,20,190,44,37,46,171,236,6,109,126,126,222,174,144,62,90,134,121]
    | 61568 => JGc_TX2_HashBytes.state [220,229,124,220,129,225,225,51,200,62,80,161,62,80,246,77,79,81,125,59,117,195,120,42,167,10,86,19,49,243,144,77]
    | _ => JGc_TX2_HashBytes.state []
  | 8 => match base with
    | 16640 => JGc_TX2_HashBytes.state [129,139,196,209,161,57,255,18,26,252,18,30,104,179,146,146,53,230,56,126,7,69,243,43,190,141,29,119,242,28,130,38]
    | 23040 => JGc_TX2_HashBytes.state [117,171,13,240,245,18,102,9,11,246,84,158,171,240,2,164,240,189,242,95,184,129,172,128,21,241,222,68,41,84,235,244]
    | 37120 => JGc_TX2_HashBytes.state [112,189,186,141,150,13,115,120,9,52,169,201,97,163,116,115,235,94,1,206,49,158,11,31,22,195,133,0,144,140,158,171]
    | 40192 => JGc_TX2_HashBytes.state [65,26,79,118,1,189,37,99,244,25,130,70,240,70,77,82,137,79,54,72,155,62,165,187,17,76,147,69,84,119,4,194]
    | 45568 => JGc_TX2_HashBytes.state [5,50,44,127,47,107,97,24,250,118,48,94,115,31,165,104,79,252,110,153,14,168,101,168,252,13,13,176,5,235,11,81]
    | 47616 => JGc_TX2_HashBytes.state [146,141,221,94,160,176,42,173,76,178,63,145,211,201,232,196,75,136,193,192,49,187,63,18,243,80,211,155,61,26,74,208]
    | 48384 => JGc_TX2_HashBytes.state [58,139,189,211,146,54,137,210,150,131,78,126,15,71,120,13,201,90,22,49,210,172,123,254,222,83,204,237,128,27,176,200]
    | 52480 => JGc_TX2_HashBytes.state [154,56,13,62,76,194,157,36,143,253,24,180,172,172,162,80,108,195,243,117,154,221,90,53,117,255,176,94,77,196,103,105]
    | 53760 => JGc_TX2_HashBytes.state [83,238,52,1,11,212,139,234,45,234,168,167,214,33,22,250,35,179,143,118,209,205,200,109,206,127,81,82,170,12,47,46]
    | 61696 => JGc_TX2_HashBytes.state [241,181,167,150,78,64,96,175,242,182,206,109,16,199,77,118,205,21,203,47,68,204,83,194,143,140,213,34,148,113,119,188]
    | _ => JGc_TX2_HashBytes.state []
  | 9 => match base with
    | 16896 => JGc_TX2_HashBytes.state [88,84,1,232,136,97,59,25,95,79,171,202,50,73,181,91,156,235,147,175,149,228,206,198,32,112,132,5,97,147,214,87]
    | 22528 => JGc_TX2_HashBytes.state [49,215,205,0,167,207,189,105,41,234,95,241,207,36,58,176,15,198,248,69,205,13,124,207,197,169,58,105,168,219,95,167]
    | 37376 => JGc_TX2_HashBytes.state [70,134,10,212,128,202,30,53,59,190,3,183,111,214,12,121,235,23,249,250,247,194,155,71,110,138,126,72,15,189,138,73]
    | 40448 => JGc_TX2_HashBytes.state [10,39,97,221,95,35,17,150,57,128,55,20,176,218,99,160,138,81,221,206,84,83,87,98,113,139,232,155,109,200,172,130]
    | 45056 => JGc_TX2_HashBytes.state [229,179,51,182,45,79,191,222,28,125,224,229,212,199,58,124,45,169,119,100,137,91,235,224,126,108,71,10,55,150,202,46]
    | 47104 => JGc_TX2_HashBytes.state [225,153,52,213,21,109,19,130,233,62,120,171,84,78,8,150,137,100,130,111,192,224,128,194,151,56,130,138,66,53,217,85]
    | 48640 => JGc_TX2_HashBytes.state [63,157,246,68,247,156,167,236,33,147,196,148,11,221,187,24,80,152,186,62,219,33,199,166,205,164,91,93,159,195,123,173]
    | 52736 => JGc_TX2_HashBytes.state [248,231,68,50,25,138,85,185,211,224,168,58,116,149,74,89,192,55,189,210,248,227,32,87,12,111,89,138,56,159,211,246]
    | 53248 => JGc_TX2_HashBytes.state [121,77,72,55,197,240,239,13,38,245,104,128,31,8,169,49,228,30,30,39,15,43,17,9,136,253,250,13,253,55,182,203]
    | 61952 => JGc_TX2_HashBytes.state [3,74,103,5,105,99,91,75,105,84,175,69,235,21,94,73,167,83,99,16,155,139,147,0,108,111,209,105,20,221,143,245]
    | _ => JGc_TX2_HashBytes.state []
  | 10 => match base with
    | 17408 => JGc_TX2_HashBytes.state [59,119,73,169,22,234,180,231,182,173,95,170,28,240,254,211,36,169,197,26,155,126,34,120,70,14,2,233,116,165,77,238]
    | 23552 => JGc_TX2_HashBytes.state [155,115,130,156,18,114,181,14,247,172,123,90,64,80,209,183,141,7,129,131,179,236,78,203,48,11,88,165,65,162,198,183]
    | 37888 => JGc_TX2_HashBytes.state [233,55,27,237,249,242,100,244,152,233,196,144,235,235,188,45,24,60,248,32,79,165,176,201,186,138,207,29,188,87,191,26]
    | 38912 => JGc_TX2_HashBytes.state [21,19,134,173,7,2,210,241,42,75,194,167,15,45,14,161,26,153,154,65,84,193,25,180,34,59,39,191,21,32,25,135]
    | 46080 => JGc_TX2_HashBytes.state [186,104,47,209,122,14,221,153,173,57,67,129,86,66,66,233,32,56,115,230,42,38,98,22,111,235,154,246,230,200,89,9]
    | 51200 => JGc_TX2_HashBytes.state [160,11,21,231,220,161,4,194,145,32,85,167,167,102,254,212,177,251,97,177,99,36,215,15,114,51,84,17,30,107,226,151]
    | 54272 => JGc_TX2_HashBytes.state [79,82,178,84,61,147,76,0,223,43,6,169,212,57,122,92,55,118,68,198,170,121,50,188,215,151,199,101,127,208,161,110]
    | 62464 => JGc_TX2_HashBytes.state [113,199,16,24,52,72,40,241,79,147,76,57,246,194,155,42,154,10,38,24,158,221,37,151,184,52,224,109,73,38,75,31]
    | _ => JGc_TX2_HashBytes.state []
  | 11 => match base with
    | 18432 => JGc_TX2_HashBytes.state [170,153,117,5,67,73,116,195,9,13,223,78,171,169,18,95,110,140,91,37,34,17,55,253,160,219,151,107,246,215,123,234]
    | 20480 => JGc_TX2_HashBytes.state [216,219,166,205,15,70,186,97,80,104,229,181,34,249,182,130,33,182,45,106,240,203,133,32,164,178,203,167,172,135,153,82]
    | 49152 => JGc_TX2_HashBytes.state [60,65,38,140,93,216,131,203,27,50,149,248,16,182,251,250,174,83,223,189,145,180,153,159,227,187,210,101,127,209,224,34]
    | 55296 => JGc_TX2_HashBytes.state [6,129,243,133,201,8,108,81,39,87,79,34,75,133,83,63,178,115,227,174,129,80,5,186,58,198,235,77,231,201,140,216]
    | 63488 => JGc_TX2_HashBytes.state [197,225,37,96,40,16,98,217,159,88,149,106,254,188,227,153,131,207,22,77,128,46,74,234,41,2,48,235,27,112,230,153]
    | _ => JGc_TX2_HashBytes.state []
  | 12 => match base with
    | 32768 => JGc_TX2_HashBytes.state [224,16,194,66,110,101,52,10,179,79,182,34,88,250,183,144,150,209,247,104,194,136,212,200,251,140,161,235,156,251,89,119]
    | 40960 => JGc_TX2_HashBytes.state [110,140,14,207,117,61,1,50,35,2,166,51,143,145,85,104,230,62,135,43,183,242,18,192,131,122,184,244,45,205,135,7]
    | 57344 => JGc_TX2_HashBytes.state [141,64,232,71,157,231,216,45,93,159,181,117,153,193,198,18,181,64,29,202,192,123,128,152,11,184,100,22,94,163,139,202]
    | _ => JGc_TX2_HashBytes.state []
  | 13 => match base with
    | 24576 => JGc_TX2_HashBytes.state [34,112,182,144,67,6,64,238,194,132,59,239,67,247,9,55,180,77,17,67,178,157,110,43,220,71,83,104,67,4,240,73]
    | _ => JGc_TX2_HashBytes.state []
  | 14 => match base with
    | 0 => JGc_TX2_HashBytes.state [28,133,8,205,254,15,139,95,248,58,225,38,64,117,236,147,74,140,165,149,219,239,213,12,183,184,40,0,97,10,83,26]
    | _ => JGc_TX2_HashBytes.state []
  | 15 => match base with
    | _ => JGc_TX2_HashBytes.state []
  | 16 => match base with
    | 65536 => JGc_TX2_HashBytes.state [128,179,167,189,122,81,88,173,23,97,55,49,163,83,67,138,131,227,2,149,136,117,239,125,58,69,31,115,134,136,165,136]
    | _ => JGc_TX2_HashBytes.state []
  | 17 => match base with
    | 131072 => JGc_TX2_HashBytes.state [220,196,233,115,158,7,124,8,46,188,36,235,198,156,139,68,223,130,204,114,37,155,16,71,174,150,102,35,254,100,134,80]
    | _ => JGc_TX2_HashBytes.state []
  | _ => JGc_TX2_HashBytes.state []
def SiblingLaw (f : Nat → Nat → State) : Prop := ∀ h,h<18 → ∀ b,b∈bases h → f h b=siblingAt h b
theorem unoccupied (f : Nat → Bytes) (g : Nat → Nat → State) (h b : Nat)
    (no : ¬OracleDecisionMultiBuild.Occupied indices h b) :
    OracleDecisionMultiBuild.build indices f g h b=.supplied (g h b) := by
  cases h <;> simp only [OracleDecisionMultiBuild.build,if_neg no]
#print axioms unoccupied
end AspisR1.JHh_C_Gr_M2Roots
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_C_Gr_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input000 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash000.message
def value000 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash000.result
theorem hash000 : JFp_SHADigest.digest input000=value000 := by
  have law := JHe_SHARealization.tree2 ⟨0, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash000
def tree000 : Tree := .opened input000
theorem root000 : root JFp_SHADigest.digest tree000=value000 := hash000
#print axioms root000
def input001 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash001.message
def value001 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash001.result
theorem hash001 : JFp_SHADigest.digest input001=value001 := by
  have law := JHe_SHARealization.tree2 ⟨1, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash001
def tree001 : Tree := .opened input001
theorem root001 : root JFp_SHADigest.digest tree001=value001 := hash001
#print axioms root001
def input002 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash002.message
def value002 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash002.result
theorem hash002 : JFp_SHADigest.digest input002=value002 := by
  have law := JHe_SHARealization.tree2 ⟨2, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash002
def tree002 : Tree := .opened input002
theorem root002 : root JFp_SHADigest.digest tree002=value002 := hash002
#print axioms root002
def input003 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash003.message
def value003 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash003.result
theorem hash003 : JFp_SHADigest.digest input003=value003 := by
  have law := JHe_SHARealization.tree2 ⟨3, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash003
def tree003 : Tree := .opened input003
theorem root003 : root JFp_SHADigest.digest tree003=value003 := hash003
#print axioms root003
def input004 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash004.message
def value004 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash004.result
theorem hash004 : JFp_SHADigest.digest input004=value004 := by
  have law := JHe_SHARealization.tree2 ⟨4, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash004
def tree004 : Tree := .opened input004
theorem root004 : root JFp_SHADigest.digest tree004=value004 := hash004
#print axioms root004
def input005 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash005.message
def value005 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash005.result
theorem hash005 : JFp_SHADigest.digest input005=value005 := by
  have law := JHe_SHARealization.tree2 ⟨5, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash005
def tree005 : Tree := .opened input005
theorem root005 : root JFp_SHADigest.digest tree005=value005 := hash005
#print axioms root005
def input006 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash006.message
def value006 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash006.result
theorem hash006 : JFp_SHADigest.digest input006=value006 := by
  have law := JHe_SHARealization.tree2 ⟨6, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash006
def tree006 : Tree := .opened input006
theorem root006 : root JFp_SHADigest.digest tree006=value006 := hash006
#print axioms root006
def input007 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash007.message
def value007 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash007.result
theorem hash007 : JFp_SHADigest.digest input007=value007 := by
  have law := JHe_SHARealization.tree2 ⟨7, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash007
def tree007 : Tree := .opened input007
theorem root007 : root JFp_SHADigest.digest tree007=value007 := hash007
#print axioms root007
def input008 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash008.message
def value008 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash008.result
theorem hash008 : JFp_SHADigest.digest input008=value008 := by
  have law := JHe_SHARealization.tree2 ⟨8, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash008
def tree008 : Tree := .opened input008
theorem root008 : root JFp_SHADigest.digest tree008=value008 := hash008
#print axioms root008
def input009 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash009.message
def value009 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash009.result
theorem hash009 : JFp_SHADigest.digest input009=value009 := by
  have law := JHe_SHARealization.tree2 ⟨9, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash009
def tree009 : Tree := .opened input009
theorem root009 : root JFp_SHADigest.digest tree009=value009 := hash009
#print axioms root009
def inputAt (base : Nat) : Bytes := match base with
  | 23374 => input000
  | 36882 => input001
  | 54205 => input002
  | 61474 => input003
  | 52342 => input004
  | 48079 => input005
  | 16398 => input006
  | 45964 => input007
  | 48273 => input008
  | 39953 => input009
  | _ => []
def InputLaw (f : Nat → Bytes) : Prop := ∀ b,b∈indices → f b=inputAt b
theorem shape000 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (_siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 0 23374=tree000 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 0 23374),inputs 23374 (by decide)]
  rfl
#print axioms shape000
theorem shape001 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (_siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 0 36882=tree001 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 0 36882),inputs 36882 (by decide)]
  rfl
#print axioms shape001
theorem shape002 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (_siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 0 54205=tree002 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 0 54205),inputs 54205 (by decide)]
  rfl
#print axioms shape002
theorem shape003 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (_siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 0 61474=tree003 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 0 61474),inputs 61474 (by decide)]
  rfl
#print axioms shape003
theorem shape004 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (_siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 0 52342=tree004 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 0 52342),inputs 52342 (by decide)]
  rfl
#print axioms shape004
theorem shape005 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (_siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 0 48079=tree005 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 0 48079),inputs 48079 (by decide)]
  rfl
#print axioms shape005
theorem shape006 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (_siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 0 16398=tree006 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 0 16398),inputs 16398 (by decide)]
  rfl
#print axioms shape006
theorem shape007 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (_siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 0 45964=tree007 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 0 45964),inputs 45964 (by decide)]
  rfl
#print axioms shape007
theorem shape008 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (_siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 0 48273=tree008 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 0 48273),inputs 48273 (by decide)]
  rfl
#print axioms shape008
theorem shape009 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (_siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 0 39953=tree009 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 0 39953),inputs 39953 (by decide)]
  rfl
#print axioms shape009
end AspisR1.JHh_C_Gr_M2Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_C_Gr_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input010 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash010.message
def value010 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash010.result
theorem hash010 : JFp_SHADigest.digest input010=value010 := by
  have law := JHe_SHARealization.tree2 ⟨10, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash010
theorem address010 : BinMerkle32Path.nodeInput (children value006 (JGc_TX2_HashBytes.state [59,19,2,0,169,92,95,200,80,218,215,254,63,229,202,59,255,62,34,152,178,252,191,0,154,18,160,100,127,195,236,140]))=input010 := by rfl
#print axioms address010
def tree010 : Tree := .branch tree006 (.supplied (JGc_TX2_HashBytes.state [59,19,2,0,169,92,95,200,80,218,215,254,63,229,202,59,255,62,34,152,178,252,191,0,154,18,160,100,127,195,236,140]))
theorem root010 : root JFp_SHADigest.digest tree010=value010 := by
  rw [tree010,root,root006]
  exact (congrArg JFp_SHADigest.digest address010).trans hash010
#print axioms root010
theorem shape010 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 16398=tree010 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 16398)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape006 f g inputs siblings]
  rw [unoccupied f g 0 16399 (by decide),siblings 0 (by decide) 16399 (by decide)]
  rfl
#print axioms shape010
def input011 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash011.message
def value011 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash011.result
theorem hash011 : JFp_SHADigest.digest input011=value011 := by
  have law := JHe_SHARealization.tree2 ⟨11, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash011
theorem address011 : BinMerkle32Path.nodeInput (children value000 (JGc_TX2_HashBytes.state [157,250,64,85,13,19,77,148,29,212,154,20,167,121,250,170,228,41,109,0,8,18,69,253,189,146,93,22,157,14,22,87]))=input011 := by rfl
#print axioms address011
def tree011 : Tree := .branch tree000 (.supplied (JGc_TX2_HashBytes.state [157,250,64,85,13,19,77,148,29,212,154,20,167,121,250,170,228,41,109,0,8,18,69,253,189,146,93,22,157,14,22,87]))
theorem root011 : root JFp_SHADigest.digest tree011=value011 := by
  rw [tree011,root,root000]
  exact (congrArg JFp_SHADigest.digest address011).trans hash011
#print axioms root011
theorem shape011 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 23374=tree011 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 23374)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape000 f g inputs siblings]
  rw [unoccupied f g 0 23375 (by decide),siblings 0 (by decide) 23375 (by decide)]
  rfl
#print axioms shape011
def input012 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash012.message
def value012 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash012.result
theorem hash012 : JFp_SHADigest.digest input012=value012 := by
  have law := JHe_SHARealization.tree2 ⟨12, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash012
theorem address012 : BinMerkle32Path.nodeInput (children value001 (JGc_TX2_HashBytes.state [200,118,125,216,76,197,168,252,66,166,175,172,159,132,202,150,238,183,109,182,215,230,204,48,38,187,56,127,4,148,156,91]))=input012 := by rfl
#print axioms address012
def tree012 : Tree := .branch tree001 (.supplied (JGc_TX2_HashBytes.state [200,118,125,216,76,197,168,252,66,166,175,172,159,132,202,150,238,183,109,182,215,230,204,48,38,187,56,127,4,148,156,91]))
theorem root012 : root JFp_SHADigest.digest tree012=value012 := by
  rw [tree012,root,root001]
  exact (congrArg JFp_SHADigest.digest address012).trans hash012
#print axioms root012
theorem shape012 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 36882=tree012 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 36882)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape001 f g inputs siblings]
  rw [unoccupied f g 0 36883 (by decide),siblings 0 (by decide) 36883 (by decide)]
  rfl
#print axioms shape012
def input013 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash013.message
def value013 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash013.result
theorem hash013 : JFp_SHADigest.digest input013=value013 := by
  have law := JHe_SHARealization.tree2 ⟨13, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash013
theorem address013 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [212,242,126,73,163,36,230,105,69,72,183,184,38,238,26,19,12,17,111,26,165,123,45,242,32,167,200,96,233,228,57,69]) value009)=input013 := by rfl
#print axioms address013
def tree013 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [212,242,126,73,163,36,230,105,69,72,183,184,38,238,26,19,12,17,111,26,165,123,45,242,32,167,200,96,233,228,57,69])) tree009
theorem root013 : root JFp_SHADigest.digest tree013=value013 := by
  rw [tree013,root,root009]
  exact (congrArg JFp_SHADigest.digest address013).trans hash013
#print axioms root013
theorem shape013 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 39952=tree013 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 39952)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 0 39952 (by decide),siblings 0 (by decide) 39952 (by decide)]
  rw [shape009 f g inputs siblings]
  rfl
#print axioms shape013
def input014 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash014.message
def value014 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash014.result
theorem hash014 : JFp_SHADigest.digest input014=value014 := by
  have law := JHe_SHARealization.tree2 ⟨14, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash014
theorem address014 : BinMerkle32Path.nodeInput (children value007 (JGc_TX2_HashBytes.state [82,191,91,24,205,192,231,67,121,98,110,223,12,88,203,10,225,19,214,220,215,156,248,27,81,185,96,114,168,9,78,14]))=input014 := by rfl
#print axioms address014
def tree014 : Tree := .branch tree007 (.supplied (JGc_TX2_HashBytes.state [82,191,91,24,205,192,231,67,121,98,110,223,12,88,203,10,225,19,214,220,215,156,248,27,81,185,96,114,168,9,78,14]))
theorem root014 : root JFp_SHADigest.digest tree014=value014 := by
  rw [tree014,root,root007]
  exact (congrArg JFp_SHADigest.digest address014).trans hash014
#print axioms root014
theorem shape014 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 45964=tree014 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 45964)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape007 f g inputs siblings]
  rw [unoccupied f g 0 45965 (by decide),siblings 0 (by decide) 45965 (by decide)]
  rfl
#print axioms shape014
def input015 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash015.message
def value015 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash015.result
theorem hash015 : JFp_SHADigest.digest input015=value015 := by
  have law := JHe_SHARealization.tree2 ⟨15, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash015
theorem address015 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [133,193,193,242,18,135,93,234,189,30,36,64,27,220,184,7,144,101,221,10,71,70,1,222,233,39,21,21,157,144,185,165]) value005)=input015 := by rfl
#print axioms address015
def tree015 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [133,193,193,242,18,135,93,234,189,30,36,64,27,220,184,7,144,101,221,10,71,70,1,222,233,39,21,21,157,144,185,165])) tree005
theorem root015 : root JFp_SHADigest.digest tree015=value015 := by
  rw [tree015,root,root005]
  exact (congrArg JFp_SHADigest.digest address015).trans hash015
#print axioms root015
theorem shape015 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 48078=tree015 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 48078)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 0 48078 (by decide),siblings 0 (by decide) 48078 (by decide)]
  rw [shape005 f g inputs siblings]
  rfl
#print axioms shape015
def input016 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash016.message
def value016 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash016.result
theorem hash016 : JFp_SHADigest.digest input016=value016 := by
  have law := JHe_SHARealization.tree2 ⟨16, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash016
theorem address016 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [98,207,122,12,13,116,247,26,12,101,199,43,169,75,183,42,84,151,241,175,190,14,219,79,255,20,41,230,147,83,213,218]) value008)=input016 := by rfl
#print axioms address016
def tree016 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [98,207,122,12,13,116,247,26,12,101,199,43,169,75,183,42,84,151,241,175,190,14,219,79,255,20,41,230,147,83,213,218])) tree008
theorem root016 : root JFp_SHADigest.digest tree016=value016 := by
  rw [tree016,root,root008]
  exact (congrArg JFp_SHADigest.digest address016).trans hash016
#print axioms root016
theorem shape016 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 48272=tree016 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 48272)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 0 48272 (by decide),siblings 0 (by decide) 48272 (by decide)]
  rw [shape008 f g inputs siblings]
  rfl
#print axioms shape016
def input017 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash017.message
def value017 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash017.result
theorem hash017 : JFp_SHADigest.digest input017=value017 := by
  have law := JHe_SHARealization.tree2 ⟨17, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash017
theorem address017 : BinMerkle32Path.nodeInput (children value004 (JGc_TX2_HashBytes.state [80,151,219,68,228,150,38,180,212,171,144,75,12,109,31,147,55,20,109,143,198,101,8,244,28,178,249,159,227,18,96,225]))=input017 := by rfl
#print axioms address017
def tree017 : Tree := .branch tree004 (.supplied (JGc_TX2_HashBytes.state [80,151,219,68,228,150,38,180,212,171,144,75,12,109,31,147,55,20,109,143,198,101,8,244,28,178,249,159,227,18,96,225]))
theorem root017 : root JFp_SHADigest.digest tree017=value017 := by
  rw [tree017,root,root004]
  exact (congrArg JFp_SHADigest.digest address017).trans hash017
#print axioms root017
theorem shape017 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 52342=tree017 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 52342)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape004 f g inputs siblings]
  rw [unoccupied f g 0 52343 (by decide),siblings 0 (by decide) 52343 (by decide)]
  rfl
#print axioms shape017
def input018 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash018.message
def value018 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash018.result
theorem hash018 : JFp_SHADigest.digest input018=value018 := by
  have law := JHe_SHARealization.tree2 ⟨18, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash018
theorem address018 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [52,8,95,13,105,245,56,139,100,239,201,233,12,0,102,84,64,208,206,160,240,46,2,104,110,111,39,205,28,111,190,253]) value002)=input018 := by rfl
#print axioms address018
def tree018 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [52,8,95,13,105,245,56,139,100,239,201,233,12,0,102,84,64,208,206,160,240,46,2,104,110,111,39,205,28,111,190,253])) tree002
theorem root018 : root JFp_SHADigest.digest tree018=value018 := by
  rw [tree018,root,root002]
  exact (congrArg JFp_SHADigest.digest address018).trans hash018
#print axioms root018
theorem shape018 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 54204=tree018 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 54204)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 0 54204 (by decide),siblings 0 (by decide) 54204 (by decide)]
  rw [shape002 f g inputs siblings]
  rfl
#print axioms shape018
def input019 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash019.message
def value019 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash019.result
theorem hash019 : JFp_SHADigest.digest input019=value019 := by
  have law := JHe_SHARealization.tree2 ⟨19, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash019
theorem address019 : BinMerkle32Path.nodeInput (children value003 (JGc_TX2_HashBytes.state [58,245,80,88,37,211,128,187,23,227,240,163,220,232,101,152,153,152,109,88,252,196,25,246,154,119,211,100,33,86,172,156]))=input019 := by rfl
#print axioms address019
def tree019 : Tree := .branch tree003 (.supplied (JGc_TX2_HashBytes.state [58,245,80,88,37,211,128,187,23,227,240,163,220,232,101,152,153,152,109,88,252,196,25,246,154,119,211,100,33,86,172,156]))
theorem root019 : root JFp_SHADigest.digest tree019=value019 := by
  rw [tree019,root,root003]
  exact (congrArg JFp_SHADigest.digest address019).trans hash019
#print axioms root019
theorem shape019 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 61474=tree019 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 61474)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape003 f g inputs siblings]
  rw [unoccupied f g 0 61475 (by decide),siblings 0 (by decide) 61475 (by decide)]
  rfl
#print axioms shape019
end AspisR1.JHh_C_Gr_M2Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_C_Gr_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input020 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash020.message
def value020 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash020.result
theorem hash020 : JFp_SHADigest.digest input020=value020 := by
  have law := JHe_SHARealization.tree2 ⟨20, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash020
theorem address020 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [179,57,66,105,91,88,148,117,98,202,23,143,65,232,228,202,11,120,180,169,158,103,229,95,32,200,194,222,112,210,131,3]) value010)=input020 := by rfl
#print axioms address020
def tree020 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [179,57,66,105,91,88,148,117,98,202,23,143,65,232,228,202,11,120,180,169,158,103,229,95,32,200,194,222,112,210,131,3])) tree010
theorem root020 : root JFp_SHADigest.digest tree020=value020 := by
  rw [tree020,root,root010]
  exact (congrArg JFp_SHADigest.digest address020).trans hash020
#print axioms root020
theorem shape020 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 16396=tree020 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 16396)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 1 16396 (by decide),siblings 1 (by decide) 16396 (by decide)]
  rw [shape010 f g inputs siblings]
  rfl
#print axioms shape020
def input021 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash021.message
def value021 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash021.result
theorem hash021 : JFp_SHADigest.digest input021=value021 := by
  have law := JHe_SHARealization.tree2 ⟨21, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash021
theorem address021 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [107,125,164,219,26,17,227,219,9,238,70,117,237,24,14,190,244,82,156,147,101,254,180,116,45,28,98,62,32,57,198,231]) value011)=input021 := by rfl
#print axioms address021
def tree021 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [107,125,164,219,26,17,227,219,9,238,70,117,237,24,14,190,244,82,156,147,101,254,180,116,45,28,98,62,32,57,198,231])) tree011
theorem root021 : root JFp_SHADigest.digest tree021=value021 := by
  rw [tree021,root,root011]
  exact (congrArg JFp_SHADigest.digest address021).trans hash021
#print axioms root021
theorem shape021 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 23372=tree021 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 23372)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 1 23372 (by decide),siblings 1 (by decide) 23372 (by decide)]
  rw [shape011 f g inputs siblings]
  rfl
#print axioms shape021
def input022 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash022.message
def value022 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash022.result
theorem hash022 : JFp_SHADigest.digest input022=value022 := by
  have law := JHe_SHARealization.tree2 ⟨22, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash022
theorem address022 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [47,141,216,252,197,166,70,210,81,178,177,38,252,245,63,138,90,15,229,137,148,184,253,55,25,241,20,143,57,249,114,136]) value012)=input022 := by rfl
#print axioms address022
def tree022 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [47,141,216,252,197,166,70,210,81,178,177,38,252,245,63,138,90,15,229,137,148,184,253,55,25,241,20,143,57,249,114,136])) tree012
theorem root022 : root JFp_SHADigest.digest tree022=value022 := by
  rw [tree022,root,root012]
  exact (congrArg JFp_SHADigest.digest address022).trans hash022
#print axioms root022
theorem shape022 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 36880=tree022 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 36880)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 1 36880 (by decide),siblings 1 (by decide) 36880 (by decide)]
  rw [shape012 f g inputs siblings]
  rfl
#print axioms shape022
def input023 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash023.message
def value023 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash023.result
theorem hash023 : JFp_SHADigest.digest input023=value023 := by
  have law := JHe_SHARealization.tree2 ⟨23, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash023
theorem address023 : BinMerkle32Path.nodeInput (children value013 (JGc_TX2_HashBytes.state [149,82,100,53,22,189,226,92,234,12,68,130,93,161,194,244,133,5,197,140,65,188,52,164,91,170,182,75,33,104,183,190]))=input023 := by rfl
#print axioms address023
def tree023 : Tree := .branch tree013 (.supplied (JGc_TX2_HashBytes.state [149,82,100,53,22,189,226,92,234,12,68,130,93,161,194,244,133,5,197,140,65,188,52,164,91,170,182,75,33,104,183,190]))
theorem root023 : root JFp_SHADigest.digest tree023=value023 := by
  rw [tree023,root,root013]
  exact (congrArg JFp_SHADigest.digest address023).trans hash023
#print axioms root023
theorem shape023 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 39952=tree023 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 39952)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape013 f g inputs siblings]
  rw [unoccupied f g 1 39954 (by decide),siblings 1 (by decide) 39954 (by decide)]
  rfl
#print axioms shape023
def input024 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash024.message
def value024 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash024.result
theorem hash024 : JFp_SHADigest.digest input024=value024 := by
  have law := JHe_SHARealization.tree2 ⟨24, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash024
theorem address024 : BinMerkle32Path.nodeInput (children value014 (JGc_TX2_HashBytes.state [153,116,202,141,139,28,14,167,146,44,161,154,154,150,133,164,1,97,251,129,67,238,209,205,47,38,121,56,63,172,240,59]))=input024 := by rfl
#print axioms address024
def tree024 : Tree := .branch tree014 (.supplied (JGc_TX2_HashBytes.state [153,116,202,141,139,28,14,167,146,44,161,154,154,150,133,164,1,97,251,129,67,238,209,205,47,38,121,56,63,172,240,59]))
theorem root024 : root JFp_SHADigest.digest tree024=value024 := by
  rw [tree024,root,root014]
  exact (congrArg JFp_SHADigest.digest address024).trans hash024
#print axioms root024
theorem shape024 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 45964=tree024 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 45964)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape014 f g inputs siblings]
  rw [unoccupied f g 1 45966 (by decide),siblings 1 (by decide) 45966 (by decide)]
  rfl
#print axioms shape024
def input025 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash025.message
def value025 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash025.result
theorem hash025 : JFp_SHADigest.digest input025=value025 := by
  have law := JHe_SHARealization.tree2 ⟨25, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash025
theorem address025 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [59,32,195,3,19,154,209,61,43,191,156,113,54,238,181,159,13,241,5,114,216,99,9,206,156,21,132,19,133,169,28,149]) value015)=input025 := by rfl
#print axioms address025
def tree025 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [59,32,195,3,19,154,209,61,43,191,156,113,54,238,181,159,13,241,5,114,216,99,9,206,156,21,132,19,133,169,28,149])) tree015
theorem root025 : root JFp_SHADigest.digest tree025=value025 := by
  rw [tree025,root,root015]
  exact (congrArg JFp_SHADigest.digest address025).trans hash025
#print axioms root025
theorem shape025 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 48076=tree025 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 48076)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 1 48076 (by decide),siblings 1 (by decide) 48076 (by decide)]
  rw [shape015 f g inputs siblings]
  rfl
#print axioms shape025
def input026 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash026.message
def value026 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash026.result
theorem hash026 : JFp_SHADigest.digest input026=value026 := by
  have law := JHe_SHARealization.tree2 ⟨26, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash026
theorem address026 : BinMerkle32Path.nodeInput (children value016 (JGc_TX2_HashBytes.state [160,150,74,176,230,87,55,149,137,239,129,40,128,128,155,164,228,20,84,10,90,170,136,112,178,54,174,236,18,211,106,20]))=input026 := by rfl
#print axioms address026
def tree026 : Tree := .branch tree016 (.supplied (JGc_TX2_HashBytes.state [160,150,74,176,230,87,55,149,137,239,129,40,128,128,155,164,228,20,84,10,90,170,136,112,178,54,174,236,18,211,106,20]))
theorem root026 : root JFp_SHADigest.digest tree026=value026 := by
  rw [tree026,root,root016]
  exact (congrArg JFp_SHADigest.digest address026).trans hash026
#print axioms root026
theorem shape026 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 48272=tree026 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 48272)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape016 f g inputs siblings]
  rw [unoccupied f g 1 48274 (by decide),siblings 1 (by decide) 48274 (by decide)]
  rfl
#print axioms shape026
def input027 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash027.message
def value027 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash027.result
theorem hash027 : JFp_SHADigest.digest input027=value027 := by
  have law := JHe_SHARealization.tree2 ⟨27, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash027
theorem address027 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [228,12,216,182,13,245,17,244,56,172,67,209,165,228,216,245,36,207,219,252,76,56,80,233,32,172,129,152,94,206,186,32]) value017)=input027 := by rfl
#print axioms address027
def tree027 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [228,12,216,182,13,245,17,244,56,172,67,209,165,228,216,245,36,207,219,252,76,56,80,233,32,172,129,152,94,206,186,32])) tree017
theorem root027 : root JFp_SHADigest.digest tree027=value027 := by
  rw [tree027,root,root017]
  exact (congrArg JFp_SHADigest.digest address027).trans hash027
#print axioms root027
theorem shape027 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 52340=tree027 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 52340)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 1 52340 (by decide),siblings 1 (by decide) 52340 (by decide)]
  rw [shape017 f g inputs siblings]
  rfl
#print axioms shape027
def input028 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash028.message
def value028 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash028.result
theorem hash028 : JFp_SHADigest.digest input028=value028 := by
  have law := JHe_SHARealization.tree2 ⟨28, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash028
theorem address028 : BinMerkle32Path.nodeInput (children value018 (JGc_TX2_HashBytes.state [188,221,111,216,18,217,30,136,2,223,90,61,66,1,162,238,11,64,13,125,84,37,35,58,104,178,136,54,100,76,168,41]))=input028 := by rfl
#print axioms address028
def tree028 : Tree := .branch tree018 (.supplied (JGc_TX2_HashBytes.state [188,221,111,216,18,217,30,136,2,223,90,61,66,1,162,238,11,64,13,125,84,37,35,58,104,178,136,54,100,76,168,41]))
theorem root028 : root JFp_SHADigest.digest tree028=value028 := by
  rw [tree028,root,root018]
  exact (congrArg JFp_SHADigest.digest address028).trans hash028
#print axioms root028
theorem shape028 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 54204=tree028 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 54204)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape018 f g inputs siblings]
  rw [unoccupied f g 1 54206 (by decide),siblings 1 (by decide) 54206 (by decide)]
  rfl
#print axioms shape028
def input029 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash029.message
def value029 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash029.result
theorem hash029 : JFp_SHADigest.digest input029=value029 := by
  have law := JHe_SHARealization.tree2 ⟨29, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash029
theorem address029 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [41,72,84,86,132,77,231,158,173,214,235,170,124,62,85,192,227,36,17,210,21,206,189,190,89,89,69,162,196,143,89,105]) value019)=input029 := by rfl
#print axioms address029
def tree029 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [41,72,84,86,132,77,231,158,173,214,235,170,124,62,85,192,227,36,17,210,21,206,189,190,89,89,69,162,196,143,89,105])) tree019
theorem root029 : root JFp_SHADigest.digest tree029=value029 := by
  rw [tree029,root,root019]
  exact (congrArg JFp_SHADigest.digest address029).trans hash029
#print axioms root029
theorem shape029 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 61472=tree029 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 61472)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 1 61472 (by decide),siblings 1 (by decide) 61472 (by decide)]
  rw [shape019 f g inputs siblings]
  rfl
#print axioms shape029
end AspisR1.JHh_C_Gr_M2Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_C_Gr_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input030 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash030.message
def value030 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash030.result
theorem hash030 : JFp_SHADigest.digest input030=value030 := by
  have law := JHe_SHARealization.tree2 ⟨30, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash030
theorem address030 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [194,245,184,247,117,235,145,13,126,50,69,25,98,255,22,215,181,195,177,122,110,168,180,137,116,143,124,181,73,28,5,69]) value020)=input030 := by rfl
#print axioms address030
def tree030 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [194,245,184,247,117,235,145,13,126,50,69,25,98,255,22,215,181,195,177,122,110,168,180,137,116,143,124,181,73,28,5,69])) tree020
theorem root030 : root JFp_SHADigest.digest tree030=value030 := by
  rw [tree030,root,root020]
  exact (congrArg JFp_SHADigest.digest address030).trans hash030
#print axioms root030
theorem shape030 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 16392=tree030 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 16392)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 2 16392 (by decide),siblings 2 (by decide) 16392 (by decide)]
  rw [shape020 f g inputs siblings]
  rfl
#print axioms shape030
def input031 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash031.message
def value031 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash031.result
theorem hash031 : JFp_SHADigest.digest input031=value031 := by
  have law := JHe_SHARealization.tree2 ⟨31, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash031
theorem address031 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [254,249,253,171,105,7,200,164,192,146,148,22,234,243,156,193,204,205,200,27,131,103,94,225,10,168,70,82,231,124,252,35]) value021)=input031 := by rfl
#print axioms address031
def tree031 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [254,249,253,171,105,7,200,164,192,146,148,22,234,243,156,193,204,205,200,27,131,103,94,225,10,168,70,82,231,124,252,35])) tree021
theorem root031 : root JFp_SHADigest.digest tree031=value031 := by
  rw [tree031,root,root021]
  exact (congrArg JFp_SHADigest.digest address031).trans hash031
#print axioms root031
theorem shape031 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 23368=tree031 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 23368)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 2 23368 (by decide),siblings 2 (by decide) 23368 (by decide)]
  rw [shape021 f g inputs siblings]
  rfl
#print axioms shape031
def input032 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash032.message
def value032 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash032.result
theorem hash032 : JFp_SHADigest.digest input032=value032 := by
  have law := JHe_SHARealization.tree2 ⟨32, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash032
theorem address032 : BinMerkle32Path.nodeInput (children value022 (JGc_TX2_HashBytes.state [186,93,169,162,221,9,97,47,195,23,151,178,51,170,82,124,130,6,105,43,70,227,136,131,203,240,135,148,160,124,113,200]))=input032 := by rfl
#print axioms address032
def tree032 : Tree := .branch tree022 (.supplied (JGc_TX2_HashBytes.state [186,93,169,162,221,9,97,47,195,23,151,178,51,170,82,124,130,6,105,43,70,227,136,131,203,240,135,148,160,124,113,200]))
theorem root032 : root JFp_SHADigest.digest tree032=value032 := by
  rw [tree032,root,root022]
  exact (congrArg JFp_SHADigest.digest address032).trans hash032
#print axioms root032
theorem shape032 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 36880=tree032 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 36880)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape022 f g inputs siblings]
  rw [unoccupied f g 2 36884 (by decide),siblings 2 (by decide) 36884 (by decide)]
  rfl
#print axioms shape032
def input033 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash033.message
def value033 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash033.result
theorem hash033 : JFp_SHADigest.digest input033=value033 := by
  have law := JHe_SHARealization.tree2 ⟨33, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash033
theorem address033 : BinMerkle32Path.nodeInput (children value023 (JGc_TX2_HashBytes.state [117,14,241,103,80,121,161,108,21,104,179,229,107,125,84,31,189,134,142,185,135,253,55,234,139,89,193,114,221,115,46,128]))=input033 := by rfl
#print axioms address033
def tree033 : Tree := .branch tree023 (.supplied (JGc_TX2_HashBytes.state [117,14,241,103,80,121,161,108,21,104,179,229,107,125,84,31,189,134,142,185,135,253,55,234,139,89,193,114,221,115,46,128]))
theorem root033 : root JFp_SHADigest.digest tree033=value033 := by
  rw [tree033,root,root023]
  exact (congrArg JFp_SHADigest.digest address033).trans hash033
#print axioms root033
theorem shape033 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 39952=tree033 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 39952)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape023 f g inputs siblings]
  rw [unoccupied f g 2 39956 (by decide),siblings 2 (by decide) 39956 (by decide)]
  rfl
#print axioms shape033
def input034 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash034.message
def value034 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash034.result
theorem hash034 : JFp_SHADigest.digest input034=value034 := by
  have law := JHe_SHARealization.tree2 ⟨34, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash034
theorem address034 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [252,199,160,112,92,68,47,54,9,188,58,105,45,11,24,100,63,52,109,70,105,61,240,30,194,73,210,110,30,137,146,5]) value024)=input034 := by rfl
#print axioms address034
def tree034 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [252,199,160,112,92,68,47,54,9,188,58,105,45,11,24,100,63,52,109,70,105,61,240,30,194,73,210,110,30,137,146,5])) tree024
theorem root034 : root JFp_SHADigest.digest tree034=value034 := by
  rw [tree034,root,root024]
  exact (congrArg JFp_SHADigest.digest address034).trans hash034
#print axioms root034
theorem shape034 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 45960=tree034 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 45960)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 2 45960 (by decide),siblings 2 (by decide) 45960 (by decide)]
  rw [shape024 f g inputs siblings]
  rfl
#print axioms shape034
def input035 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash035.message
def value035 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash035.result
theorem hash035 : JFp_SHADigest.digest input035=value035 := by
  have law := JHe_SHARealization.tree2 ⟨35, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash035
theorem address035 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [235,50,176,191,189,100,44,247,120,2,40,116,130,231,48,6,150,118,123,187,248,252,9,165,185,26,191,183,209,65,102,221]) value025)=input035 := by rfl
#print axioms address035
def tree035 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [235,50,176,191,189,100,44,247,120,2,40,116,130,231,48,6,150,118,123,187,248,252,9,165,185,26,191,183,209,65,102,221])) tree025
theorem root035 : root JFp_SHADigest.digest tree035=value035 := by
  rw [tree035,root,root025]
  exact (congrArg JFp_SHADigest.digest address035).trans hash035
#print axioms root035
theorem shape035 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 48072=tree035 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 48072)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 2 48072 (by decide),siblings 2 (by decide) 48072 (by decide)]
  rw [shape025 f g inputs siblings]
  rfl
#print axioms shape035
def input036 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash036.message
def value036 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash036.result
theorem hash036 : JFp_SHADigest.digest input036=value036 := by
  have law := JHe_SHARealization.tree2 ⟨36, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash036
theorem address036 : BinMerkle32Path.nodeInput (children value026 (JGc_TX2_HashBytes.state [220,245,95,204,173,38,219,209,33,203,132,173,44,78,7,132,64,185,24,223,162,215,156,66,211,174,245,196,96,216,230,66]))=input036 := by rfl
#print axioms address036
def tree036 : Tree := .branch tree026 (.supplied (JGc_TX2_HashBytes.state [220,245,95,204,173,38,219,209,33,203,132,173,44,78,7,132,64,185,24,223,162,215,156,66,211,174,245,196,96,216,230,66]))
theorem root036 : root JFp_SHADigest.digest tree036=value036 := by
  rw [tree036,root,root026]
  exact (congrArg JFp_SHADigest.digest address036).trans hash036
#print axioms root036
theorem shape036 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 48272=tree036 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 48272)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape026 f g inputs siblings]
  rw [unoccupied f g 2 48276 (by decide),siblings 2 (by decide) 48276 (by decide)]
  rfl
#print axioms shape036
def input037 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash037.message
def value037 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash037.result
theorem hash037 : JFp_SHADigest.digest input037=value037 := by
  have law := JHe_SHARealization.tree2 ⟨37, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash037
theorem address037 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [106,76,243,247,175,186,175,214,242,19,159,62,63,228,244,231,157,110,252,193,106,75,125,234,209,149,240,59,55,204,191,128]) value027)=input037 := by rfl
#print axioms address037
def tree037 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [106,76,243,247,175,186,175,214,242,19,159,62,63,228,244,231,157,110,252,193,106,75,125,234,209,149,240,59,55,204,191,128])) tree027
theorem root037 : root JFp_SHADigest.digest tree037=value037 := by
  rw [tree037,root,root027]
  exact (congrArg JFp_SHADigest.digest address037).trans hash037
#print axioms root037
theorem shape037 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 52336=tree037 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 52336)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 2 52336 (by decide),siblings 2 (by decide) 52336 (by decide)]
  rw [shape027 f g inputs siblings]
  rfl
#print axioms shape037
def input038 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash038.message
def value038 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash038.result
theorem hash038 : JFp_SHADigest.digest input038=value038 := by
  have law := JHe_SHARealization.tree2 ⟨38, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash038
theorem address038 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [236,64,23,201,253,208,86,58,10,82,89,203,137,84,53,121,112,94,44,47,16,0,83,247,169,8,40,153,151,170,22,238]) value028)=input038 := by rfl
#print axioms address038
def tree038 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [236,64,23,201,253,208,86,58,10,82,89,203,137,84,53,121,112,94,44,47,16,0,83,247,169,8,40,153,151,170,22,238])) tree028
theorem root038 : root JFp_SHADigest.digest tree038=value038 := by
  rw [tree038,root,root028]
  exact (congrArg JFp_SHADigest.digest address038).trans hash038
#print axioms root038
theorem shape038 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 54200=tree038 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 54200)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 2 54200 (by decide),siblings 2 (by decide) 54200 (by decide)]
  rw [shape028 f g inputs siblings]
  rfl
#print axioms shape038
def input039 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash039.message
def value039 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash039.result
theorem hash039 : JFp_SHADigest.digest input039=value039 := by
  have law := JHe_SHARealization.tree2 ⟨39, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash039
theorem address039 : BinMerkle32Path.nodeInput (children value029 (JGc_TX2_HashBytes.state [202,189,29,169,70,123,183,226,47,76,15,140,170,67,27,238,204,183,171,51,116,132,60,183,181,124,58,4,43,84,219,250]))=input039 := by rfl
#print axioms address039
def tree039 : Tree := .branch tree029 (.supplied (JGc_TX2_HashBytes.state [202,189,29,169,70,123,183,226,47,76,15,140,170,67,27,238,204,183,171,51,116,132,60,183,181,124,58,4,43,84,219,250]))
theorem root039 : root JFp_SHADigest.digest tree039=value039 := by
  rw [tree039,root,root029]
  exact (congrArg JFp_SHADigest.digest address039).trans hash039
#print axioms root039
theorem shape039 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 61472=tree039 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 61472)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape029 f g inputs siblings]
  rw [unoccupied f g 2 61476 (by decide),siblings 2 (by decide) 61476 (by decide)]
  rfl
#print axioms shape039
end AspisR1.JHh_C_Gr_M2Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_C_Gr_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input040 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash040.message
def value040 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash040.result
theorem hash040 : JFp_SHADigest.digest input040=value040 := by
  have law := JHe_SHARealization.tree2 ⟨40, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash040
theorem address040 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [249,97,95,72,195,239,230,133,231,204,195,159,197,242,53,210,181,126,161,238,155,106,151,110,88,108,146,232,8,121,248,62]) value030)=input040 := by rfl
#print axioms address040
def tree040 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [249,97,95,72,195,239,230,133,231,204,195,159,197,242,53,210,181,126,161,238,155,106,151,110,88,108,146,232,8,121,248,62])) tree030
theorem root040 : root JFp_SHADigest.digest tree040=value040 := by
  rw [tree040,root,root030]
  exact (congrArg JFp_SHADigest.digest address040).trans hash040
#print axioms root040
theorem shape040 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 16384=tree040 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 16384)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 3 16384 (by decide),siblings 3 (by decide) 16384 (by decide)]
  rw [shape030 f g inputs siblings]
  rfl
#print axioms shape040
def input041 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash041.message
def value041 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash041.result
theorem hash041 : JFp_SHADigest.digest input041=value041 := by
  have law := JHe_SHARealization.tree2 ⟨41, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash041
theorem address041 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [179,62,84,67,145,245,19,145,0,76,183,216,254,164,78,100,235,197,149,22,181,176,111,192,90,35,170,224,190,165,169,130]) value031)=input041 := by rfl
#print axioms address041
def tree041 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [179,62,84,67,145,245,19,145,0,76,183,216,254,164,78,100,235,197,149,22,181,176,111,192,90,35,170,224,190,165,169,130])) tree031
theorem root041 : root JFp_SHADigest.digest tree041=value041 := by
  rw [tree041,root,root031]
  exact (congrArg JFp_SHADigest.digest address041).trans hash041
#print axioms root041
theorem shape041 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 23360=tree041 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 23360)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 3 23360 (by decide),siblings 3 (by decide) 23360 (by decide)]
  rw [shape031 f g inputs siblings]
  rfl
#print axioms shape041
def input042 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash042.message
def value042 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash042.result
theorem hash042 : JFp_SHADigest.digest input042=value042 := by
  have law := JHe_SHARealization.tree2 ⟨42, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash042
theorem address042 : BinMerkle32Path.nodeInput (children value032 (JGc_TX2_HashBytes.state [169,21,194,86,169,83,68,57,145,59,224,82,4,255,183,95,137,88,198,233,243,230,177,89,132,186,175,162,5,209,79,171]))=input042 := by rfl
#print axioms address042
def tree042 : Tree := .branch tree032 (.supplied (JGc_TX2_HashBytes.state [169,21,194,86,169,83,68,57,145,59,224,82,4,255,183,95,137,88,198,233,243,230,177,89,132,186,175,162,5,209,79,171]))
theorem root042 : root JFp_SHADigest.digest tree042=value042 := by
  rw [tree042,root,root032]
  exact (congrArg JFp_SHADigest.digest address042).trans hash042
#print axioms root042
theorem shape042 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 36880=tree042 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 36880)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape032 f g inputs siblings]
  rw [unoccupied f g 3 36888 (by decide),siblings 3 (by decide) 36888 (by decide)]
  rfl
#print axioms shape042
def input043 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash043.message
def value043 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash043.result
theorem hash043 : JFp_SHADigest.digest input043=value043 := by
  have law := JHe_SHARealization.tree2 ⟨43, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash043
theorem address043 : BinMerkle32Path.nodeInput (children value033 (JGc_TX2_HashBytes.state [249,125,104,173,124,225,131,121,245,201,10,19,165,30,103,92,67,162,190,80,0,142,172,114,183,72,182,186,237,7,60,125]))=input043 := by rfl
#print axioms address043
def tree043 : Tree := .branch tree033 (.supplied (JGc_TX2_HashBytes.state [249,125,104,173,124,225,131,121,245,201,10,19,165,30,103,92,67,162,190,80,0,142,172,114,183,72,182,186,237,7,60,125]))
theorem root043 : root JFp_SHADigest.digest tree043=value043 := by
  rw [tree043,root,root033]
  exact (congrArg JFp_SHADigest.digest address043).trans hash043
#print axioms root043
theorem shape043 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 39952=tree043 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 39952)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape033 f g inputs siblings]
  rw [unoccupied f g 3 39960 (by decide),siblings 3 (by decide) 39960 (by decide)]
  rfl
#print axioms shape043
def input044 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash044.message
def value044 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash044.result
theorem hash044 : JFp_SHADigest.digest input044=value044 := by
  have law := JHe_SHARealization.tree2 ⟨44, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash044
theorem address044 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [195,11,91,13,242,157,237,14,230,48,53,152,68,28,146,173,39,23,72,54,22,225,121,215,107,229,54,60,170,68,238,72]) value034)=input044 := by rfl
#print axioms address044
def tree044 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [195,11,91,13,242,157,237,14,230,48,53,152,68,28,146,173,39,23,72,54,22,225,121,215,107,229,54,60,170,68,238,72])) tree034
theorem root044 : root JFp_SHADigest.digest tree044=value044 := by
  rw [tree044,root,root034]
  exact (congrArg JFp_SHADigest.digest address044).trans hash044
#print axioms root044
theorem shape044 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 45952=tree044 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 45952)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 3 45952 (by decide),siblings 3 (by decide) 45952 (by decide)]
  rw [shape034 f g inputs siblings]
  rfl
#print axioms shape044
def input045 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash045.message
def value045 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash045.result
theorem hash045 : JFp_SHADigest.digest input045=value045 := by
  have law := JHe_SHARealization.tree2 ⟨45, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash045
theorem address045 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [179,112,196,108,44,160,62,125,194,38,29,185,108,215,4,140,11,246,68,159,82,31,45,80,100,31,239,92,243,120,250,219]) value035)=input045 := by rfl
#print axioms address045
def tree045 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [179,112,196,108,44,160,62,125,194,38,29,185,108,215,4,140,11,246,68,159,82,31,45,80,100,31,239,92,243,120,250,219])) tree035
theorem root045 : root JFp_SHADigest.digest tree045=value045 := by
  rw [tree045,root,root035]
  exact (congrArg JFp_SHADigest.digest address045).trans hash045
#print axioms root045
theorem shape045 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 48064=tree045 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 48064)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 3 48064 (by decide),siblings 3 (by decide) 48064 (by decide)]
  rw [shape035 f g inputs siblings]
  rfl
#print axioms shape045
def input046 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash046.message
def value046 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash046.result
theorem hash046 : JFp_SHADigest.digest input046=value046 := by
  have law := JHe_SHARealization.tree2 ⟨46, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash046
theorem address046 : BinMerkle32Path.nodeInput (children value036 (JGc_TX2_HashBytes.state [62,167,250,165,65,31,182,78,176,251,194,75,161,83,115,3,81,118,25,197,64,0,255,47,232,78,185,56,42,93,69,86]))=input046 := by rfl
#print axioms address046
def tree046 : Tree := .branch tree036 (.supplied (JGc_TX2_HashBytes.state [62,167,250,165,65,31,182,78,176,251,194,75,161,83,115,3,81,118,25,197,64,0,255,47,232,78,185,56,42,93,69,86]))
theorem root046 : root JFp_SHADigest.digest tree046=value046 := by
  rw [tree046,root,root036]
  exact (congrArg JFp_SHADigest.digest address046).trans hash046
#print axioms root046
theorem shape046 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 48272=tree046 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 48272)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape036 f g inputs siblings]
  rw [unoccupied f g 3 48280 (by decide),siblings 3 (by decide) 48280 (by decide)]
  rfl
#print axioms shape046
def input047 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash047.message
def value047 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash047.result
theorem hash047 : JFp_SHADigest.digest input047=value047 := by
  have law := JHe_SHARealization.tree2 ⟨47, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash047
theorem address047 : BinMerkle32Path.nodeInput (children value037 (JGc_TX2_HashBytes.state [57,54,77,49,101,42,95,108,7,193,128,156,160,108,172,205,176,94,234,119,178,60,14,61,107,83,83,99,46,128,55,36]))=input047 := by rfl
#print axioms address047
def tree047 : Tree := .branch tree037 (.supplied (JGc_TX2_HashBytes.state [57,54,77,49,101,42,95,108,7,193,128,156,160,108,172,205,176,94,234,119,178,60,14,61,107,83,83,99,46,128,55,36]))
theorem root047 : root JFp_SHADigest.digest tree047=value047 := by
  rw [tree047,root,root037]
  exact (congrArg JFp_SHADigest.digest address047).trans hash047
#print axioms root047
theorem shape047 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 52336=tree047 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 52336)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape037 f g inputs siblings]
  rw [unoccupied f g 3 52344 (by decide),siblings 3 (by decide) 52344 (by decide)]
  rfl
#print axioms shape047
def input048 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash048.message
def value048 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash048.result
theorem hash048 : JFp_SHADigest.digest input048=value048 := by
  have law := JHe_SHARealization.tree2 ⟨48, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash048
theorem address048 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [162,78,44,26,160,83,123,134,218,232,6,213,29,159,101,194,116,107,147,229,122,88,91,82,166,42,5,120,181,179,197,167]) value038)=input048 := by rfl
#print axioms address048
def tree048 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [162,78,44,26,160,83,123,134,218,232,6,213,29,159,101,194,116,107,147,229,122,88,91,82,166,42,5,120,181,179,197,167])) tree038
theorem root048 : root JFp_SHADigest.digest tree048=value048 := by
  rw [tree048,root,root038]
  exact (congrArg JFp_SHADigest.digest address048).trans hash048
#print axioms root048
theorem shape048 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 54192=tree048 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 54192)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 3 54192 (by decide),siblings 3 (by decide) 54192 (by decide)]
  rw [shape038 f g inputs siblings]
  rfl
#print axioms shape048
def input049 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash049.message
def value049 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash049.result
theorem hash049 : JFp_SHADigest.digest input049=value049 := by
  have law := JHe_SHARealization.tree2 ⟨49, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash049
theorem address049 : BinMerkle32Path.nodeInput (children value039 (JGc_TX2_HashBytes.state [16,233,214,196,219,235,118,177,214,211,77,23,126,52,140,234,128,247,206,133,105,180,135,29,2,2,189,128,41,90,9,193]))=input049 := by rfl
#print axioms address049
def tree049 : Tree := .branch tree039 (.supplied (JGc_TX2_HashBytes.state [16,233,214,196,219,235,118,177,214,211,77,23,126,52,140,234,128,247,206,133,105,180,135,29,2,2,189,128,41,90,9,193]))
theorem root049 : root JFp_SHADigest.digest tree049=value049 := by
  rw [tree049,root,root039]
  exact (congrArg JFp_SHADigest.digest address049).trans hash049
#print axioms root049
theorem shape049 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 61472=tree049 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 61472)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape039 f g inputs siblings]
  rw [unoccupied f g 3 61480 (by decide),siblings 3 (by decide) 61480 (by decide)]
  rfl
#print axioms shape049
end AspisR1.JHh_C_Gr_M2Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_C_Gr_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input050 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash050.message
def value050 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash050.result
theorem hash050 : JFp_SHADigest.digest input050=value050 := by
  have law := JHe_SHARealization.tree2 ⟨50, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash050
theorem address050 : BinMerkle32Path.nodeInput (children value040 (JGc_TX2_HashBytes.state [65,234,38,73,66,178,230,20,65,121,30,37,225,239,162,80,19,158,198,194,173,16,25,109,108,151,246,72,8,249,139,52]))=input050 := by rfl
#print axioms address050
def tree050 : Tree := .branch tree040 (.supplied (JGc_TX2_HashBytes.state [65,234,38,73,66,178,230,20,65,121,30,37,225,239,162,80,19,158,198,194,173,16,25,109,108,151,246,72,8,249,139,52]))
theorem root050 : root JFp_SHADigest.digest tree050=value050 := by
  rw [tree050,root,root040]
  exact (congrArg JFp_SHADigest.digest address050).trans hash050
#print axioms root050
theorem shape050 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 16384=tree050 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 16384)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape040 f g inputs siblings]
  rw [unoccupied f g 4 16400 (by decide),siblings 4 (by decide) 16400 (by decide)]
  rfl
#print axioms shape050
def input051 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash051.message
def value051 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash051.result
theorem hash051 : JFp_SHADigest.digest input051=value051 := by
  have law := JHe_SHARealization.tree2 ⟨51, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash051
theorem address051 : BinMerkle32Path.nodeInput (children value041 (JGc_TX2_HashBytes.state [160,196,206,167,250,112,3,28,143,138,174,230,166,61,96,100,21,194,32,169,75,99,235,184,138,126,251,198,150,238,190,52]))=input051 := by rfl
#print axioms address051
def tree051 : Tree := .branch tree041 (.supplied (JGc_TX2_HashBytes.state [160,196,206,167,250,112,3,28,143,138,174,230,166,61,96,100,21,194,32,169,75,99,235,184,138,126,251,198,150,238,190,52]))
theorem root051 : root JFp_SHADigest.digest tree051=value051 := by
  rw [tree051,root,root041]
  exact (congrArg JFp_SHADigest.digest address051).trans hash051
#print axioms root051
theorem shape051 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 23360=tree051 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 23360)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape041 f g inputs siblings]
  rw [unoccupied f g 4 23376 (by decide),siblings 4 (by decide) 23376 (by decide)]
  rfl
#print axioms shape051
def input052 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash052.message
def value052 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash052.result
theorem hash052 : JFp_SHADigest.digest input052=value052 := by
  have law := JHe_SHARealization.tree2 ⟨52, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash052
theorem address052 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [116,149,89,253,254,19,246,16,170,116,173,230,189,196,143,72,229,205,60,207,4,27,195,29,163,34,89,116,252,50,119,14]) value042)=input052 := by rfl
#print axioms address052
def tree052 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [116,149,89,253,254,19,246,16,170,116,173,230,189,196,143,72,229,205,60,207,4,27,195,29,163,34,89,116,252,50,119,14])) tree042
theorem root052 : root JFp_SHADigest.digest tree052=value052 := by
  rw [tree052,root,root042]
  exact (congrArg JFp_SHADigest.digest address052).trans hash052
#print axioms root052
theorem shape052 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 36864=tree052 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 36864)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 4 36864 (by decide),siblings 4 (by decide) 36864 (by decide)]
  rw [shape042 f g inputs siblings]
  rfl
#print axioms shape052
def input053 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash053.message
def value053 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash053.result
theorem hash053 : JFp_SHADigest.digest input053=value053 := by
  have law := JHe_SHARealization.tree2 ⟨53, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash053
theorem address053 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [55,78,39,200,76,202,7,1,140,171,82,253,129,15,177,0,61,7,55,23,33,240,211,141,37,123,101,117,182,39,64,187]) value043)=input053 := by rfl
#print axioms address053
def tree053 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [55,78,39,200,76,202,7,1,140,171,82,253,129,15,177,0,61,7,55,23,33,240,211,141,37,123,101,117,182,39,64,187])) tree043
theorem root053 : root JFp_SHADigest.digest tree053=value053 := by
  rw [tree053,root,root043]
  exact (congrArg JFp_SHADigest.digest address053).trans hash053
#print axioms root053
theorem shape053 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 39936=tree053 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 39936)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 4 39936 (by decide),siblings 4 (by decide) 39936 (by decide)]
  rw [shape043 f g inputs siblings]
  rfl
#print axioms shape053
def input054 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash054.message
def value054 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash054.result
theorem hash054 : JFp_SHADigest.digest input054=value054 := by
  have law := JHe_SHARealization.tree2 ⟨54, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash054
theorem address054 : BinMerkle32Path.nodeInput (children value044 (JGc_TX2_HashBytes.state [214,125,42,28,128,37,83,168,43,239,170,218,176,52,50,65,50,39,88,130,133,76,132,84,182,217,3,23,118,224,99,151]))=input054 := by rfl
#print axioms address054
def tree054 : Tree := .branch tree044 (.supplied (JGc_TX2_HashBytes.state [214,125,42,28,128,37,83,168,43,239,170,218,176,52,50,65,50,39,88,130,133,76,132,84,182,217,3,23,118,224,99,151]))
theorem root054 : root JFp_SHADigest.digest tree054=value054 := by
  rw [tree054,root,root044]
  exact (congrArg JFp_SHADigest.digest address054).trans hash054
#print axioms root054
theorem shape054 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 45952=tree054 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 45952)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape044 f g inputs siblings]
  rw [unoccupied f g 4 45968 (by decide),siblings 4 (by decide) 45968 (by decide)]
  rfl
#print axioms shape054
def input055 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash055.message
def value055 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash055.result
theorem hash055 : JFp_SHADigest.digest input055=value055 := by
  have law := JHe_SHARealization.tree2 ⟨55, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash055
theorem address055 : BinMerkle32Path.nodeInput (children value045 (JGc_TX2_HashBytes.state [59,77,103,151,197,77,27,177,181,138,84,152,90,178,108,53,229,207,203,146,23,110,171,197,65,83,20,196,13,21,172,117]))=input055 := by rfl
#print axioms address055
def tree055 : Tree := .branch tree045 (.supplied (JGc_TX2_HashBytes.state [59,77,103,151,197,77,27,177,181,138,84,152,90,178,108,53,229,207,203,146,23,110,171,197,65,83,20,196,13,21,172,117]))
theorem root055 : root JFp_SHADigest.digest tree055=value055 := by
  rw [tree055,root,root045]
  exact (congrArg JFp_SHADigest.digest address055).trans hash055
#print axioms root055
theorem shape055 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 48064=tree055 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 48064)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape045 f g inputs siblings]
  rw [unoccupied f g 4 48080 (by decide),siblings 4 (by decide) 48080 (by decide)]
  rfl
#print axioms shape055
def input056 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash056.message
def value056 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash056.result
theorem hash056 : JFp_SHADigest.digest input056=value056 := by
  have law := JHe_SHARealization.tree2 ⟨56, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash056
theorem address056 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [121,155,170,137,92,23,153,245,180,227,87,14,77,237,32,32,201,175,78,100,37,206,227,60,30,169,227,45,145,173,245,195]) value046)=input056 := by rfl
#print axioms address056
def tree056 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [121,155,170,137,92,23,153,245,180,227,87,14,77,237,32,32,201,175,78,100,37,206,227,60,30,169,227,45,145,173,245,195])) tree046
theorem root056 : root JFp_SHADigest.digest tree056=value056 := by
  rw [tree056,root,root046]
  exact (congrArg JFp_SHADigest.digest address056).trans hash056
#print axioms root056
theorem shape056 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 48256=tree056 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 48256)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 4 48256 (by decide),siblings 4 (by decide) 48256 (by decide)]
  rw [shape046 f g inputs siblings]
  rfl
#print axioms shape056
def input057 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash057.message
def value057 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash057.result
theorem hash057 : JFp_SHADigest.digest input057=value057 := by
  have law := JHe_SHARealization.tree2 ⟨57, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash057
theorem address057 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [77,20,168,204,126,214,237,104,69,211,193,212,69,14,169,89,19,73,26,130,68,35,49,151,26,120,232,187,43,24,108,230]) value047)=input057 := by rfl
#print axioms address057
def tree057 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [77,20,168,204,126,214,237,104,69,211,193,212,69,14,169,89,19,73,26,130,68,35,49,151,26,120,232,187,43,24,108,230])) tree047
theorem root057 : root JFp_SHADigest.digest tree057=value057 := by
  rw [tree057,root,root047]
  exact (congrArg JFp_SHADigest.digest address057).trans hash057
#print axioms root057
theorem shape057 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 52320=tree057 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 52320)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 4 52320 (by decide),siblings 4 (by decide) 52320 (by decide)]
  rw [shape047 f g inputs siblings]
  rfl
#print axioms shape057
def input058 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash058.message
def value058 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash058.result
theorem hash058 : JFp_SHADigest.digest input058=value058 := by
  have law := JHe_SHARealization.tree2 ⟨58, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash058
theorem address058 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [219,113,206,154,96,101,14,206,79,208,91,12,62,43,111,15,159,175,162,128,58,189,130,180,129,14,209,29,246,135,107,199]) value048)=input058 := by rfl
#print axioms address058
def tree058 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [219,113,206,154,96,101,14,206,79,208,91,12,62,43,111,15,159,175,162,128,58,189,130,180,129,14,209,29,246,135,107,199])) tree048
theorem root058 : root JFp_SHADigest.digest tree058=value058 := by
  rw [tree058,root,root048]
  exact (congrArg JFp_SHADigest.digest address058).trans hash058
#print axioms root058
theorem shape058 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 54176=tree058 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 54176)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 4 54176 (by decide),siblings 4 (by decide) 54176 (by decide)]
  rw [shape048 f g inputs siblings]
  rfl
#print axioms shape058
def input059 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash059.message
def value059 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash059.result
theorem hash059 : JFp_SHADigest.digest input059=value059 := by
  have law := JHe_SHARealization.tree2 ⟨59, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash059
theorem address059 : BinMerkle32Path.nodeInput (children value049 (JGc_TX2_HashBytes.state [179,218,162,212,20,131,120,109,52,129,111,92,132,18,158,30,184,98,130,212,185,233,158,145,127,59,221,46,0,214,80,21]))=input059 := by rfl
#print axioms address059
def tree059 : Tree := .branch tree049 (.supplied (JGc_TX2_HashBytes.state [179,218,162,212,20,131,120,109,52,129,111,92,132,18,158,30,184,98,130,212,185,233,158,145,127,59,221,46,0,214,80,21]))
theorem root059 : root JFp_SHADigest.digest tree059=value059 := by
  rw [tree059,root,root049]
  exact (congrArg JFp_SHADigest.digest address059).trans hash059
#print axioms root059
theorem shape059 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 61472=tree059 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 61472)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape049 f g inputs siblings]
  rw [unoccupied f g 4 61488 (by decide),siblings 4 (by decide) 61488 (by decide)]
  rfl
#print axioms shape059
end AspisR1.JHh_C_Gr_M2Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_C_Gr_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input060 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash060.message
def value060 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash060.result
theorem hash060 : JFp_SHADigest.digest input060=value060 := by
  have law := JHe_SHARealization.tree2 ⟨60, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash060
theorem address060 : BinMerkle32Path.nodeInput (children value050 (JGc_TX2_HashBytes.state [125,62,11,58,152,121,161,20,87,123,59,146,157,58,136,241,164,159,33,232,66,172,208,243,124,111,180,225,182,173,183,11]))=input060 := by rfl
#print axioms address060
def tree060 : Tree := .branch tree050 (.supplied (JGc_TX2_HashBytes.state [125,62,11,58,152,121,161,20,87,123,59,146,157,58,136,241,164,159,33,232,66,172,208,243,124,111,180,225,182,173,183,11]))
theorem root060 : root JFp_SHADigest.digest tree060=value060 := by
  rw [tree060,root,root050]
  exact (congrArg JFp_SHADigest.digest address060).trans hash060
#print axioms root060
theorem shape060 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 16384=tree060 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 16384)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape050 f g inputs siblings]
  rw [unoccupied f g 5 16416 (by decide),siblings 5 (by decide) 16416 (by decide)]
  rfl
#print axioms shape060
def input061 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash061.message
def value061 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash061.result
theorem hash061 : JFp_SHADigest.digest input061=value061 := by
  have law := JHe_SHARealization.tree2 ⟨61, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash061
theorem address061 : BinMerkle32Path.nodeInput (children value051 (JGc_TX2_HashBytes.state [108,85,227,67,255,107,240,217,131,85,181,219,24,10,252,188,214,141,198,133,159,73,116,15,37,35,242,27,251,66,11,3]))=input061 := by rfl
#print axioms address061
def tree061 : Tree := .branch tree051 (.supplied (JGc_TX2_HashBytes.state [108,85,227,67,255,107,240,217,131,85,181,219,24,10,252,188,214,141,198,133,159,73,116,15,37,35,242,27,251,66,11,3]))
theorem root061 : root JFp_SHADigest.digest tree061=value061 := by
  rw [tree061,root,root051]
  exact (congrArg JFp_SHADigest.digest address061).trans hash061
#print axioms root061
theorem shape061 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 23360=tree061 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 23360)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape051 f g inputs siblings]
  rw [unoccupied f g 5 23392 (by decide),siblings 5 (by decide) 23392 (by decide)]
  rfl
#print axioms shape061
def input062 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash062.message
def value062 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash062.result
theorem hash062 : JFp_SHADigest.digest input062=value062 := by
  have law := JHe_SHARealization.tree2 ⟨62, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash062
theorem address062 : BinMerkle32Path.nodeInput (children value052 (JGc_TX2_HashBytes.state [20,69,131,244,4,224,142,147,45,30,160,115,55,150,86,41,62,233,146,3,5,126,120,19,244,204,58,53,181,84,196,197]))=input062 := by rfl
#print axioms address062
def tree062 : Tree := .branch tree052 (.supplied (JGc_TX2_HashBytes.state [20,69,131,244,4,224,142,147,45,30,160,115,55,150,86,41,62,233,146,3,5,126,120,19,244,204,58,53,181,84,196,197]))
theorem root062 : root JFp_SHADigest.digest tree062=value062 := by
  rw [tree062,root,root052]
  exact (congrArg JFp_SHADigest.digest address062).trans hash062
#print axioms root062
theorem shape062 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 36864=tree062 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 36864)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape052 f g inputs siblings]
  rw [unoccupied f g 5 36896 (by decide),siblings 5 (by decide) 36896 (by decide)]
  rfl
#print axioms shape062
def input063 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash063.message
def value063 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash063.result
theorem hash063 : JFp_SHADigest.digest input063=value063 := by
  have law := JHe_SHARealization.tree2 ⟨63, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash063
theorem address063 : BinMerkle32Path.nodeInput (children value053 (JGc_TX2_HashBytes.state [46,207,213,156,44,97,223,5,239,95,131,76,225,10,249,132,169,237,91,238,24,122,79,76,77,172,35,29,240,46,161,81]))=input063 := by rfl
#print axioms address063
def tree063 : Tree := .branch tree053 (.supplied (JGc_TX2_HashBytes.state [46,207,213,156,44,97,223,5,239,95,131,76,225,10,249,132,169,237,91,238,24,122,79,76,77,172,35,29,240,46,161,81]))
theorem root063 : root JFp_SHADigest.digest tree063=value063 := by
  rw [tree063,root,root053]
  exact (congrArg JFp_SHADigest.digest address063).trans hash063
#print axioms root063
theorem shape063 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 39936=tree063 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 39936)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape053 f g inputs siblings]
  rw [unoccupied f g 5 39968 (by decide),siblings 5 (by decide) 39968 (by decide)]
  rfl
#print axioms shape063
def input064 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash064.message
def value064 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash064.result
theorem hash064 : JFp_SHADigest.digest input064=value064 := by
  have law := JHe_SHARealization.tree2 ⟨64, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash064
theorem address064 : BinMerkle32Path.nodeInput (children value054 (JGc_TX2_HashBytes.state [95,12,139,86,115,166,43,216,121,70,107,251,72,70,51,33,19,180,64,129,152,241,136,194,104,235,4,19,207,59,71,38]))=input064 := by rfl
#print axioms address064
def tree064 : Tree := .branch tree054 (.supplied (JGc_TX2_HashBytes.state [95,12,139,86,115,166,43,216,121,70,107,251,72,70,51,33,19,180,64,129,152,241,136,194,104,235,4,19,207,59,71,38]))
theorem root064 : root JFp_SHADigest.digest tree064=value064 := by
  rw [tree064,root,root054]
  exact (congrArg JFp_SHADigest.digest address064).trans hash064
#print axioms root064
theorem shape064 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 45952=tree064 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 45952)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape054 f g inputs siblings]
  rw [unoccupied f g 5 45984 (by decide),siblings 5 (by decide) 45984 (by decide)]
  rfl
#print axioms shape064
def input065 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash065.message
def value065 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash065.result
theorem hash065 : JFp_SHADigest.digest input065=value065 := by
  have law := JHe_SHARealization.tree2 ⟨65, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash065
theorem address065 : BinMerkle32Path.nodeInput (children value055 (JGc_TX2_HashBytes.state [96,144,30,173,153,163,192,34,238,70,42,254,168,235,204,203,30,126,228,206,111,202,34,173,110,50,39,31,76,7,91,117]))=input065 := by rfl
#print axioms address065
def tree065 : Tree := .branch tree055 (.supplied (JGc_TX2_HashBytes.state [96,144,30,173,153,163,192,34,238,70,42,254,168,235,204,203,30,126,228,206,111,202,34,173,110,50,39,31,76,7,91,117]))
theorem root065 : root JFp_SHADigest.digest tree065=value065 := by
  rw [tree065,root,root055]
  exact (congrArg JFp_SHADigest.digest address065).trans hash065
#print axioms root065
theorem shape065 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 48064=tree065 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 48064)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape055 f g inputs siblings]
  rw [unoccupied f g 5 48096 (by decide),siblings 5 (by decide) 48096 (by decide)]
  rfl
#print axioms shape065
def input066 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash066.message
def value066 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash066.result
theorem hash066 : JFp_SHADigest.digest input066=value066 := by
  have law := JHe_SHARealization.tree2 ⟨66, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash066
theorem address066 : BinMerkle32Path.nodeInput (children value056 (JGc_TX2_HashBytes.state [193,40,69,139,235,218,184,141,95,6,104,82,149,17,63,148,181,126,57,142,185,25,231,88,16,185,114,171,2,44,236,81]))=input066 := by rfl
#print axioms address066
def tree066 : Tree := .branch tree056 (.supplied (JGc_TX2_HashBytes.state [193,40,69,139,235,218,184,141,95,6,104,82,149,17,63,148,181,126,57,142,185,25,231,88,16,185,114,171,2,44,236,81]))
theorem root066 : root JFp_SHADigest.digest tree066=value066 := by
  rw [tree066,root,root056]
  exact (congrArg JFp_SHADigest.digest address066).trans hash066
#print axioms root066
theorem shape066 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 48256=tree066 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 48256)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape056 f g inputs siblings]
  rw [unoccupied f g 5 48288 (by decide),siblings 5 (by decide) 48288 (by decide)]
  rfl
#print axioms shape066
def input067 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash067.message
def value067 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash067.result
theorem hash067 : JFp_SHADigest.digest input067=value067 := by
  have law := JHe_SHARealization.tree2 ⟨67, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash067
theorem address067 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [108,244,30,13,4,164,224,60,6,70,5,194,113,19,224,179,103,199,233,246,124,170,2,80,220,146,148,253,253,191,218,219]) value057)=input067 := by rfl
#print axioms address067
def tree067 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [108,244,30,13,4,164,224,60,6,70,5,194,113,19,224,179,103,199,233,246,124,170,2,80,220,146,148,253,253,191,218,219])) tree057
theorem root067 : root JFp_SHADigest.digest tree067=value067 := by
  rw [tree067,root,root057]
  exact (congrArg JFp_SHADigest.digest address067).trans hash067
#print axioms root067
theorem shape067 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 52288=tree067 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 52288)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 5 52288 (by decide),siblings 5 (by decide) 52288 (by decide)]
  rw [shape057 f g inputs siblings]
  rfl
#print axioms shape067
def input068 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash068.message
def value068 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash068.result
theorem hash068 : JFp_SHADigest.digest input068=value068 := by
  have law := JHe_SHARealization.tree2 ⟨68, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash068
theorem address068 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [77,83,165,84,145,44,241,189,189,116,178,122,62,239,124,255,41,4,75,96,207,188,221,80,196,143,108,51,218,23,202,213]) value058)=input068 := by rfl
#print axioms address068
def tree068 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [77,83,165,84,145,44,241,189,189,116,178,122,62,239,124,255,41,4,75,96,207,188,221,80,196,143,108,51,218,23,202,213])) tree058
theorem root068 : root JFp_SHADigest.digest tree068=value068 := by
  rw [tree068,root,root058]
  exact (congrArg JFp_SHADigest.digest address068).trans hash068
#print axioms root068
theorem shape068 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 54144=tree068 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 54144)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 5 54144 (by decide),siblings 5 (by decide) 54144 (by decide)]
  rw [shape058 f g inputs siblings]
  rfl
#print axioms shape068
def input069 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash069.message
def value069 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash069.result
theorem hash069 : JFp_SHADigest.digest input069=value069 := by
  have law := JHe_SHARealization.tree2 ⟨69, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash069
theorem address069 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [111,137,193,249,230,246,19,197,115,7,165,255,66,184,205,55,249,202,250,176,180,214,60,254,61,126,78,118,255,181,149,35]) value059)=input069 := by rfl
#print axioms address069
def tree069 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [111,137,193,249,230,246,19,197,115,7,165,255,66,184,205,55,249,202,250,176,180,214,60,254,61,126,78,118,255,181,149,35])) tree059
theorem root069 : root JFp_SHADigest.digest tree069=value069 := by
  rw [tree069,root,root059]
  exact (congrArg JFp_SHADigest.digest address069).trans hash069
#print axioms root069
theorem shape069 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 61440=tree069 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 61440)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 5 61440 (by decide),siblings 5 (by decide) 61440 (by decide)]
  rw [shape059 f g inputs siblings]
  rfl
#print axioms shape069
end AspisR1.JHh_C_Gr_M2Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_C_Gr_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input070 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash070.message
def value070 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash070.result
theorem hash070 : JFp_SHADigest.digest input070=value070 := by
  have law := JHe_SHARealization.tree2 ⟨70, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash070
theorem address070 : BinMerkle32Path.nodeInput (children value060 (JGc_TX2_HashBytes.state [12,35,6,54,189,41,166,74,28,227,63,181,204,131,135,75,78,199,125,83,131,232,162,74,16,255,240,44,226,253,152,131]))=input070 := by rfl
#print axioms address070
def tree070 : Tree := .branch tree060 (.supplied (JGc_TX2_HashBytes.state [12,35,6,54,189,41,166,74,28,227,63,181,204,131,135,75,78,199,125,83,131,232,162,74,16,255,240,44,226,253,152,131]))
theorem root070 : root JFp_SHADigest.digest tree070=value070 := by
  rw [tree070,root,root060]
  exact (congrArg JFp_SHADigest.digest address070).trans hash070
#print axioms root070
theorem shape070 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 16384=tree070 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 16384)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape060 f g inputs siblings]
  rw [unoccupied f g 6 16448 (by decide),siblings 6 (by decide) 16448 (by decide)]
  rfl
#print axioms shape070
def input071 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash071.message
def value071 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash071.result
theorem hash071 : JFp_SHADigest.digest input071=value071 := by
  have law := JHe_SHARealization.tree2 ⟨71, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash071
theorem address071 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [34,202,202,246,204,161,168,147,72,248,145,59,46,233,17,80,67,226,203,239,118,214,122,140,141,112,234,72,115,236,35,119]) value061)=input071 := by rfl
#print axioms address071
def tree071 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [34,202,202,246,204,161,168,147,72,248,145,59,46,233,17,80,67,226,203,239,118,214,122,140,141,112,234,72,115,236,35,119])) tree061
theorem root071 : root JFp_SHADigest.digest tree071=value071 := by
  rw [tree071,root,root061]
  exact (congrArg JFp_SHADigest.digest address071).trans hash071
#print axioms root071
theorem shape071 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 23296=tree071 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 23296)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 6 23296 (by decide),siblings 6 (by decide) 23296 (by decide)]
  rw [shape061 f g inputs siblings]
  rfl
#print axioms shape071
def input072 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash072.message
def value072 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash072.result
theorem hash072 : JFp_SHADigest.digest input072=value072 := by
  have law := JHe_SHARealization.tree2 ⟨72, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash072
theorem address072 : BinMerkle32Path.nodeInput (children value062 (JGc_TX2_HashBytes.state [233,186,25,148,101,33,33,145,191,159,134,50,19,208,18,164,241,22,203,112,242,116,2,159,74,87,212,75,68,12,27,203]))=input072 := by rfl
#print axioms address072
def tree072 : Tree := .branch tree062 (.supplied (JGc_TX2_HashBytes.state [233,186,25,148,101,33,33,145,191,159,134,50,19,208,18,164,241,22,203,112,242,116,2,159,74,87,212,75,68,12,27,203]))
theorem root072 : root JFp_SHADigest.digest tree072=value072 := by
  rw [tree072,root,root062]
  exact (congrArg JFp_SHADigest.digest address072).trans hash072
#print axioms root072
theorem shape072 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 36864=tree072 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 36864)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape062 f g inputs siblings]
  rw [unoccupied f g 6 36928 (by decide),siblings 6 (by decide) 36928 (by decide)]
  rfl
#print axioms shape072
def input073 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash073.message
def value073 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash073.result
theorem hash073 : JFp_SHADigest.digest input073=value073 := by
  have law := JHe_SHARealization.tree2 ⟨73, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash073
theorem address073 : BinMerkle32Path.nodeInput (children value063 (JGc_TX2_HashBytes.state [172,95,38,161,233,39,109,98,162,182,95,62,119,94,97,67,209,214,59,41,199,165,99,92,109,80,89,57,162,40,2,101]))=input073 := by rfl
#print axioms address073
def tree073 : Tree := .branch tree063 (.supplied (JGc_TX2_HashBytes.state [172,95,38,161,233,39,109,98,162,182,95,62,119,94,97,67,209,214,59,41,199,165,99,92,109,80,89,57,162,40,2,101]))
theorem root073 : root JFp_SHADigest.digest tree073=value073 := by
  rw [tree073,root,root063]
  exact (congrArg JFp_SHADigest.digest address073).trans hash073
#print axioms root073
theorem shape073 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 39936=tree073 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 39936)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape063 f g inputs siblings]
  rw [unoccupied f g 6 40000 (by decide),siblings 6 (by decide) 40000 (by decide)]
  rfl
#print axioms shape073
def input074 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash074.message
def value074 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash074.result
theorem hash074 : JFp_SHADigest.digest input074=value074 := by
  have law := JHe_SHARealization.tree2 ⟨74, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash074
theorem address074 : BinMerkle32Path.nodeInput (children value064 (JGc_TX2_HashBytes.state [103,108,72,109,95,12,246,45,50,177,228,166,118,36,249,156,201,210,30,254,219,199,140,75,105,48,211,178,152,240,35,25]))=input074 := by rfl
#print axioms address074
def tree074 : Tree := .branch tree064 (.supplied (JGc_TX2_HashBytes.state [103,108,72,109,95,12,246,45,50,177,228,166,118,36,249,156,201,210,30,254,219,199,140,75,105,48,211,178,152,240,35,25]))
theorem root074 : root JFp_SHADigest.digest tree074=value074 := by
  rw [tree074,root,root064]
  exact (congrArg JFp_SHADigest.digest address074).trans hash074
#print axioms root074
theorem shape074 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 45952=tree074 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 45952)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape064 f g inputs siblings]
  rw [unoccupied f g 6 46016 (by decide),siblings 6 (by decide) 46016 (by decide)]
  rfl
#print axioms shape074
def input075 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash075.message
def value075 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash075.result
theorem hash075 : JFp_SHADigest.digest input075=value075 := by
  have law := JHe_SHARealization.tree2 ⟨75, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash075
theorem address075 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [76,138,139,110,125,144,229,21,210,24,82,54,6,198,0,84,11,57,149,77,118,158,174,117,16,240,50,61,167,224,164,114]) value065)=input075 := by rfl
#print axioms address075
def tree075 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [76,138,139,110,125,144,229,21,210,24,82,54,6,198,0,84,11,57,149,77,118,158,174,117,16,240,50,61,167,224,164,114])) tree065
theorem root075 : root JFp_SHADigest.digest tree075=value075 := by
  rw [tree075,root,root065]
  exact (congrArg JFp_SHADigest.digest address075).trans hash075
#print axioms root075
theorem shape075 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 48000=tree075 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 48000)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 6 48000 (by decide),siblings 6 (by decide) 48000 (by decide)]
  rw [shape065 f g inputs siblings]
  rfl
#print axioms shape075
def input076 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash076.message
def value076 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash076.result
theorem hash076 : JFp_SHADigest.digest input076=value076 := by
  have law := JHe_SHARealization.tree2 ⟨76, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash076
theorem address076 : BinMerkle32Path.nodeInput (children value066 (JGc_TX2_HashBytes.state [92,18,27,186,69,57,105,145,26,193,234,90,166,206,223,1,124,10,44,87,174,35,213,59,133,136,95,93,181,15,102,76]))=input076 := by rfl
#print axioms address076
def tree076 : Tree := .branch tree066 (.supplied (JGc_TX2_HashBytes.state [92,18,27,186,69,57,105,145,26,193,234,90,166,206,223,1,124,10,44,87,174,35,213,59,133,136,95,93,181,15,102,76]))
theorem root076 : root JFp_SHADigest.digest tree076=value076 := by
  rw [tree076,root,root066]
  exact (congrArg JFp_SHADigest.digest address076).trans hash076
#print axioms root076
theorem shape076 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 48256=tree076 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 48256)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape066 f g inputs siblings]
  rw [unoccupied f g 6 48320 (by decide),siblings 6 (by decide) 48320 (by decide)]
  rfl
#print axioms shape076
def input077 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash077.message
def value077 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash077.result
theorem hash077 : JFp_SHADigest.digest input077=value077 := by
  have law := JHe_SHARealization.tree2 ⟨77, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash077
theorem address077 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [221,19,169,114,80,134,201,224,126,254,210,16,35,216,131,101,98,130,177,176,105,17,245,221,225,119,36,214,154,102,135,54]) value067)=input077 := by rfl
#print axioms address077
def tree077 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [221,19,169,114,80,134,201,224,126,254,210,16,35,216,131,101,98,130,177,176,105,17,245,221,225,119,36,214,154,102,135,54])) tree067
theorem root077 : root JFp_SHADigest.digest tree077=value077 := by
  rw [tree077,root,root067]
  exact (congrArg JFp_SHADigest.digest address077).trans hash077
#print axioms root077
theorem shape077 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 52224=tree077 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 52224)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 6 52224 (by decide),siblings 6 (by decide) 52224 (by decide)]
  rw [shape067 f g inputs siblings]
  rfl
#print axioms shape077
def input078 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash078.message
def value078 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash078.result
theorem hash078 : JFp_SHADigest.digest input078=value078 := by
  have law := JHe_SHARealization.tree2 ⟨78, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash078
theorem address078 : BinMerkle32Path.nodeInput (children value068 (JGc_TX2_HashBytes.state [109,164,95,10,124,67,109,255,131,97,215,20,161,76,7,61,239,85,118,134,154,43,70,21,176,103,66,1,84,203,21,178]))=input078 := by rfl
#print axioms address078
def tree078 : Tree := .branch tree068 (.supplied (JGc_TX2_HashBytes.state [109,164,95,10,124,67,109,255,131,97,215,20,161,76,7,61,239,85,118,134,154,43,70,21,176,103,66,1,84,203,21,178]))
theorem root078 : root JFp_SHADigest.digest tree078=value078 := by
  rw [tree078,root,root068]
  exact (congrArg JFp_SHADigest.digest address078).trans hash078
#print axioms root078
theorem shape078 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 54144=tree078 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 54144)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape068 f g inputs siblings]
  rw [unoccupied f g 6 54208 (by decide),siblings 6 (by decide) 54208 (by decide)]
  rfl
#print axioms shape078
def input079 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash079.message
def value079 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash079.result
theorem hash079 : JFp_SHADigest.digest input079=value079 := by
  have law := JHe_SHARealization.tree2 ⟨79, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash079
theorem address079 : BinMerkle32Path.nodeInput (children value069 (JGc_TX2_HashBytes.state [189,12,56,31,97,219,222,72,85,148,145,20,206,134,123,106,158,78,125,165,158,116,184,132,122,139,219,64,2,74,255,189]))=input079 := by rfl
#print axioms address079
def tree079 : Tree := .branch tree069 (.supplied (JGc_TX2_HashBytes.state [189,12,56,31,97,219,222,72,85,148,145,20,206,134,123,106,158,78,125,165,158,116,184,132,122,139,219,64,2,74,255,189]))
theorem root079 : root JFp_SHADigest.digest tree079=value079 := by
  rw [tree079,root,root069]
  exact (congrArg JFp_SHADigest.digest address079).trans hash079
#print axioms root079
theorem shape079 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 61440=tree079 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 61440)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape069 f g inputs siblings]
  rw [unoccupied f g 6 61504 (by decide),siblings 6 (by decide) 61504 (by decide)]
  rfl
#print axioms shape079
end AspisR1.JHh_C_Gr_M2Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_C_Gr_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input080 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash080.message
def value080 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash080.result
theorem hash080 : JFp_SHADigest.digest input080=value080 := by
  have law := JHe_SHARealization.tree2 ⟨80, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash080
theorem address080 : BinMerkle32Path.nodeInput (children value070 (JGc_TX2_HashBytes.state [40,66,57,248,171,64,19,248,144,29,218,123,161,176,117,253,56,239,96,55,49,89,217,26,77,172,100,4,82,114,8,47]))=input080 := by rfl
#print axioms address080
def tree080 : Tree := .branch tree070 (.supplied (JGc_TX2_HashBytes.state [40,66,57,248,171,64,19,248,144,29,218,123,161,176,117,253,56,239,96,55,49,89,217,26,77,172,100,4,82,114,8,47]))
theorem root080 : root JFp_SHADigest.digest tree080=value080 := by
  rw [tree080,root,root070]
  exact (congrArg JFp_SHADigest.digest address080).trans hash080
#print axioms root080
theorem shape080 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 16384=tree080 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 16384)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape070 f g inputs siblings]
  rw [unoccupied f g 7 16512 (by decide),siblings 7 (by decide) 16512 (by decide)]
  rfl
#print axioms shape080
def input081 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash081.message
def value081 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash081.result
theorem hash081 : JFp_SHADigest.digest input081=value081 := by
  have law := JHe_SHARealization.tree2 ⟨81, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash081
theorem address081 : BinMerkle32Path.nodeInput (children value071 (JGc_TX2_HashBytes.state [120,18,210,66,139,22,89,122,216,63,152,111,19,111,250,236,51,117,22,85,177,55,233,164,124,98,214,151,43,78,253,217]))=input081 := by rfl
#print axioms address081
def tree081 : Tree := .branch tree071 (.supplied (JGc_TX2_HashBytes.state [120,18,210,66,139,22,89,122,216,63,152,111,19,111,250,236,51,117,22,85,177,55,233,164,124,98,214,151,43,78,253,217]))
theorem root081 : root JFp_SHADigest.digest tree081=value081 := by
  rw [tree081,root,root071]
  exact (congrArg JFp_SHADigest.digest address081).trans hash081
#print axioms root081
theorem shape081 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 23296=tree081 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 23296)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape071 f g inputs siblings]
  rw [unoccupied f g 7 23424 (by decide),siblings 7 (by decide) 23424 (by decide)]
  rfl
#print axioms shape081
def input082 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash082.message
def value082 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash082.result
theorem hash082 : JFp_SHADigest.digest input082=value082 := by
  have law := JHe_SHARealization.tree2 ⟨82, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash082
theorem address082 : BinMerkle32Path.nodeInput (children value072 (JGc_TX2_HashBytes.state [103,178,124,35,134,30,155,148,34,121,100,244,172,217,64,95,40,79,185,187,244,242,175,24,223,94,11,7,90,165,205,4]))=input082 := by rfl
#print axioms address082
def tree082 : Tree := .branch tree072 (.supplied (JGc_TX2_HashBytes.state [103,178,124,35,134,30,155,148,34,121,100,244,172,217,64,95,40,79,185,187,244,242,175,24,223,94,11,7,90,165,205,4]))
theorem root082 : root JFp_SHADigest.digest tree082=value082 := by
  rw [tree082,root,root072]
  exact (congrArg JFp_SHADigest.digest address082).trans hash082
#print axioms root082
theorem shape082 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 36864=tree082 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 36864)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape072 f g inputs siblings]
  rw [unoccupied f g 7 36992 (by decide),siblings 7 (by decide) 36992 (by decide)]
  rfl
#print axioms shape082
def input083 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash083.message
def value083 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash083.result
theorem hash083 : JFp_SHADigest.digest input083=value083 := by
  have law := JHe_SHARealization.tree2 ⟨83, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash083
theorem address083 : BinMerkle32Path.nodeInput (children value073 (JGc_TX2_HashBytes.state [226,197,181,101,101,106,77,175,222,109,224,228,95,177,222,195,21,159,182,213,81,131,239,8,141,115,209,130,107,39,67,196]))=input083 := by rfl
#print axioms address083
def tree083 : Tree := .branch tree073 (.supplied (JGc_TX2_HashBytes.state [226,197,181,101,101,106,77,175,222,109,224,228,95,177,222,195,21,159,182,213,81,131,239,8,141,115,209,130,107,39,67,196]))
theorem root083 : root JFp_SHADigest.digest tree083=value083 := by
  rw [tree083,root,root073]
  exact (congrArg JFp_SHADigest.digest address083).trans hash083
#print axioms root083
theorem shape083 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 39936=tree083 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 39936)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape073 f g inputs siblings]
  rw [unoccupied f g 7 40064 (by decide),siblings 7 (by decide) 40064 (by decide)]
  rfl
#print axioms shape083
def input084 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash084.message
def value084 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash084.result
theorem hash084 : JFp_SHADigest.digest input084=value084 := by
  have law := JHe_SHARealization.tree2 ⟨84, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash084
theorem address084 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [79,228,52,63,17,238,145,181,34,187,241,201,144,85,1,72,189,253,175,235,150,239,202,216,171,117,100,210,208,107,207,133]) value074)=input084 := by rfl
#print axioms address084
def tree084 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [79,228,52,63,17,238,145,181,34,187,241,201,144,85,1,72,189,253,175,235,150,239,202,216,171,117,100,210,208,107,207,133])) tree074
theorem root084 : root JFp_SHADigest.digest tree084=value084 := by
  rw [tree084,root,root074]
  exact (congrArg JFp_SHADigest.digest address084).trans hash084
#print axioms root084
theorem shape084 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 45824=tree084 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 45824)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 7 45824 (by decide),siblings 7 (by decide) 45824 (by decide)]
  rw [shape074 f g inputs siblings]
  rfl
#print axioms shape084
def input085 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash085.message
def value085 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash085.result
theorem hash085 : JFp_SHADigest.digest input085=value085 := by
  have law := JHe_SHARealization.tree2 ⟨85, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash085
theorem address085 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [86,120,3,16,14,90,106,11,180,182,86,253,48,54,60,51,178,176,131,60,37,248,185,4,109,125,236,97,241,128,96,4]) value075)=input085 := by rfl
#print axioms address085
def tree085 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [86,120,3,16,14,90,106,11,180,182,86,253,48,54,60,51,178,176,131,60,37,248,185,4,109,125,236,97,241,128,96,4])) tree075
theorem root085 : root JFp_SHADigest.digest tree085=value085 := by
  rw [tree085,root,root075]
  exact (congrArg JFp_SHADigest.digest address085).trans hash085
#print axioms root085
theorem shape085 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 47872=tree085 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 47872)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 7 47872 (by decide),siblings 7 (by decide) 47872 (by decide)]
  rw [shape075 f g inputs siblings]
  rfl
#print axioms shape085
def input086 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash086.message
def value086 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash086.result
theorem hash086 : JFp_SHADigest.digest input086=value086 := by
  have law := JHe_SHARealization.tree2 ⟨86, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash086
theorem address086 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [220,66,240,11,224,86,73,210,202,251,58,129,19,14,221,86,179,240,73,49,122,95,40,107,25,132,18,187,64,22,193,243]) value076)=input086 := by rfl
#print axioms address086
def tree086 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [220,66,240,11,224,86,73,210,202,251,58,129,19,14,221,86,179,240,73,49,122,95,40,107,25,132,18,187,64,22,193,243])) tree076
theorem root086 : root JFp_SHADigest.digest tree086=value086 := by
  rw [tree086,root,root076]
  exact (congrArg JFp_SHADigest.digest address086).trans hash086
#print axioms root086
theorem shape086 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 48128=tree086 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 48128)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 7 48128 (by decide),siblings 7 (by decide) 48128 (by decide)]
  rw [shape076 f g inputs siblings]
  rfl
#print axioms shape086
def input087 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash087.message
def value087 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash087.result
theorem hash087 : JFp_SHADigest.digest input087=value087 := by
  have law := JHe_SHARealization.tree2 ⟨87, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash087
theorem address087 : BinMerkle32Path.nodeInput (children value077 (JGc_TX2_HashBytes.state [238,251,240,139,222,162,82,13,5,62,14,101,72,222,153,31,136,216,181,124,9,170,18,210,98,111,201,200,121,154,149,146]))=input087 := by rfl
#print axioms address087
def tree087 : Tree := .branch tree077 (.supplied (JGc_TX2_HashBytes.state [238,251,240,139,222,162,82,13,5,62,14,101,72,222,153,31,136,216,181,124,9,170,18,210,98,111,201,200,121,154,149,146]))
theorem root087 : root JFp_SHADigest.digest tree087=value087 := by
  rw [tree087,root,root077]
  exact (congrArg JFp_SHADigest.digest address087).trans hash087
#print axioms root087
theorem shape087 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 52224=tree087 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 52224)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape077 f g inputs siblings]
  rw [unoccupied f g 7 52352 (by decide),siblings 7 (by decide) 52352 (by decide)]
  rfl
#print axioms shape087
def input088 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash088.message
def value088 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash088.result
theorem hash088 : JFp_SHADigest.digest input088=value088 := by
  have law := JHe_SHARealization.tree2 ⟨88, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash088
theorem address088 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [84,69,130,187,250,41,60,93,211,73,58,43,46,132,20,190,44,37,46,171,236,6,109,126,126,222,174,144,62,90,134,121]) value078)=input088 := by rfl
#print axioms address088
def tree088 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [84,69,130,187,250,41,60,93,211,73,58,43,46,132,20,190,44,37,46,171,236,6,109,126,126,222,174,144,62,90,134,121])) tree078
theorem root088 : root JFp_SHADigest.digest tree088=value088 := by
  rw [tree088,root,root078]
  exact (congrArg JFp_SHADigest.digest address088).trans hash088
#print axioms root088
theorem shape088 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 54016=tree088 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 54016)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 7 54016 (by decide),siblings 7 (by decide) 54016 (by decide)]
  rw [shape078 f g inputs siblings]
  rfl
#print axioms shape088
def input089 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash089.message
def value089 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash089.result
theorem hash089 : JFp_SHADigest.digest input089=value089 := by
  have law := JHe_SHARealization.tree2 ⟨89, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash089
theorem address089 : BinMerkle32Path.nodeInput (children value079 (JGc_TX2_HashBytes.state [220,229,124,220,129,225,225,51,200,62,80,161,62,80,246,77,79,81,125,59,117,195,120,42,167,10,86,19,49,243,144,77]))=input089 := by rfl
#print axioms address089
def tree089 : Tree := .branch tree079 (.supplied (JGc_TX2_HashBytes.state [220,229,124,220,129,225,225,51,200,62,80,161,62,80,246,77,79,81,125,59,117,195,120,42,167,10,86,19,49,243,144,77]))
theorem root089 : root JFp_SHADigest.digest tree089=value089 := by
  rw [tree089,root,root079]
  exact (congrArg JFp_SHADigest.digest address089).trans hash089
#print axioms root089
theorem shape089 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 61440=tree089 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 61440)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape079 f g inputs siblings]
  rw [unoccupied f g 7 61568 (by decide),siblings 7 (by decide) 61568 (by decide)]
  rfl
#print axioms shape089
end AspisR1.JHh_C_Gr_M2Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_C_Gr_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input090 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash090.message
def value090 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash090.result
theorem hash090 : JFp_SHADigest.digest input090=value090 := by
  have law := JHe_SHARealization.tree2 ⟨90, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash090
theorem address090 : BinMerkle32Path.nodeInput (children value080 (JGc_TX2_HashBytes.state [129,139,196,209,161,57,255,18,26,252,18,30,104,179,146,146,53,230,56,126,7,69,243,43,190,141,29,119,242,28,130,38]))=input090 := by rfl
#print axioms address090
def tree090 : Tree := .branch tree080 (.supplied (JGc_TX2_HashBytes.state [129,139,196,209,161,57,255,18,26,252,18,30,104,179,146,146,53,230,56,126,7,69,243,43,190,141,29,119,242,28,130,38]))
theorem root090 : root JFp_SHADigest.digest tree090=value090 := by
  rw [tree090,root,root080]
  exact (congrArg JFp_SHADigest.digest address090).trans hash090
#print axioms root090
theorem shape090 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 16384=tree090 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 16384)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape080 f g inputs siblings]
  rw [unoccupied f g 8 16640 (by decide),siblings 8 (by decide) 16640 (by decide)]
  rfl
#print axioms shape090
def input091 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash091.message
def value091 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash091.result
theorem hash091 : JFp_SHADigest.digest input091=value091 := by
  have law := JHe_SHARealization.tree2 ⟨91, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash091
theorem address091 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [117,171,13,240,245,18,102,9,11,246,84,158,171,240,2,164,240,189,242,95,184,129,172,128,21,241,222,68,41,84,235,244]) value081)=input091 := by rfl
#print axioms address091
def tree091 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [117,171,13,240,245,18,102,9,11,246,84,158,171,240,2,164,240,189,242,95,184,129,172,128,21,241,222,68,41,84,235,244])) tree081
theorem root091 : root JFp_SHADigest.digest tree091=value091 := by
  rw [tree091,root,root081]
  exact (congrArg JFp_SHADigest.digest address091).trans hash091
#print axioms root091
theorem shape091 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 23040=tree091 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 23040)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 8 23040 (by decide),siblings 8 (by decide) 23040 (by decide)]
  rw [shape081 f g inputs siblings]
  rfl
#print axioms shape091
def input092 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash092.message
def value092 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash092.result
theorem hash092 : JFp_SHADigest.digest input092=value092 := by
  have law := JHe_SHARealization.tree2 ⟨92, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash092
theorem address092 : BinMerkle32Path.nodeInput (children value082 (JGc_TX2_HashBytes.state [112,189,186,141,150,13,115,120,9,52,169,201,97,163,116,115,235,94,1,206,49,158,11,31,22,195,133,0,144,140,158,171]))=input092 := by rfl
#print axioms address092
def tree092 : Tree := .branch tree082 (.supplied (JGc_TX2_HashBytes.state [112,189,186,141,150,13,115,120,9,52,169,201,97,163,116,115,235,94,1,206,49,158,11,31,22,195,133,0,144,140,158,171]))
theorem root092 : root JFp_SHADigest.digest tree092=value092 := by
  rw [tree092,root,root082]
  exact (congrArg JFp_SHADigest.digest address092).trans hash092
#print axioms root092
theorem shape092 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 36864=tree092 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 36864)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape082 f g inputs siblings]
  rw [unoccupied f g 8 37120 (by decide),siblings 8 (by decide) 37120 (by decide)]
  rfl
#print axioms shape092
def input093 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash093.message
def value093 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash093.result
theorem hash093 : JFp_SHADigest.digest input093=value093 := by
  have law := JHe_SHARealization.tree2 ⟨93, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash093
theorem address093 : BinMerkle32Path.nodeInput (children value083 (JGc_TX2_HashBytes.state [65,26,79,118,1,189,37,99,244,25,130,70,240,70,77,82,137,79,54,72,155,62,165,187,17,76,147,69,84,119,4,194]))=input093 := by rfl
#print axioms address093
def tree093 : Tree := .branch tree083 (.supplied (JGc_TX2_HashBytes.state [65,26,79,118,1,189,37,99,244,25,130,70,240,70,77,82,137,79,54,72,155,62,165,187,17,76,147,69,84,119,4,194]))
theorem root093 : root JFp_SHADigest.digest tree093=value093 := by
  rw [tree093,root,root083]
  exact (congrArg JFp_SHADigest.digest address093).trans hash093
#print axioms root093
theorem shape093 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 39936=tree093 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 39936)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape083 f g inputs siblings]
  rw [unoccupied f g 8 40192 (by decide),siblings 8 (by decide) 40192 (by decide)]
  rfl
#print axioms shape093
def input094 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash094.message
def value094 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash094.result
theorem hash094 : JFp_SHADigest.digest input094=value094 := by
  have law := JHe_SHARealization.tree2 ⟨94, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash094
theorem address094 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [5,50,44,127,47,107,97,24,250,118,48,94,115,31,165,104,79,252,110,153,14,168,101,168,252,13,13,176,5,235,11,81]) value084)=input094 := by rfl
#print axioms address094
def tree094 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [5,50,44,127,47,107,97,24,250,118,48,94,115,31,165,104,79,252,110,153,14,168,101,168,252,13,13,176,5,235,11,81])) tree084
theorem root094 : root JFp_SHADigest.digest tree094=value094 := by
  rw [tree094,root,root084]
  exact (congrArg JFp_SHADigest.digest address094).trans hash094
#print axioms root094
theorem shape094 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 45568=tree094 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 45568)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 8 45568 (by decide),siblings 8 (by decide) 45568 (by decide)]
  rw [shape084 f g inputs siblings]
  rfl
#print axioms shape094
def input095 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash095.message
def value095 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash095.result
theorem hash095 : JFp_SHADigest.digest input095=value095 := by
  have law := JHe_SHARealization.tree2 ⟨95, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash095
theorem address095 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [146,141,221,94,160,176,42,173,76,178,63,145,211,201,232,196,75,136,193,192,49,187,63,18,243,80,211,155,61,26,74,208]) value085)=input095 := by rfl
#print axioms address095
def tree095 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [146,141,221,94,160,176,42,173,76,178,63,145,211,201,232,196,75,136,193,192,49,187,63,18,243,80,211,155,61,26,74,208])) tree085
theorem root095 : root JFp_SHADigest.digest tree095=value095 := by
  rw [tree095,root,root085]
  exact (congrArg JFp_SHADigest.digest address095).trans hash095
#print axioms root095
theorem shape095 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 47616=tree095 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 47616)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 8 47616 (by decide),siblings 8 (by decide) 47616 (by decide)]
  rw [shape085 f g inputs siblings]
  rfl
#print axioms shape095
def input096 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash096.message
def value096 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash096.result
theorem hash096 : JFp_SHADigest.digest input096=value096 := by
  have law := JHe_SHARealization.tree2 ⟨96, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash096
theorem address096 : BinMerkle32Path.nodeInput (children value086 (JGc_TX2_HashBytes.state [58,139,189,211,146,54,137,210,150,131,78,126,15,71,120,13,201,90,22,49,210,172,123,254,222,83,204,237,128,27,176,200]))=input096 := by rfl
#print axioms address096
def tree096 : Tree := .branch tree086 (.supplied (JGc_TX2_HashBytes.state [58,139,189,211,146,54,137,210,150,131,78,126,15,71,120,13,201,90,22,49,210,172,123,254,222,83,204,237,128,27,176,200]))
theorem root096 : root JFp_SHADigest.digest tree096=value096 := by
  rw [tree096,root,root086]
  exact (congrArg JFp_SHADigest.digest address096).trans hash096
#print axioms root096
theorem shape096 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 48128=tree096 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 48128)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape086 f g inputs siblings]
  rw [unoccupied f g 8 48384 (by decide),siblings 8 (by decide) 48384 (by decide)]
  rfl
#print axioms shape096
def input097 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash097.message
def value097 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash097.result
theorem hash097 : JFp_SHADigest.digest input097=value097 := by
  have law := JHe_SHARealization.tree2 ⟨97, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash097
theorem address097 : BinMerkle32Path.nodeInput (children value087 (JGc_TX2_HashBytes.state [154,56,13,62,76,194,157,36,143,253,24,180,172,172,162,80,108,195,243,117,154,221,90,53,117,255,176,94,77,196,103,105]))=input097 := by rfl
#print axioms address097
def tree097 : Tree := .branch tree087 (.supplied (JGc_TX2_HashBytes.state [154,56,13,62,76,194,157,36,143,253,24,180,172,172,162,80,108,195,243,117,154,221,90,53,117,255,176,94,77,196,103,105]))
theorem root097 : root JFp_SHADigest.digest tree097=value097 := by
  rw [tree097,root,root087]
  exact (congrArg JFp_SHADigest.digest address097).trans hash097
#print axioms root097
theorem shape097 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 52224=tree097 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 52224)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape087 f g inputs siblings]
  rw [unoccupied f g 8 52480 (by decide),siblings 8 (by decide) 52480 (by decide)]
  rfl
#print axioms shape097
def input098 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash098.message
def value098 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash098.result
theorem hash098 : JFp_SHADigest.digest input098=value098 := by
  have law := JHe_SHARealization.tree2 ⟨98, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash098
theorem address098 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [83,238,52,1,11,212,139,234,45,234,168,167,214,33,22,250,35,179,143,118,209,205,200,109,206,127,81,82,170,12,47,46]) value088)=input098 := by rfl
#print axioms address098
def tree098 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [83,238,52,1,11,212,139,234,45,234,168,167,214,33,22,250,35,179,143,118,209,205,200,109,206,127,81,82,170,12,47,46])) tree088
theorem root098 : root JFp_SHADigest.digest tree098=value098 := by
  rw [tree098,root,root088]
  exact (congrArg JFp_SHADigest.digest address098).trans hash098
#print axioms root098
theorem shape098 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 53760=tree098 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 53760)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 8 53760 (by decide),siblings 8 (by decide) 53760 (by decide)]
  rw [shape088 f g inputs siblings]
  rfl
#print axioms shape098
def input099 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash099.message
def value099 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash099.result
theorem hash099 : JFp_SHADigest.digest input099=value099 := by
  have law := JHe_SHARealization.tree2 ⟨99, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash099
theorem address099 : BinMerkle32Path.nodeInput (children value089 (JGc_TX2_HashBytes.state [241,181,167,150,78,64,96,175,242,182,206,109,16,199,77,118,205,21,203,47,68,204,83,194,143,140,213,34,148,113,119,188]))=input099 := by rfl
#print axioms address099
def tree099 : Tree := .branch tree089 (.supplied (JGc_TX2_HashBytes.state [241,181,167,150,78,64,96,175,242,182,206,109,16,199,77,118,205,21,203,47,68,204,83,194,143,140,213,34,148,113,119,188]))
theorem root099 : root JFp_SHADigest.digest tree099=value099 := by
  rw [tree099,root,root089]
  exact (congrArg JFp_SHADigest.digest address099).trans hash099
#print axioms root099
theorem shape099 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 61440=tree099 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 61440)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape089 f g inputs siblings]
  rw [unoccupied f g 8 61696 (by decide),siblings 8 (by decide) 61696 (by decide)]
  rfl
#print axioms shape099
end AspisR1.JHh_C_Gr_M2Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_C_Gr_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input100 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash100.message
def value100 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash100.result
theorem hash100 : JFp_SHADigest.digest input100=value100 := by
  have law := JHe_SHARealization.tree2 ⟨100, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash100
theorem address100 : BinMerkle32Path.nodeInput (children value090 (JGc_TX2_HashBytes.state [88,84,1,232,136,97,59,25,95,79,171,202,50,73,181,91,156,235,147,175,149,228,206,198,32,112,132,5,97,147,214,87]))=input100 := by rfl
#print axioms address100
def tree100 : Tree := .branch tree090 (.supplied (JGc_TX2_HashBytes.state [88,84,1,232,136,97,59,25,95,79,171,202,50,73,181,91,156,235,147,175,149,228,206,198,32,112,132,5,97,147,214,87]))
theorem root100 : root JFp_SHADigest.digest tree100=value100 := by
  rw [tree100,root,root090]
  exact (congrArg JFp_SHADigest.digest address100).trans hash100
#print axioms root100
theorem shape100 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 16384=tree100 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 16384)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape090 f g inputs siblings]
  rw [unoccupied f g 9 16896 (by decide),siblings 9 (by decide) 16896 (by decide)]
  rfl
#print axioms shape100
def input101 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash101.message
def value101 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash101.result
theorem hash101 : JFp_SHADigest.digest input101=value101 := by
  have law := JHe_SHARealization.tree2 ⟨101, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash101
theorem address101 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [49,215,205,0,167,207,189,105,41,234,95,241,207,36,58,176,15,198,248,69,205,13,124,207,197,169,58,105,168,219,95,167]) value091)=input101 := by rfl
#print axioms address101
def tree101 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [49,215,205,0,167,207,189,105,41,234,95,241,207,36,58,176,15,198,248,69,205,13,124,207,197,169,58,105,168,219,95,167])) tree091
theorem root101 : root JFp_SHADigest.digest tree101=value101 := by
  rw [tree101,root,root091]
  exact (congrArg JFp_SHADigest.digest address101).trans hash101
#print axioms root101
theorem shape101 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 22528=tree101 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 22528)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 9 22528 (by decide),siblings 9 (by decide) 22528 (by decide)]
  rw [shape091 f g inputs siblings]
  rfl
#print axioms shape101
def input102 : Bytes := JGc_TX2_M2Roots.input126
def value102 : State := JGc_TX2_M2Roots.value126
theorem hash102 : JFp_SHADigest.digest input102=value102 := by
  have law := JHe_SHARealization.tree2 ⟨102, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash102
theorem address102 : BinMerkle32Path.nodeInput (children value092 (JGc_TX2_HashBytes.state [70,134,10,212,128,202,30,53,59,190,3,183,111,214,12,121,235,23,249,250,247,194,155,71,110,138,126,72,15,189,138,73]))=input102 := by rfl
#print axioms address102
def tree102 : Tree := .branch tree092 (.supplied (JGc_TX2_HashBytes.state [70,134,10,212,128,202,30,53,59,190,3,183,111,214,12,121,235,23,249,250,247,194,155,71,110,138,126,72,15,189,138,73]))
theorem root102 : root JFp_SHADigest.digest tree102=value102 := by
  rw [tree102,root,root092]
  exact (congrArg JFp_SHADigest.digest address102).trans hash102
#print axioms root102
theorem shape102 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 36864=tree102 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 36864)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape092 f g inputs siblings]
  rw [unoccupied f g 9 37376 (by decide),siblings 9 (by decide) 37376 (by decide)]
  rfl
#print axioms shape102
def input103 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash103.message
def value103 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash103.result
theorem hash103 : JFp_SHADigest.digest input103=value103 := by
  have law := JHe_SHARealization.tree2 ⟨103, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash103
theorem address103 : BinMerkle32Path.nodeInput (children value093 (JGc_TX2_HashBytes.state [10,39,97,221,95,35,17,150,57,128,55,20,176,218,99,160,138,81,221,206,84,83,87,98,113,139,232,155,109,200,172,130]))=input103 := by rfl
#print axioms address103
def tree103 : Tree := .branch tree093 (.supplied (JGc_TX2_HashBytes.state [10,39,97,221,95,35,17,150,57,128,55,20,176,218,99,160,138,81,221,206,84,83,87,98,113,139,232,155,109,200,172,130]))
theorem root103 : root JFp_SHADigest.digest tree103=value103 := by
  rw [tree103,root,root093]
  exact (congrArg JFp_SHADigest.digest address103).trans hash103
#print axioms root103
theorem shape103 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 39936=tree103 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 39936)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape093 f g inputs siblings]
  rw [unoccupied f g 9 40448 (by decide),siblings 9 (by decide) 40448 (by decide)]
  rfl
#print axioms shape103
def input104 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash104.message
def value104 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash104.result
theorem hash104 : JFp_SHADigest.digest input104=value104 := by
  have law := JHe_SHARealization.tree2 ⟨104, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash104
theorem address104 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [229,179,51,182,45,79,191,222,28,125,224,229,212,199,58,124,45,169,119,100,137,91,235,224,126,108,71,10,55,150,202,46]) value094)=input104 := by rfl
#print axioms address104
def tree104 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [229,179,51,182,45,79,191,222,28,125,224,229,212,199,58,124,45,169,119,100,137,91,235,224,126,108,71,10,55,150,202,46])) tree094
theorem root104 : root JFp_SHADigest.digest tree104=value104 := by
  rw [tree104,root,root094]
  exact (congrArg JFp_SHADigest.digest address104).trans hash104
#print axioms root104
theorem shape104 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 45056=tree104 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 45056)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 9 45056 (by decide),siblings 9 (by decide) 45056 (by decide)]
  rw [shape094 f g inputs siblings]
  rfl
#print axioms shape104
def input105 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash105.message
def value105 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash105.result
theorem hash105 : JFp_SHADigest.digest input105=value105 := by
  have law := JHe_SHARealization.tree2 ⟨105, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash105
theorem address105 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [225,153,52,213,21,109,19,130,233,62,120,171,84,78,8,150,137,100,130,111,192,224,128,194,151,56,130,138,66,53,217,85]) value095)=input105 := by rfl
#print axioms address105
def tree105 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [225,153,52,213,21,109,19,130,233,62,120,171,84,78,8,150,137,100,130,111,192,224,128,194,151,56,130,138,66,53,217,85])) tree095
theorem root105 : root JFp_SHADigest.digest tree105=value105 := by
  rw [tree105,root,root095]
  exact (congrArg JFp_SHADigest.digest address105).trans hash105
#print axioms root105
theorem shape105 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 47104=tree105 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 47104)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 9 47104 (by decide),siblings 9 (by decide) 47104 (by decide)]
  rw [shape095 f g inputs siblings]
  rfl
#print axioms shape105
def input106 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash106.message
def value106 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash106.result
theorem hash106 : JFp_SHADigest.digest input106=value106 := by
  have law := JHe_SHARealization.tree2 ⟨106, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash106
theorem address106 : BinMerkle32Path.nodeInput (children value096 (JGc_TX2_HashBytes.state [63,157,246,68,247,156,167,236,33,147,196,148,11,221,187,24,80,152,186,62,219,33,199,166,205,164,91,93,159,195,123,173]))=input106 := by rfl
#print axioms address106
def tree106 : Tree := .branch tree096 (.supplied (JGc_TX2_HashBytes.state [63,157,246,68,247,156,167,236,33,147,196,148,11,221,187,24,80,152,186,62,219,33,199,166,205,164,91,93,159,195,123,173]))
theorem root106 : root JFp_SHADigest.digest tree106=value106 := by
  rw [tree106,root,root096]
  exact (congrArg JFp_SHADigest.digest address106).trans hash106
#print axioms root106
theorem shape106 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 48128=tree106 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 48128)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape096 f g inputs siblings]
  rw [unoccupied f g 9 48640 (by decide),siblings 9 (by decide) 48640 (by decide)]
  rfl
#print axioms shape106
def input107 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash107.message
def value107 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash107.result
theorem hash107 : JFp_SHADigest.digest input107=value107 := by
  have law := JHe_SHARealization.tree2 ⟨107, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash107
theorem address107 : BinMerkle32Path.nodeInput (children value097 (JGc_TX2_HashBytes.state [248,231,68,50,25,138,85,185,211,224,168,58,116,149,74,89,192,55,189,210,248,227,32,87,12,111,89,138,56,159,211,246]))=input107 := by rfl
#print axioms address107
def tree107 : Tree := .branch tree097 (.supplied (JGc_TX2_HashBytes.state [248,231,68,50,25,138,85,185,211,224,168,58,116,149,74,89,192,55,189,210,248,227,32,87,12,111,89,138,56,159,211,246]))
theorem root107 : root JFp_SHADigest.digest tree107=value107 := by
  rw [tree107,root,root097]
  exact (congrArg JFp_SHADigest.digest address107).trans hash107
#print axioms root107
theorem shape107 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 52224=tree107 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 52224)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape097 f g inputs siblings]
  rw [unoccupied f g 9 52736 (by decide),siblings 9 (by decide) 52736 (by decide)]
  rfl
#print axioms shape107
def input108 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash108.message
def value108 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash108.result
theorem hash108 : JFp_SHADigest.digest input108=value108 := by
  have law := JHe_SHARealization.tree2 ⟨108, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash108
theorem address108 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [121,77,72,55,197,240,239,13,38,245,104,128,31,8,169,49,228,30,30,39,15,43,17,9,136,253,250,13,253,55,182,203]) value098)=input108 := by rfl
#print axioms address108
def tree108 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [121,77,72,55,197,240,239,13,38,245,104,128,31,8,169,49,228,30,30,39,15,43,17,9,136,253,250,13,253,55,182,203])) tree098
theorem root108 : root JFp_SHADigest.digest tree108=value108 := by
  rw [tree108,root,root098]
  exact (congrArg JFp_SHADigest.digest address108).trans hash108
#print axioms root108
theorem shape108 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 53248=tree108 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 53248)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 9 53248 (by decide),siblings 9 (by decide) 53248 (by decide)]
  rw [shape098 f g inputs siblings]
  rfl
#print axioms shape108
def input109 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash109.message
def value109 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash109.result
theorem hash109 : JFp_SHADigest.digest input109=value109 := by
  have law := JHe_SHARealization.tree2 ⟨109, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash109
theorem address109 : BinMerkle32Path.nodeInput (children value099 (JGc_TX2_HashBytes.state [3,74,103,5,105,99,91,75,105,84,175,69,235,21,94,73,167,83,99,16,155,139,147,0,108,111,209,105,20,221,143,245]))=input109 := by rfl
#print axioms address109
def tree109 : Tree := .branch tree099 (.supplied (JGc_TX2_HashBytes.state [3,74,103,5,105,99,91,75,105,84,175,69,235,21,94,73,167,83,99,16,155,139,147,0,108,111,209,105,20,221,143,245]))
theorem root109 : root JFp_SHADigest.digest tree109=value109 := by
  rw [tree109,root,root099]
  exact (congrArg JFp_SHADigest.digest address109).trans hash109
#print axioms root109
theorem shape109 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 61440=tree109 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 61440)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape099 f g inputs siblings]
  rw [unoccupied f g 9 61952 (by decide),siblings 9 (by decide) 61952 (by decide)]
  rfl
#print axioms shape109
end AspisR1.JHh_C_Gr_M2Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_C_Gr_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input110 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash110.message
def value110 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash110.result
theorem hash110 : JFp_SHADigest.digest input110=value110 := by
  have law := JHe_SHARealization.tree2 ⟨110, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash110
theorem address110 : BinMerkle32Path.nodeInput (children value100 (JGc_TX2_HashBytes.state [59,119,73,169,22,234,180,231,182,173,95,170,28,240,254,211,36,169,197,26,155,126,34,120,70,14,2,233,116,165,77,238]))=input110 := by rfl
#print axioms address110
def tree110 : Tree := .branch tree100 (.supplied (JGc_TX2_HashBytes.state [59,119,73,169,22,234,180,231,182,173,95,170,28,240,254,211,36,169,197,26,155,126,34,120,70,14,2,233,116,165,77,238]))
theorem root110 : root JFp_SHADigest.digest tree110=value110 := by
  rw [tree110,root,root100]
  exact (congrArg JFp_SHADigest.digest address110).trans hash110
#print axioms root110
theorem shape110 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 16384=tree110 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 16384)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape100 f g inputs siblings]
  rw [unoccupied f g 10 17408 (by decide),siblings 10 (by decide) 17408 (by decide)]
  rfl
#print axioms shape110
def input111 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash111.message
def value111 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash111.result
theorem hash111 : JFp_SHADigest.digest input111=value111 := by
  have law := JHe_SHARealization.tree2 ⟨111, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash111
theorem address111 : BinMerkle32Path.nodeInput (children value101 (JGc_TX2_HashBytes.state [155,115,130,156,18,114,181,14,247,172,123,90,64,80,209,183,141,7,129,131,179,236,78,203,48,11,88,165,65,162,198,183]))=input111 := by rfl
#print axioms address111
def tree111 : Tree := .branch tree101 (.supplied (JGc_TX2_HashBytes.state [155,115,130,156,18,114,181,14,247,172,123,90,64,80,209,183,141,7,129,131,179,236,78,203,48,11,88,165,65,162,198,183]))
theorem root111 : root JFp_SHADigest.digest tree111=value111 := by
  rw [tree111,root,root101]
  exact (congrArg JFp_SHADigest.digest address111).trans hash111
#print axioms root111
theorem shape111 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 22528=tree111 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 22528)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape101 f g inputs siblings]
  rw [unoccupied f g 10 23552 (by decide),siblings 10 (by decide) 23552 (by decide)]
  rfl
#print axioms shape111
def input112 : Bytes := JGc_TX2_M2Roots.input137
def value112 : State := JGc_TX2_M2Roots.value137
theorem hash112 : JFp_SHADigest.digest input112=value112 := by
  have law := JHe_SHARealization.tree2 ⟨112, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash112
theorem address112 : BinMerkle32Path.nodeInput (children value102 (JGc_TX2_HashBytes.state [233,55,27,237,249,242,100,244,152,233,196,144,235,235,188,45,24,60,248,32,79,165,176,201,186,138,207,29,188,87,191,26]))=input112 := by rfl
#print axioms address112
def tree112 : Tree := .branch tree102 (.supplied (JGc_TX2_HashBytes.state [233,55,27,237,249,242,100,244,152,233,196,144,235,235,188,45,24,60,248,32,79,165,176,201,186,138,207,29,188,87,191,26]))
theorem root112 : root JFp_SHADigest.digest tree112=value112 := by
  rw [tree112,root,root102]
  exact (congrArg JFp_SHADigest.digest address112).trans hash112
#print axioms root112
theorem shape112 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 36864=tree112 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 36864)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape102 f g inputs siblings]
  rw [unoccupied f g 10 37888 (by decide),siblings 10 (by decide) 37888 (by decide)]
  rfl
#print axioms shape112
def input113 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash113.message
def value113 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash113.result
theorem hash113 : JFp_SHADigest.digest input113=value113 := by
  have law := JHe_SHARealization.tree2 ⟨113, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash113
theorem address113 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [21,19,134,173,7,2,210,241,42,75,194,167,15,45,14,161,26,153,154,65,84,193,25,180,34,59,39,191,21,32,25,135]) value103)=input113 := by rfl
#print axioms address113
def tree113 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [21,19,134,173,7,2,210,241,42,75,194,167,15,45,14,161,26,153,154,65,84,193,25,180,34,59,39,191,21,32,25,135])) tree103
theorem root113 : root JFp_SHADigest.digest tree113=value113 := by
  rw [tree113,root,root103]
  exact (congrArg JFp_SHADigest.digest address113).trans hash113
#print axioms root113
theorem shape113 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 38912=tree113 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 38912)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 10 38912 (by decide),siblings 10 (by decide) 38912 (by decide)]
  rw [shape103 f g inputs siblings]
  rfl
#print axioms shape113
def input114 : Bytes := JGc_TX2_M2Roots.input140
def value114 : State := JGc_TX2_M2Roots.value140
theorem hash114 : JFp_SHADigest.digest input114=value114 := by
  have law := JHe_SHARealization.tree2 ⟨114, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash114
theorem address114 : BinMerkle32Path.nodeInput (children value104 (JGc_TX2_HashBytes.state [186,104,47,209,122,14,221,153,173,57,67,129,86,66,66,233,32,56,115,230,42,38,98,22,111,235,154,246,230,200,89,9]))=input114 := by rfl
#print axioms address114
def tree114 : Tree := .branch tree104 (.supplied (JGc_TX2_HashBytes.state [186,104,47,209,122,14,221,153,173,57,67,129,86,66,66,233,32,56,115,230,42,38,98,22,111,235,154,246,230,200,89,9]))
theorem root114 : root JFp_SHADigest.digest tree114=value114 := by
  rw [tree114,root,root104]
  exact (congrArg JFp_SHADigest.digest address114).trans hash114
#print axioms root114
theorem shape114 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 45056=tree114 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 45056)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape104 f g inputs siblings]
  rw [unoccupied f g 10 46080 (by decide),siblings 10 (by decide) 46080 (by decide)]
  rfl
#print axioms shape114
def input115 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash115.message
def value115 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash115.result
theorem hash115 : JFp_SHADigest.digest input115=value115 := by
  have law := JHe_SHARealization.tree2 ⟨115, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash115
theorem address115 : BinMerkle32Path.nodeInput (children value105 value106)=input115 := by rfl
#print axioms address115
def tree115 : Tree := .branch tree105 tree106
theorem root115 : root JFp_SHADigest.digest tree115=value115 := by
  rw [tree115,root,root105,root106]
  exact (congrArg JFp_SHADigest.digest address115).trans hash115
#print axioms root115
theorem shape115 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 47104=tree115 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 47104)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape105 f g inputs siblings]
  rw [shape106 f g inputs siblings]
  rfl
#print axioms shape115
def input116 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash116.message
def value116 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash116.result
theorem hash116 : JFp_SHADigest.digest input116=value116 := by
  have law := JHe_SHARealization.tree2 ⟨116, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash116
theorem address116 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [160,11,21,231,220,161,4,194,145,32,85,167,167,102,254,212,177,251,97,177,99,36,215,15,114,51,84,17,30,107,226,151]) value107)=input116 := by rfl
#print axioms address116
def tree116 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [160,11,21,231,220,161,4,194,145,32,85,167,167,102,254,212,177,251,97,177,99,36,215,15,114,51,84,17,30,107,226,151])) tree107
theorem root116 : root JFp_SHADigest.digest tree116=value116 := by
  rw [tree116,root,root107]
  exact (congrArg JFp_SHADigest.digest address116).trans hash116
#print axioms root116
theorem shape116 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 51200=tree116 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 51200)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 10 51200 (by decide),siblings 10 (by decide) 51200 (by decide)]
  rw [shape107 f g inputs siblings]
  rfl
#print axioms shape116
def input117 : Bytes := JGc_TX2_M2Roots.input141
def value117 : State := JGc_TX2_M2Roots.value141
theorem hash117 : JFp_SHADigest.digest input117=value117 := by
  have law := JHe_SHARealization.tree2 ⟨117, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash117
theorem address117 : BinMerkle32Path.nodeInput (children value108 (JGc_TX2_HashBytes.state [79,82,178,84,61,147,76,0,223,43,6,169,212,57,122,92,55,118,68,198,170,121,50,188,215,151,199,101,127,208,161,110]))=input117 := by rfl
#print axioms address117
def tree117 : Tree := .branch tree108 (.supplied (JGc_TX2_HashBytes.state [79,82,178,84,61,147,76,0,223,43,6,169,212,57,122,92,55,118,68,198,170,121,50,188,215,151,199,101,127,208,161,110]))
theorem root117 : root JFp_SHADigest.digest tree117=value117 := by
  rw [tree117,root,root108]
  exact (congrArg JFp_SHADigest.digest address117).trans hash117
#print axioms root117
theorem shape117 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 53248=tree117 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 53248)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape108 f g inputs siblings]
  rw [unoccupied f g 10 54272 (by decide),siblings 10 (by decide) 54272 (by decide)]
  rfl
#print axioms shape117
def input118 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash118.message
def value118 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash118.result
theorem hash118 : JFp_SHADigest.digest input118=value118 := by
  have law := JHe_SHARealization.tree2 ⟨118, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash118
theorem address118 : BinMerkle32Path.nodeInput (children value109 (JGc_TX2_HashBytes.state [113,199,16,24,52,72,40,241,79,147,76,57,246,194,155,42,154,10,38,24,158,221,37,151,184,52,224,109,73,38,75,31]))=input118 := by rfl
#print axioms address118
def tree118 : Tree := .branch tree109 (.supplied (JGc_TX2_HashBytes.state [113,199,16,24,52,72,40,241,79,147,76,57,246,194,155,42,154,10,38,24,158,221,37,151,184,52,224,109,73,38,75,31]))
theorem root118 : root JFp_SHADigest.digest tree118=value118 := by
  rw [tree118,root,root109]
  exact (congrArg JFp_SHADigest.digest address118).trans hash118
#print axioms root118
theorem shape118 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 61440=tree118 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 61440)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape109 f g inputs siblings]
  rw [unoccupied f g 10 62464 (by decide),siblings 10 (by decide) 62464 (by decide)]
  rfl
#print axioms shape118
end AspisR1.JHh_C_Gr_M2Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_C_Gr_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input119 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash119.message
def value119 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash119.result
theorem hash119 : JFp_SHADigest.digest input119=value119 := by
  have law := JHe_SHARealization.tree2 ⟨119, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash119
theorem address119 : BinMerkle32Path.nodeInput (children value110 (JGc_TX2_HashBytes.state [170,153,117,5,67,73,116,195,9,13,223,78,171,169,18,95,110,140,91,37,34,17,55,253,160,219,151,107,246,215,123,234]))=input119 := by rfl
#print axioms address119
def tree119 : Tree := .branch tree110 (.supplied (JGc_TX2_HashBytes.state [170,153,117,5,67,73,116,195,9,13,223,78,171,169,18,95,110,140,91,37,34,17,55,253,160,219,151,107,246,215,123,234]))
theorem root119 : root JFp_SHADigest.digest tree119=value119 := by
  rw [tree119,root,root110]
  exact (congrArg JFp_SHADigest.digest address119).trans hash119
#print axioms root119
theorem shape119 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 12 16384=tree119 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 12 16384)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape110 f g inputs siblings]
  rw [unoccupied f g 11 18432 (by decide),siblings 11 (by decide) 18432 (by decide)]
  rfl
#print axioms shape119
def input120 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash120.message
def value120 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash120.result
theorem hash120 : JFp_SHADigest.digest input120=value120 := by
  have law := JHe_SHARealization.tree2 ⟨120, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash120
theorem address120 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [216,219,166,205,15,70,186,97,80,104,229,181,34,249,182,130,33,182,45,106,240,203,133,32,164,178,203,167,172,135,153,82]) value111)=input120 := by rfl
#print axioms address120
def tree120 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [216,219,166,205,15,70,186,97,80,104,229,181,34,249,182,130,33,182,45,106,240,203,133,32,164,178,203,167,172,135,153,82])) tree111
theorem root120 : root JFp_SHADigest.digest tree120=value120 := by
  rw [tree120,root,root111]
  exact (congrArg JFp_SHADigest.digest address120).trans hash120
#print axioms root120
theorem shape120 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 12 20480=tree120 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 12 20480)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 11 20480 (by decide),siblings 11 (by decide) 20480 (by decide)]
  rw [shape111 f g inputs siblings]
  rfl
#print axioms shape120
def input121 : Bytes := JGc_TX2_M2Roots.input147
def value121 : State := JGc_TX2_M2Roots.value147
theorem hash121 : JFp_SHADigest.digest input121=value121 := by
  have law := JHe_SHARealization.tree2 ⟨121, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash121
theorem address121 : BinMerkle32Path.nodeInput (children value112 value113)=input121 := by rfl
#print axioms address121
def tree121 : Tree := .branch tree112 tree113
theorem root121 : root JFp_SHADigest.digest tree121=value121 := by
  rw [tree121,root,root112,root113]
  exact (congrArg JFp_SHADigest.digest address121).trans hash121
#print axioms root121
theorem shape121 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 12 36864=tree121 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 12 36864)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape112 f g inputs siblings]
  rw [shape113 f g inputs siblings]
  rfl
#print axioms shape121
def input122 : Bytes := JGc_TX2_M2Roots.input149
def value122 : State := JGc_TX2_M2Roots.value149
theorem hash122 : JFp_SHADigest.digest input122=value122 := by
  have law := JHe_SHARealization.tree2 ⟨122, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash122
theorem address122 : BinMerkle32Path.nodeInput (children value114 value115)=input122 := by rfl
#print axioms address122
def tree122 : Tree := .branch tree114 tree115
theorem root122 : root JFp_SHADigest.digest tree122=value122 := by
  rw [tree122,root,root114,root115]
  exact (congrArg JFp_SHADigest.digest address122).trans hash122
#print axioms root122
theorem shape122 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 12 45056=tree122 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 12 45056)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape114 f g inputs siblings]
  rw [shape115 f g inputs siblings]
  rfl
#print axioms shape122
def input123 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash123.message
def value123 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash123.result
theorem hash123 : JFp_SHADigest.digest input123=value123 := by
  have law := JHe_SHARealization.tree2 ⟨123, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash123
theorem address123 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [60,65,38,140,93,216,131,203,27,50,149,248,16,182,251,250,174,83,223,189,145,180,153,159,227,187,210,101,127,209,224,34]) value116)=input123 := by rfl
#print axioms address123
def tree123 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [60,65,38,140,93,216,131,203,27,50,149,248,16,182,251,250,174,83,223,189,145,180,153,159,227,187,210,101,127,209,224,34])) tree116
theorem root123 : root JFp_SHADigest.digest tree123=value123 := by
  rw [tree123,root,root116]
  exact (congrArg JFp_SHADigest.digest address123).trans hash123
#print axioms root123
theorem shape123 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 12 49152=tree123 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 12 49152)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 11 49152 (by decide),siblings 11 (by decide) 49152 (by decide)]
  rw [shape116 f g inputs siblings]
  rfl
#print axioms shape123
def input124 : Bytes := JGc_TX2_M2Roots.input150
def value124 : State := JGc_TX2_M2Roots.value150
theorem hash124 : JFp_SHADigest.digest input124=value124 := by
  have law := JHe_SHARealization.tree2 ⟨124, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash124
theorem address124 : BinMerkle32Path.nodeInput (children value117 (JGc_TX2_HashBytes.state [6,129,243,133,201,8,108,81,39,87,79,34,75,133,83,63,178,115,227,174,129,80,5,186,58,198,235,77,231,201,140,216]))=input124 := by rfl
#print axioms address124
def tree124 : Tree := .branch tree117 (.supplied (JGc_TX2_HashBytes.state [6,129,243,133,201,8,108,81,39,87,79,34,75,133,83,63,178,115,227,174,129,80,5,186,58,198,235,77,231,201,140,216]))
theorem root124 : root JFp_SHADigest.digest tree124=value124 := by
  rw [tree124,root,root117]
  exact (congrArg JFp_SHADigest.digest address124).trans hash124
#print axioms root124
theorem shape124 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 12 53248=tree124 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 12 53248)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape117 f g inputs siblings]
  rw [unoccupied f g 11 55296 (by decide),siblings 11 (by decide) 55296 (by decide)]
  rfl
#print axioms shape124
def input125 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash125.message
def value125 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash125.result
theorem hash125 : JFp_SHADigest.digest input125=value125 := by
  have law := JHe_SHARealization.tree2 ⟨125, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash125
theorem address125 : BinMerkle32Path.nodeInput (children value118 (JGc_TX2_HashBytes.state [197,225,37,96,40,16,98,217,159,88,149,106,254,188,227,153,131,207,22,77,128,46,74,234,41,2,48,235,27,112,230,153]))=input125 := by rfl
#print axioms address125
def tree125 : Tree := .branch tree118 (.supplied (JGc_TX2_HashBytes.state [197,225,37,96,40,16,98,217,159,88,149,106,254,188,227,153,131,207,22,77,128,46,74,234,41,2,48,235,27,112,230,153]))
theorem root125 : root JFp_SHADigest.digest tree125=value125 := by
  rw [tree125,root,root118]
  exact (congrArg JFp_SHADigest.digest address125).trans hash125
#print axioms root125
theorem shape125 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 12 61440=tree125 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 12 61440)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape118 f g inputs siblings]
  rw [unoccupied f g 11 63488 (by decide),siblings 11 (by decide) 63488 (by decide)]
  rfl
#print axioms shape125
end AspisR1.JHh_C_Gr_M2Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_C_Gr_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input126 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash126.message
def value126 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash126.result
theorem hash126 : JFp_SHADigest.digest input126=value126 := by
  have law := JHe_SHARealization.tree2 ⟨126, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash126
theorem address126 : BinMerkle32Path.nodeInput (children value119 value120)=input126 := by rfl
#print axioms address126
def tree126 : Tree := .branch tree119 tree120
theorem root126 : root JFp_SHADigest.digest tree126=value126 := by
  rw [tree126,root,root119,root120]
  exact (congrArg JFp_SHADigest.digest address126).trans hash126
#print axioms root126
theorem shape126 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 13 16384=tree126 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 13 16384)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape119 f g inputs siblings]
  rw [shape120 f g inputs siblings]
  rfl
#print axioms shape126
def input127 : Bytes := JGc_TX2_M2Roots.input153
def value127 : State := JGc_TX2_M2Roots.value153
theorem hash127 : JFp_SHADigest.digest input127=value127 := by
  have law := JHe_SHARealization.tree2 ⟨127, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash127
theorem address127 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [224,16,194,66,110,101,52,10,179,79,182,34,88,250,183,144,150,209,247,104,194,136,212,200,251,140,161,235,156,251,89,119]) value121)=input127 := by rfl
#print axioms address127
def tree127 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [224,16,194,66,110,101,52,10,179,79,182,34,88,250,183,144,150,209,247,104,194,136,212,200,251,140,161,235,156,251,89,119])) tree121
theorem root127 : root JFp_SHADigest.digest tree127=value127 := by
  rw [tree127,root,root121]
  exact (congrArg JFp_SHADigest.digest address127).trans hash127
#print axioms root127
theorem shape127 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 13 32768=tree127 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 13 32768)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 12 32768 (by decide),siblings 12 (by decide) 32768 (by decide)]
  rw [shape121 f g inputs siblings]
  rfl
#print axioms shape127
def input128 : Bytes := JGc_TX2_M2Roots.input154
def value128 : State := JGc_TX2_M2Roots.value154
theorem hash128 : JFp_SHADigest.digest input128=value128 := by
  have law := JHe_SHARealization.tree2 ⟨128, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash128
theorem address128 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [110,140,14,207,117,61,1,50,35,2,166,51,143,145,85,104,230,62,135,43,183,242,18,192,131,122,184,244,45,205,135,7]) value122)=input128 := by rfl
#print axioms address128
def tree128 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [110,140,14,207,117,61,1,50,35,2,166,51,143,145,85,104,230,62,135,43,183,242,18,192,131,122,184,244,45,205,135,7])) tree122
theorem root128 : root JFp_SHADigest.digest tree128=value128 := by
  rw [tree128,root,root122]
  exact (congrArg JFp_SHADigest.digest address128).trans hash128
#print axioms root128
theorem shape128 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 13 40960=tree128 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 13 40960)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 12 40960 (by decide),siblings 12 (by decide) 40960 (by decide)]
  rw [shape122 f g inputs siblings]
  rfl
#print axioms shape128
def input129 : Bytes := JGc_TX2_M2Roots.input155
def value129 : State := JGc_TX2_M2Roots.value155
theorem hash129 : JFp_SHADigest.digest input129=value129 := by
  have law := JHe_SHARealization.tree2 ⟨129, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash129
theorem address129 : BinMerkle32Path.nodeInput (children value123 value124)=input129 := by rfl
#print axioms address129
def tree129 : Tree := .branch tree123 tree124
theorem root129 : root JFp_SHADigest.digest tree129=value129 := by
  rw [tree129,root,root123,root124]
  exact (congrArg JFp_SHADigest.digest address129).trans hash129
#print axioms root129
theorem shape129 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 13 49152=tree129 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 13 49152)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape123 f g inputs siblings]
  rw [shape124 f g inputs siblings]
  rfl
#print axioms shape129
def input130 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash130.message
def value130 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash130.result
theorem hash130 : JFp_SHADigest.digest input130=value130 := by
  have law := JHe_SHARealization.tree2 ⟨130, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash130
theorem address130 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [141,64,232,71,157,231,216,45,93,159,181,117,153,193,198,18,181,64,29,202,192,123,128,152,11,184,100,22,94,163,139,202]) value125)=input130 := by rfl
#print axioms address130
def tree130 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [141,64,232,71,157,231,216,45,93,159,181,117,153,193,198,18,181,64,29,202,192,123,128,152,11,184,100,22,94,163,139,202])) tree125
theorem root130 : root JFp_SHADigest.digest tree130=value130 := by
  rw [tree130,root,root125]
  exact (congrArg JFp_SHADigest.digest address130).trans hash130
#print axioms root130
theorem shape130 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 13 57344=tree130 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 13 57344)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 12 57344 (by decide),siblings 12 (by decide) 57344 (by decide)]
  rw [shape125 f g inputs siblings]
  rfl
#print axioms shape130
end AspisR1.JHh_C_Gr_M2Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_C_Gr_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input131 : Bytes := JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash131.message
def value131 : State := JFp_SHADigest.output JHe_C_Gr_M2.Hash131.result
theorem hash131 : JFp_SHADigest.digest input131=value131 := by
  have law := JHe_SHARealization.tree2 ⟨131, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash131
theorem address131 : BinMerkle32Path.nodeInput (children value126 (JGc_TX2_HashBytes.state [34,112,182,144,67,6,64,238,194,132,59,239,67,247,9,55,180,77,17,67,178,157,110,43,220,71,83,104,67,4,240,73]))=input131 := by rfl
#print axioms address131
def tree131 : Tree := .branch tree126 (.supplied (JGc_TX2_HashBytes.state [34,112,182,144,67,6,64,238,194,132,59,239,67,247,9,55,180,77,17,67,178,157,110,43,220,71,83,104,67,4,240,73]))
theorem root131 : root JFp_SHADigest.digest tree131=value131 := by
  rw [tree131,root,root126]
  exact (congrArg JFp_SHADigest.digest address131).trans hash131
#print axioms root131
theorem shape131 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 14 16384=tree131 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 14 16384)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape126 f g inputs siblings]
  rw [unoccupied f g 13 24576 (by decide),siblings 13 (by decide) 24576 (by decide)]
  rfl
#print axioms shape131
def input132 : Bytes := JGc_TX2_M2Roots.input157
def value132 : State := JGc_TX2_M2Roots.value157
theorem hash132 : JFp_SHADigest.digest input132=value132 := by
  have law := JHe_SHARealization.tree2 ⟨132, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash132
theorem address132 : BinMerkle32Path.nodeInput (children value127 value128)=input132 := by rfl
#print axioms address132
def tree132 : Tree := .branch tree127 tree128
theorem root132 : root JFp_SHADigest.digest tree132=value132 := by
  rw [tree132,root,root127,root128]
  exact (congrArg JFp_SHADigest.digest address132).trans hash132
#print axioms root132
theorem shape132 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 14 32768=tree132 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 14 32768)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape127 f g inputs siblings]
  rw [shape128 f g inputs siblings]
  rfl
#print axioms shape132
def input133 : Bytes := JGc_TX2_M2Roots.input158
def value133 : State := JGc_TX2_M2Roots.value158
theorem hash133 : JFp_SHADigest.digest input133=value133 := by
  have law := JHe_SHARealization.tree2 ⟨133, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash133
theorem address133 : BinMerkle32Path.nodeInput (children value129 value130)=input133 := by rfl
#print axioms address133
def tree133 : Tree := .branch tree129 tree130
theorem root133 : root JFp_SHADigest.digest tree133=value133 := by
  rw [tree133,root,root129,root130]
  exact (congrArg JFp_SHADigest.digest address133).trans hash133
#print axioms root133
theorem shape133 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 14 49152=tree133 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 14 49152)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape129 f g inputs siblings]
  rw [shape130 f g inputs siblings]
  rfl
#print axioms shape133
end AspisR1.JHh_C_Gr_M2Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_C_Gr_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input134 : Bytes := JGc_TX2_M2Roots.input159
def value134 : State := JGc_TX2_M2Roots.value159
theorem hash134 : JFp_SHADigest.digest input134=value134 := by
  have law := JHe_SHARealization.tree2 ⟨134, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash134
theorem address134 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [28,133,8,205,254,15,139,95,248,58,225,38,64,117,236,147,74,140,165,149,219,239,213,12,183,184,40,0,97,10,83,26]) value131)=input134 := by rfl
#print axioms address134
def tree134 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [28,133,8,205,254,15,139,95,248,58,225,38,64,117,236,147,74,140,165,149,219,239,213,12,183,184,40,0,97,10,83,26])) tree131
theorem root134 : root JFp_SHADigest.digest tree134=value134 := by
  rw [tree134,root,root131]
  exact (congrArg JFp_SHADigest.digest address134).trans hash134
#print axioms root134
theorem shape134 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 15 0=tree134 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 15 0)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 14 0 (by decide),siblings 14 (by decide) 0 (by decide)]
  rw [shape131 f g inputs siblings]
  rfl
#print axioms shape134
def input135 : Bytes := JGc_TX2_M2Roots.input160
def value135 : State := JGc_TX2_M2Roots.value160
theorem hash135 : JFp_SHADigest.digest input135=value135 := by
  have law := JHe_SHARealization.tree2 ⟨135, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash135
theorem address135 : BinMerkle32Path.nodeInput (children value132 value133)=input135 := by rfl
#print axioms address135
def tree135 : Tree := .branch tree132 tree133
theorem root135 : root JFp_SHADigest.digest tree135=value135 := by
  rw [tree135,root,root132,root133]
  exact (congrArg JFp_SHADigest.digest address135).trans hash135
#print axioms root135
theorem shape135 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 15 32768=tree135 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 15 32768)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape132 f g inputs siblings]
  rw [shape133 f g inputs siblings]
  rfl
#print axioms shape135
end AspisR1.JHh_C_Gr_M2Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_C_Gr_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input136 : Bytes := JGc_TX2_M2Roots.input161
def value136 : State := JGc_TX2_M2Roots.value161
theorem hash136 : JFp_SHADigest.digest input136=value136 := by
  have law := JHe_SHARealization.tree2 ⟨136, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash136
theorem address136 : BinMerkle32Path.nodeInput (children value134 value135)=input136 := by rfl
#print axioms address136
def tree136 : Tree := .branch tree134 tree135
theorem root136 : root JFp_SHADigest.digest tree136=value136 := by
  rw [tree136,root,root134,root135]
  exact (congrArg JFp_SHADigest.digest address136).trans hash136
#print axioms root136
theorem shape136 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 16 0=tree136 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 16 0)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape134 f g inputs siblings]
  rw [shape135 f g inputs siblings]
  rfl
#print axioms shape136
end AspisR1.JHh_C_Gr_M2Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_C_Gr_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input137 : Bytes := JGc_TX2_M2Roots.input162
def value137 : State := JGc_TX2_M2Roots.value162
theorem hash137 : JFp_SHADigest.digest input137=value137 := by
  have law := JHe_SHARealization.tree2 ⟨137, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash137
theorem address137 : BinMerkle32Path.nodeInput (children value136 (JGc_TX2_HashBytes.state [128,179,167,189,122,81,88,173,23,97,55,49,163,83,67,138,131,227,2,149,136,117,239,125,58,69,31,115,134,136,165,136]))=input137 := by rfl
#print axioms address137
def tree137 : Tree := .branch tree136 (.supplied (JGc_TX2_HashBytes.state [128,179,167,189,122,81,88,173,23,97,55,49,163,83,67,138,131,227,2,149,136,117,239,125,58,69,31,115,134,136,165,136]))
theorem root137 : root JFp_SHADigest.digest tree137=value137 := by
  rw [tree137,root,root136]
  exact (congrArg JFp_SHADigest.digest address137).trans hash137
#print axioms root137
theorem shape137 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 17 0=tree137 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 17 0)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape136 f g inputs siblings]
  rw [unoccupied f g 16 65536 (by decide),siblings 16 (by decide) 65536 (by decide)]
  rfl
#print axioms shape137
end AspisR1.JHh_C_Gr_M2Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_C_Gr_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input138 : Bytes := JGc_TX2_M2Roots.input163
def value138 : State := JGc_TX2_M2Roots.value163
theorem hash138 : JFp_SHADigest.digest input138=value138 := by
  have law := JHe_SHARealization.tree2 ⟨138, by decide⟩
  dsimp only [JHe_SHAInputs2.input,JHe_SHAInputs2.expected] at law
  exact law
#print axioms hash138
theorem address138 : BinMerkle32Path.nodeInput (children value137 (JGc_TX2_HashBytes.state [220,196,233,115,158,7,124,8,46,188,36,235,198,156,139,68,223,130,204,114,37,155,16,71,174,150,102,35,254,100,134,80]))=input138 := by rfl
#print axioms address138
def tree138 : Tree := .branch tree137 (.supplied (JGc_TX2_HashBytes.state [220,196,233,115,158,7,124,8,46,188,36,235,198,156,139,68,223,130,204,114,37,155,16,71,174,150,102,35,254,100,134,80]))
theorem root138 : root JFp_SHADigest.digest tree138=value138 := by
  rw [tree138,root,root137]
  exact (congrArg JFp_SHADigest.digest address138).trans hash138
#print axioms root138
theorem shape138 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 18 0=tree138 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 18 0)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape137 f g inputs siblings]
  rw [unoccupied f g 17 131072 (by decide),siblings 17 (by decide) 131072 (by decide)]
  rfl
#print axioms shape138
end AspisR1.JHh_C_Gr_M2Roots
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_C_Gr_M2Root
open Aeneas Aeneas.Std
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiBuild OracleDecisionMultiTree JHh_C_Gr_M2Roots

def retainedRoot : State := JGc_TX2_M2Root.retainedRoot

theorem value_eq : value138=retainedRoot := by
  funext i
  fin_cases i <;> rfl
#print axioms value_eq

theorem source (f : Nat → Bytes) (g : Nat → Nat → State)
    (inputs : InputLaw f) (siblings : SiblingLaw g) :
    root JFp_SHADigest.digest (build indices f g 18 0)=retainedRoot := by
  rw [shape138 f g inputs siblings,root138,value_eq]
#print axioms source

theorem selected_queries : OraclePortSelectedDraft.selected
    (Port4B_KeyInstall.queries JFo_Prepared.value.queries) 0 2=indices := rfl
#print axioms selected_queries

theorem inhabited : ∃ (f : Nat → Bytes) (g : Nat → Nat → State),
    InputLaw f ∧ SiblingLaw g ∧
    root JFp_SHADigest.digest (build indices f g 18 0)=retainedRoot :=
  ⟨inputAt,siblingAt,(by intro b _;rfl),(by intro h _ b _;rfl),
    source inputAt siblingAt (by intro b _;rfl) (by intro h _ b _;rfl)⟩
#print axioms inhabited
end AspisR1.JHh_C_Gr_M2Root
end
end
