# Stage 2a: both actual final-round decoders

JGo_TX2_FieldRead.source supplies the actual installed FIn field call from a
bounded symbolic source window and a native parser call. JGo_TX2_Windows.cell
splits a 224-byte round window without reducing the retained proof buffer.
JGo_TX2_Cell0_0..0_6 and Cell1_0..1_6 instantiate all14 native parsers and actual
FIn field calls, each selecting its SAME retained32-byte window. No decoder,
canonicality, field-success or finish premise is supplied. The source generator
--check matches all14 modules. 006/007/009–022 pass at current hashes. 008's
attempted parser rfl failed and was replaced by the existing fixed_success_iff
parser theorem with eight bounded limb checks. It is retained without credit.

This stage removes decoder obligations only from these fixed local facts.
It does not remove any actual ARX_Root.deployed hypothesis, prove pairing/dot
or accepted2, or establish complete top non-vacuity. Two round arithmetic and
forward Weights.new stages follow. No real-byte premise is proved false.
