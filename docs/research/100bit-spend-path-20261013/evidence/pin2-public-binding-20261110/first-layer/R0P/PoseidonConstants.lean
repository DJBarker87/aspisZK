import R0P.Core

/-! G3 constant transcription, inspection pin
e4d68a70d3f6beb215c9f6dd418f4a2a3740c809.
Source P = crates/aspis-statement/src/poseidon2.rs.
These constants do not supply the QM31 tower operations missing from Core;
Poseidon.lean records that boundary rather than defining a surrogate Family.
No theorem evaluates a literal table. -/
set_option autoImplicit false
namespace R0P
variable {K : Type} [Field K]

/-- P:83–104, EXTERNAL_INITIAL. Exact source-region SHA-256:
52abaf623026228d1b36fa76087eb2602cd61b0e98631777786c4a7c4bd08454. -/
def poseidonExternalInitial : Fin 4 → Fin 16 → K :=
  ![![0x768bab52, 0x70e0ab7d, 0x3d266c8a, 0x6da42045, 0x600fef22, 0x41dace6b, 0x64f9bdd4, 0x5d42d4fe, 0x76b1516d, 0x6fc9a717, 0x70ac4fb6, 0x00194ef6, 0x22b644e2, 0x1f7916d5, 0x47581be2, 0x2710a123],
    ![0x6284e867, 0x018d3afe, 0x5df99ef3, 0x4c1e467b, 0x566f6abc, 0x2994e427, 0x538a6d42, 0x5d7bf2cf, 0x7fda2dab, 0x0fd854c4, 0x46922fca, 0x3d7763a1, 0x19fd05ca, 0x0a4bbb43, 0x15075851, 0x3d903d76],
    ![0x2d290ff7, 0x40809fa0, 0x59dac6ec, 0x127927a2, 0x6bbf0ea0, 0x0294140f, 0x24742976, 0x6e84c081, 0x22484f4a, 0x354cae59, 0x0453ffe1, 0x3f47a3cc, 0x0088204e, 0x6066e109, 0x3b7c4b80, 0x6b55665d],
    ![0x3bc4b897, 0x735bf378, 0x508daf42, 0x1884fc2b, 0x7214f24c, 0x7498be0a, 0x1a60e640, 0x3303f928, 0x29b46376, 0x5c96bb68, 0x65d097a5, 0x1d358e9f, 0x4a9a9017, 0x4724cf76, 0x347af70f, 0x1e77e59a]]

/-- P:106–127, EXTERNAL_FINAL. Exact source-region SHA-256:
e275b74c1f8a96cd2379cb1b1d7f786dffae4144668b602199334485e922c9a1. -/
def poseidonExternalFinal : Fin 4 → Fin 16 → K :=
  ![![0x57090613, 0x1fa42108, 0x17bbef50, 0x1ff7e11c, 0x047b24ca, 0x4e140275, 0x4fa086f5, 0x079b309c, 0x1159bd47, 0x6d37e4e5, 0x075d8dce, 0x12121ca0, 0x7f6a7c40, 0x68e182ba, 0x5493201b, 0x0444a80e],
    ![0x0064f4c6, 0x6467abe6, 0x66975762, 0x2af68f9b, 0x345b33be, 0x1b70d47f, 0x053db717, 0x381189cb, 0x43b915f8, 0x20df3694, 0x0f459d26, 0x77a0e97b, 0x2f73e739, 0x1876c2f9, 0x65a0e29a, 0x4cabefbe],
    ![0x5abd1268, 0x4d34a760, 0x12771799, 0x69a0c9ac, 0x39091e55, 0x7f611cd0, 0x3af055da, 0x7ac0bbdf, 0x6e0f3a24, 0x41e3b6f7, 0x49b3756d, 0x568bc538, 0x20c079d8, 0x1701c72c, 0x7670dc6c, 0x5a439035],
    ![0x7c93e00e, 0x561fbb4d, 0x1178907b, 0x02737406, 0x32fb24f1, 0x6323b60a, 0x6ab12418, 0x42c99cea, 0x155a0b97, 0x53d1c6aa, 0x2bd20347, 0x279b3d73, 0x4f5f3c70, 0x0245af6c, 0x238359d3, 0x49966a59]]

/-- P:129–132, INTERNAL. Exact source-region SHA-256:
f149c66e7e6ab405edc31af5bd85b11afdbc872fe64d46aa26fff497b8fae323. -/
def poseidonInternalConstants : Fin 14 → K :=
  ![0x7f7ec4bf, 0x0421926f, 0x5198e669, 0x34db3148, 0x4368bafd, 0x66685c7f, 0x78d3249a, 0x60187881, 0x76dad67a, 0x0690b437, 0x1ea95311, 0x40e5369a, 0x38f103fc, 0x1d226a21]

/-- P:134, INTERNAL_SHIFTS. Exact source-region SHA-256:
0498beff372384d7b4fb3a2739789fa0d53ec0700aa26d92f239a61f2e7f2534. Also state_only_poseidon.rs:305. -/
def poseidonInternalShifts : Fin 15 → Nat :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 13, 14, 15, 16]

end R0P
