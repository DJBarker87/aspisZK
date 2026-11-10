import NPP_ComputableSdk
set_option autoImplicit false
set_option maxHeartbeats 0
/-! NPP_ (Stream A, gate row 5, step 2 preparation). Target not yet established.

Executable inputs for the timing probe. Nothing here is a proof about the recorded run.
* `sdkAt H pda clock res ie` is the computable host dictionary, written as the body of
  `NOC_HostCtx.sdk` over the NPP_C copies; `sdkAt_eq` says it is the copy at any context.
  With `NPP_SdkNovEq.eq` (stage B) this is the 10 November host's `NOC_Run5bCtx.sdk c`.
* `Hlog` is SHA-256 computed in Lean, logging every query and digest (`NPP_Q <query> <digest>`)
  for the offline table check. -/
/-! SHA-256 (FIPS 180-4) over `ByteArray`, used only as the executable table H of the probe.
Every (query, digest) pair the run issues is logged; NPP_check_queries.py recomputes each digest
with hashlib. -/
namespace NPP_Sha
def K : Array UInt32 := #[
  0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
  0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
  0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
  0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
  0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
  0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
  0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
  0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2]
def rotr (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))
def pad (m : ByteArray) : ByteArray := Id.run do
  let len := m.size
  let mut b := m.push 0x80
  while b.size % 64 != 56 do b := b.push 0
  let bits := len * 8
  for i in [0:8] do b := b.push ((bits >>> (8 * (7 - i))) % 256).toUInt8
  return b
def hash (m : ByteArray) : ByteArray := Id.run do
  let b := pad m
  let mut h : Array UInt32 := #[0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19]
  for blk in [0:b.size / 64] do
    let mut w : Array UInt32 := Array.mkEmpty 64
    for t in [0:16] do
      let o := blk * 64 + 4 * t
      w := w.push ((b.get! o).toUInt32 <<< 24 ||| (b.get! (o+1)).toUInt32 <<< 16 ||| (b.get! (o+2)).toUInt32 <<< 8 ||| (b.get! (o+3)).toUInt32)
    for t in [16:64] do
      let s0 := rotr w[t-15]! 7 ^^^ rotr w[t-15]! 18 ^^^ (w[t-15]! >>> 3)
      let s1 := rotr w[t-2]! 17 ^^^ rotr w[t-2]! 19 ^^^ (w[t-2]! >>> 10)
      w := w.push (w[t-16]! + s0 + w[t-7]! + s1)
    let mut a := h[0]!; let mut bb := h[1]!; let mut c := h[2]!; let mut d := h[3]!
    let mut e := h[4]!; let mut f := h[5]!; let mut g := h[6]!; let mut hh := h[7]!
    for t in [0:64] do
      let S1 := rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25
      let ch := (e &&& f) ^^^ ((~~~ e) &&& g)
      let t1 := hh + S1 + ch + K[t]! + w[t]!
      let S0 := rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22
      let maj := (a &&& bb) ^^^ (a &&& c) ^^^ (bb &&& c)
      let t2 := S0 + maj
      hh := g; g := f; f := e; e := d + t1; d := c; c := bb; bb := a; a := t1 + t2
    h := #[h[0]!+a, h[1]!+bb, h[2]!+c, h[3]!+d, h[4]!+e, h[5]!+f, h[6]!+g, h[7]!+hh]
  let mut out := ByteArray.empty
  for x in h do
    for i in [0:4] do out := out.push ((x >>> (8 * (3 - i).toUInt32)) &&& 0xff).toUInt8
  return out
def hexChar (n : Nat) : Char := "0123456789abcdef".get ⟨n⟩
def hex (b : ByteArray) : String := b.foldl (fun s x => s.push (hexChar (x.toNat / 16)) |>.push (hexChar (x.toNat % 16))) ""
def unhex (s : String) : List UInt8 :=
  let v (c : Char) : Nat := if c.isDigit then c.toNat - 48 else c.toNat - 87
  let rec go : List Char → List UInt8
    | a :: b :: r => (v a * 16 + v b).toUInt8 :: go r
    | _ => []
  go s.trim.toList
end NPP_Sha

namespace NPP_Probe
open Aeneas Aeneas.Std AspisR1

abbrev HBytes := AspisV8R19.DuplexFrames.Bytes
abbrev HState := AspisV8R19.SourceDuplexStep.State

def toBA (q : HBytes) : ByteArray := ⟨(q.map fun b => b.val.toUInt8).toArray⟩

/-- H: SHA-256 with every query logged to stderr. -/
def Hlog (q : HBytes) : HState :=
  let ba := toBA q
  let d := NPP_Sha.hash ba
  dbgTrace s!"NPP_Q {NPP_Sha.hex ba} {NPP_Sha.hex d}" fun _ =>
    fun i => ⟨(d.get! i.val).toNat % 256, Nat.mod_lt _ (by decide)⟩

def sdkAt (H : HBytes → HState) (pda : List RSL.Bytes → RSL.B32 → Option RSL.B32)
    (clock : Except RSL.ProgramError UInt64) (res : NP6_StdModel.Reservation)
    (ie : NFN_NEW_GeometryDictionary.CE) : AdapterRw.Ops :=
  let env := DGP_HostDigest.envInst H pda clock res
  let missing := NPP_C.NNH_Tx2Configuration.select
    (NNH_CorrectConfiguration.residual (NOC_HostSeed.m0 env.reservation) env) env
  NPP_C.AspisR1.DrvC_Installation.sdk (NPP_C.AspisR1.FIp_Install.configuration ie
    (NPP_C.AspisR1.IDa_Deployed.deployedConfiguration missing ie res) res)

theorem sdkAt_eq {W Tx : Type} (c : NOC_HostCtx.Ctx W Tx) :
    NPP_C.AspisR1.NOC_Run5bCtx.sdk c =
      sdkAt c.sha256 c.fixed.pda c.fixed.clock c.fixed.reservation c.fixed.indexError := rfl

def u8 (x : UInt8) : U8 := ⟨x.toBitVec⟩
def usz (n : Nat) : Usize := if h : n < 2 ^ UScalarTy.Usize.numBits then UScalar.ofNatCore n h else 0#usize
def slice {α : Type} (l : List α) : Slice α :=
  if h : l.length ≤ Usize.max then ⟨l, h⟩ else ⟨[], by simp⟩
def vec {α : Type} (l : List α) : alloc.vec.Vec α :=
  if h : l.length ≤ Usize.max then ⟨l, h⟩ else ⟨[], by simp⟩
def key (l : List UInt8) : AdapterRw.solana_pubkey.Pubkey :=
  if h : (l.map u8).length = (32#usize).val then (⟨l.map u8, h⟩ : Aeneas.Std.Array U8 32#usize)
  else Aeneas.Std.Array.repeat 32#usize 0#u8

def acct (line : String) (data : ByteArray) : AdapterRw.r1_pool_adapter.owned.OwnedAccount :=
  let w := (line.splitOn " ").toArray
  { key := key (NPP_Sha.unhex w[0]!), owner := key (NPP_Sha.unhex w[1]!),
    is_signer := w[2]! == "1", is_writable := w[3]! == "1", executable := w[4]! == "1",
    length := .Ok (usz data.size), bytes := .Ok (vec (data.toList.map u8)) }

def vecBytes (v : alloc.vec.Vec U8) : List Nat := v.val.map fun x => x.bv.toNat

def pda0 : List RSL.Bytes → RSL.B32 → Option RSL.B32 := fun _ _ => none
def clock0 : Except RSL.ProgramError UInt64 := .ok 520606640
def res0 : NP6_StdModel.Reservation := .Ok ()

end NPP_Probe

/-! Sanity evaluations (small): the SHA-256 test vector, and the first dictionary call of
`stage1_owned` (op1 on the instruction data against [3,10]) at the computable sdk. -/
#eval NPP_Sha.hex (NPP_Sha.hash "abc".toUTF8)
open AdapterRw Aeneas.Std in
#eval
  let sdk := NPP_Probe.sdkAt NPP_Probe.Hlog NPP_Probe.pda0 NPP_Probe.clock0 NPP_Probe.res0 NFN_NEW_GeometryDictionary.err
  match sdk.op1 core.cmp.PartialEqU8 (NPP_Probe.slice [NPP_Probe.u8 3, NPP_Probe.u8 10])
      (Aeneas.Std.Array.make 2#usize [3#u8, 10#u8]) with
  | .ok b => s!"op1 ok {b}"
  | _ => "op1 not ok"
#print axioms NPP_Probe.sdkAt_eq
