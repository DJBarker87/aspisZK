/-! Solana `create_program_address` in Lean, used only as the executable pda binder of the TX2 probe:
sha256(seeds ‖ program ‖ "ProgramDerivedAddress"), rejected (none) if more than 16 seeds, a seed
longer than 32 bytes, or the digest decompresses to an ed25519 point (u/v a square mod p, with
y the little-endian digest with bit 255 cleared, u = y²-1, v = d·y²+1; curve25519-dalek
`CompressedEdwardsY::decompress`). Every query is logged as `NPP_PDA <seeds> <program> <answer>`;
NPP_check_pda.py recomputes each one. -/
namespace NPP_Pda
def p : Nat := 2 ^ 255 - 19
def d : Nat := 37095705934669439343138083508754565189542113879843219016388785533085940283555
def powMod (b e m : Nat) : Nat := Id.run do
  let mut r := 1; let mut x := b % m; let mut k := e
  for _ in [0:256] do
    if k % 2 == 1 then r := r * x % m
    x := x * x % m; k := k / 2
  return r
def onCurve (h : ByteArray) : Bool :=
  let y0 := (List.range 32).foldr (fun i acc => acc * 256 + (h.get! i).toNat) 0
  let y := (y0 % 2 ^ 255) % p
  let y2 := y * y % p
  let u := (y2 + p - 1) % p
  let v := (d * y2 + 1) % p
  let r := u * powMod v (p - 2) p % p
  let l := powMod r ((p - 1) / 2) p
  l == 0 || l == 1
def create (seeds : List (List UInt8)) (prog : List UInt8) : Option (List UInt8) :=
  if seeds.length > 16 || seeds.any (·.length > 32) then none else
  let msg := (seeds.foldl (· ++ ·) []) ++ prog ++ "ProgramDerivedAddress".toUTF8.toList
  let h := NPP_Sha.hash ⟨msg.toArray⟩
  if onCurve h then none else some h.toList
end NPP_Pda
