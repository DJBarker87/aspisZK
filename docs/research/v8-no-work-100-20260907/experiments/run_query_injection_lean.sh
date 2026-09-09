#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)" cache=/Users/dominic/ZK/AspisFormal
[[ $# == 1 && ! -e "$1" ]] || exit 2
readonly log="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"
check(){ [[ "$(shasum -a 256 "$ex/$1" | cut -d' ' -f1)" == "$2" ]] || exit 2; }
check QueryAffine.lean ef1ed7df323c3929fe49232521dbfe9ffedc8d9bb9e16b6e77944d444fcf0b89
check QueryAffine.olean a7d819d33ec2866337e4d2d0fa681bda0c19e971d6fbb04669f3cc2c392c0c0b
check SharedGammaDots.lean be975aa4fa3f7d79c002186a783d27aeb0800a1474e442ecd1b3ec37cd9ea5a0
check SharedGammaDots.olean bbd233019d79bc1fe55ef714840f6ba9a27814b48ca75d9d66f76fd3782fdc35
check AffinePrimal.lean 5853394263e336cc2cddfd860ca7e157acb207b08deed3fe20669946ae62718d
check AffinePrimal.olean e788b85338eb0a5e8e388cad6cbe5309f3475181439f46d3889bdfea22de1f74
check SemanticCarry.lean 717b4bfcef6e1517780f1052d6961c7c0c02809c247606c92262b30916177d54
check SemanticCarry.olean f90b84321f2ca2620a6963fa362af7521485bf0ced54109e084f58c05ce13ea2
check QmCrossRange.lean cb06024066b66778a8e3de356871d4766ce2d6b17a7b698890195f8a9329f409
check QmCrossRange.olean b305936b5137a85f5015d363bcb0d416a2de9e4da2ba3d4d4453ec589718f064
[[ "$(git -C "$cache/.lake/packages/mathlib" rev-parse HEAD)" == 81a5d257c8e410db227a6665ed08f64fea08e997 ]] || exit 2
cd "$cache"
{
 git -C "$ex" rev-parse HEAD
 shasum -a 256 "$ex/QueryInjection.lean" "$ex/SharedGammaDots.lean" "$ex/SharedGammaDots.olean" "$cache/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Tactic.olean"
 /Users/dominic/.elan/bin/lake env bash -c 'export LEAN_PATH="$1:$LEAN_PATH"; /usr/bin/time -l lean -M7000 -R "$1" -o "$1/QueryInjection.olean" "$1/QueryInjection.lean"' _ "$ex"
 shasum -a 256 "$ex/QueryInjection.olean"
} 2>&1 | tee "$log"
