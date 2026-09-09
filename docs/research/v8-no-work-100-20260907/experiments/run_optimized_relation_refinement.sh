#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)"
readonly cache=/Users/dominic/ZK/AspisFormal joint=/tmp/aspis-v8-joint-cache.n3hmg5
[[ $# == 1 && ! -e "$1" ]] || exit 2
readonly log="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"
check(){ [[ "$(shasum -a 256 "$1" | cut -d' ' -f1)" == "$2" ]] || { echo "Provenance mismatch: $1"; exit 2; }; }
source_cache(){
  check "$ex/../../../../AspisFormal/AspisFormal/$1.lean" "$2"
  check "$cache/AspisFormal/$1.lean" "$2"
  check "$cache/.lake/build/lib/lean/AspisFormal/$1.olean" "$3"
}
source_cache V6RelationFold 1d72d79ae170a8791744fe25e66a7dea19e1bd8750d212c21c05c784c85f52f4 24ef5d29a92b3fd142fc7fb3c6c9ce8dc1a824f49beb433ad62adf73a33cf01c
source_cache V6TranscriptRelationGrammar e584b3b6aa73d862326a0ca3bceedff2488bec3fffd394884f2a42c049b3c8e2 f76f8fa9807928637b9aa4af1919026c1b810a94228ec6064c67c52ef23a9b24
source_cache V5FriRelationCandidateBridge 14166cddb9736ea7c737b6d2dd9623f5647e7abecb612685ef6f818ad9e4049d 9a7464778703e38c71c0ca3a555f95ae1963a293288cbd62f7b4af5835b56eaa
source_cache V5RelationSumcheckSoundness cd46d222f4e90dc6a46c3dba15c1b0de96f19d0100770f24f0706c409176a22f c71edc1274b1e9a5b0b6b06f80e411ea30d5734fde797b322bdbe3ba33b853c4
source_cache V5ComponentCRelationRowLinearity 9aed9ae1744ac09c0aed8db332fb501bac7d545f7b401e8b29a131edbbf648e9 04df913e3b693927d2d2e448d0d9ecb4ba59051dabde522c6bc25c9acf174fb4
source_cache V5ComponentCConcreteFoldLinearity bada16fd76a4eebeede8ef6c004db7af753966cd61b244abf2abc73470fbfbad fa7658c4f3cd058cedebe0f696246b9b933532523c60c19b18bf87361bcebc3c
source_cache V5FriConcreteEncoderApplicability 91d8d7a2d8e1ea832459a439482aa858e970cba1608ab7652bdfce3eede632d3 2ed1ef913f2baaeffd2e0ad289e750ba2b1e2c7282d783de8fedb8904464d8d6
check "$ex/JointImageGame.lean" 746b466d3b5c258be8e8670e4cac47771e4dcd9223bc5828f5d803ab72fb8c1d
check "$joint/JointImageGame.olean" 4eda76950026ee3690bb26984f5ae8e59cdf3d87c9ccb8a94439cb4d1be0c780
[[ "$(git -C "$cache/.lake/packages/mathlib" rev-parse HEAD)" == 81a5d257c8e410db227a6665ed08f64fea08e997 ]] || exit 2
check "$cache/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Tactic.olean" 55ee2345729e8a4d379de3bce14ea18b14fbfdc259cf2653fadf4bf3a46876d8
cd "$cache"
{
  git -C "$ex" rev-parse HEAD
  git -C "$cache" rev-parse HEAD
  /Users/dominic/.elan/bin/lake env lean --version
  shasum -a 256 "$ex/OptimizedRelationRefinement.lean" "$joint/JointImageGame.olean"
  /Users/dominic/.elan/bin/lake env bash -c 'export LEAN_PATH="$1:$2:$LEAN_PATH"; /usr/bin/time -l lean -M7000 -R "$1" -o "$1/OptimizedRelationRefinement.olean" "$1/OptimizedRelationRefinement.lean"' _ "$ex" "$joint"
  shasum -a 256 "$ex/OptimizedRelationRefinement.olean"
} 2>&1 | tee "$log"
