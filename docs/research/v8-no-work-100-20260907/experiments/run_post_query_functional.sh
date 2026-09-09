#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)"
readonly cache=/Users/dominic/ZK/AspisFormal joint=/tmp/aspis-v8-joint-cache.n3hmg5
[[ $# == 2 && ! -e "$2" ]] || exit 2
case "$1" in
  interface) target=ImageCallbackInterfaces ;;
  leaf) target=PostQueryFunctional ;;
  *) exit 2 ;;
esac
readonly target log="$(cd "$(dirname "$2")" && pwd)/$(basename "$2")"
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
source_cache V7ExactOneFoldDomains 60eb390e89f9ad82537b784a7c328a8fa1ab76e328dd7b5c836c8d587cf42d98 a6ceb7039b7eb00e4d9315518ea84ed2081dc9cc437bc9f2164ed9d50a184443
source_cache V5FriInitialCircleEncoderIdentity 2bde5263fbfae6730288883515b1689a1856ace2b428a73d6a985f256b608084 b7ba0d31ffe194bf949adfbe4f3ead6d2541e2dc49063c64408e4ae48244c226
source_cache V5FriConcreteEncoderCommutation 1d91ec87e0276c06e2fa4a4cc69f8e32f2cdb9c010f5b3928a61701271623f03 4f9abb1d140d1688584342e48d204426fd446e766f6308976bc6b421a4ab97bb
source_cache V6EncoderDistance 36ee79a60cb5e7909beb4da3ebba1af63fd9a2ad35dcdd1ff74f516aa153e196 2fe4cfa0bc44213b3f50ab2f911a526cd85cbaaeb4fb330517358082a9be4324
check "$ex/JointImageGame.lean" 746b466d3b5c258be8e8670e4cac47771e4dcd9223bc5828f5d803ab72fb8c1d
check "$joint/JointImageGame.olean" 4eda76950026ee3690bb26984f5ae8e59cdf3d87c9ccb8a94439cb4d1be0c780
check "$ex/OptimizedRelationRefinement.lean" 98b861e3d8a4d06d2a9ffc01bb394314353dc3dbbf55efeaa4f7390d8d8e8304
check "$ex/OptimizedRelationRefinement.olean" 4aaf5ff39ddecd665d0593d57f8459c629a7cb3ee7c873798af80aac4cd4941d
check "$ex/ImageCallbackInterfaces.lean" 5d6d1f5be0a0351c1288c975355f944a9ea447d90c8c40d0b57898138ec6cdd8
if [[ "$target" == PostQueryFunctional ]]; then
  check "$ex/ImageCallbackInterfaces.olean" 33b837a6e80e0697281a0195ea87dc5419852b91653523503e228cd79d2535b5
fi
[[ "$(git -C "$cache/.lake/packages/mathlib" rev-parse HEAD)" == 81a5d257c8e410db227a6665ed08f64fea08e997 ]] || exit 2
check "$cache/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Tactic.olean" 55ee2345729e8a4d379de3bce14ea18b14fbfdc259cf2653fadf4bf3a46876d8
cd "$cache"
{
  git -C "$ex" rev-parse HEAD
  git -C "$cache" rev-parse HEAD
  /Users/dominic/.elan/bin/lake env lean --version
  shasum -a 256 "$ex/$target.lean" "$joint/JointImageGame.olean"
  if [[ "$target" == PostQueryFunctional ]]; then shasum -a 256 "$ex/ImageCallbackInterfaces.olean"; fi
  /Users/dominic/.elan/bin/lake env bash -c 'export LEAN_PATH="$1:$2:$LEAN_PATH"; /usr/bin/time -l lean -M7000 -R "$1" -o "$1/$3.olean" "$1/$3.lean"' _ "$ex" "$joint" "$target"
  shasum -a 256 "$ex/$target.olean"
} 2>&1 | tee "$log"
