#!/usr/bin/env bash
# Apply only the pinned research patch chain to an existing task-owned COPY.
# Does not provision a host, fetch dependencies, reset a tree or deploy.
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)" rt="$(cd "$(dirname "$0")/../../../.." && pwd)"
[[ "$rt" == /home/dombarker/project-offloads/aspis-v8-* && ! -e "$rt/.git" ]] || exit 2
cd "$rt"
hash(){ sha256sum "$1" | cut -d' ' -f1; }
readonly original_field=5795495e2fa9ad85e097c2ad96ffc826aaad3c16afc0e0bd00459f9f51068cd8
readonly range_field=8f8b3aad6193ba5ee0b160a61994b19b5f154009ff250d704203c713bf38778c
readonly final_field=4233620fc2640a7fee834adacedfbf22e085efa6e314a550d2b39c361f15b13f
if [[ "$(hash crates/aspis-core/src/field.rs)" == "$original_field" ]];then
 for p in canonical-m31 canonical-cm31 canonical-dots canonical-cm-schoolbook canonical-branchless canonical-prepared;do
  git apply --check "$ex/$p.patch";git apply "$ex/$p.patch"
 done
fi
if [[ "$(hash crates/aspis-core/src/field.rs)" == "$range_field" ]];then
 for p in qm-hybrid qm-lazy-c0;do
  git apply --check --unidiff-zero "$ex/$p.patch";git apply --unidiff-zero "$ex/$p.patch"
 done
fi
[[ "$(hash crates/aspis-core/src/field.rs)" == "$final_field" ]] || { echo 'Unexpected field source; inspect without resetting.' >&2;exit 2; }
readonly files=(programs/aspis-verifier/src/lib.rs programs/aspis-verifier/src/v7_pair_forest_dispatch.rs crates/aspis-statement/src/pool_v1/tag73_pair_forest_profile.rs results/v7-pair-forest-combined-rejection-litesvm-20260828/harness/src/main.rs)
readonly original=(06bd276c29812aab0f30311fce275d1121a229c5192ef35f3f04e2cd7379903c 4577c435a5c41a147331ca7d42b65053e181d58dca1b4322ef96b48c85babf77 1f3f06d55e891dfcdfb5777380762d7595c109559b12f164d96001c6ddb2d7c5 13c39245aba6392ea4059848c3912c77a1330fce01579d828215451689749060)
readonly patched=(3905ac298f9f74602b6f8601e35d40dae30ae1aaa7592961253a167ac5117409 50ffb4598fca897e79bc7fca1fb4c1742c0ec15327032d117477e9a93150c4da 4f3476a2798a6093cbbecdad616ebc41cb8e003b1cadcd4a9b90c89af809f7fc 251aba0b81db74a2c6916c1a522d8a4e3fa63c422fa4797ada53d4132c0398f1)
all_original=1
for i in 0 1 2 3;do [[ "$(hash "${files[i]}")" == "${original[i]}" ]] || all_original=0;done
if [[ "$all_original" == 1 ]];then
 for p in complete-integration complete-matched-driver;do
  git apply --check --unidiff-zero "$ex/$p.patch";git apply --unidiff-zero "$ex/$p.patch"
 done
fi
for i in 0 1 2 3;do
 [[ "$(hash "${files[i]}")" == "${patched[i]}" ]] || { echo "Unexpected source: ${files[i]}; inspect without resetting." >&2;exit 2; }
done
sha256sum crates/aspis-core/src/field.rs "${files[@]}"
