#!/bin/bash
# PCXT_: NPJ_ attempt 4 recipe, source from git archive d7142292c48, own workspace path.
set -u
W=/home/dombarker/project-offloads/codex-pc-pin2-client-20261111
H=/home/dombarker
N=${ATTEMPT:-1}
cd $W
mkdir -p target-$N cargo-home-$N receipts
IMG=$(docker image inspect alpine:3.22 --format "{{.Id}}")
echo "$IMG" > receipts/PCXT_attempt$N.image
cat > receipts/PCXT_attempt$N.admission.json <<J
{"scopes_whole_host_lean_extraction":0,"stream_c_scopes":0,"disk_free_gb_ge_45":true,"reservation_gib":8,"allowed":true,"note":"checked by hand before launch; 1 scope"}
J
timeout 1800 systemd-run --user --scope --unit=PCXT-client-build$N -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 \
 docker run --rm --name pcxt-client-build$N --network none --user 1000:1000 \
  --memory=8g --memory-swap=8g --memory-reservation=6g --pids-limit=64 \
  -v /usr:/usr:ro -v /usr/bin:/bin:ro -v /usr/lib:/lib:ro -v /usr/lib64:/lib64:ro -v /usr/sbin:/sbin:ro -v /etc:/etc:ro \
  --tmpfs /tmp:rw,size=2g,exec \
  -v $W/cargo-home-$N:$H/.cargo \
  -v $H/.cargo/bin:$H/.cargo/bin:ro -v $H/.cargo/registry:$H/.cargo/registry:ro -v $H/.cargo/git:$H/.cargo/git:ro \
  -v $H/.rustup:$H/.rustup:ro \
  -v $W/src:$W/src:ro -v $W/target-$N:$W/target-$N \
  -v $W/receipts:/receipts \
  -w $W -e HOME=$H -e PATH=$H/.cargo/bin:/usr/bin:/bin -e CARGO_TARGET_DIR=$W/target-$N \
  "$IMG" /usr/bin/bash -c "rustc -vV > /receipts/PCXT_attempt$N.rustc; cargo -vV > /receipts/PCXT_attempt$N.cargo; env | grep -E \"^(RUST|CARGO)\" | sort > /receipts/PCXT_attempt$N.env; /usr/bin/time -v -o /receipts/PCXT_attempt$N.time $H/.cargo/bin/cargo build --manifest-path $W/src/tools/r1-cost-probe/Cargo.toml --release --locked --offline -j \${JOBS:-1} --features r1p-check --bin devnet_spend --bin pv_client_gate > /receipts/PCXT_attempt$N.log 2>&1; echo exit=\$? > /receipts/PCXT_attempt$N.exit"
echo "docker_exit=$?" >> receipts/PCXT_attempt$N.exit
sha256sum target-$N/release/devnet_spend target-$N/release/pv_client_gate >> receipts/PCXT_attempt$N.exit 2>&1
