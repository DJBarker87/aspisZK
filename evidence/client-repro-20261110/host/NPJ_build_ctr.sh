#!/bin/bash
# NPJ_ attempt 4: path-identical build. A container (host userland bind-mounted read-only)
# sees this workspace at the original NDZ absolute paths; nothing on the host outside
# this workspace is written. No RUSTFLAGS, no wrapper.
set -u
W=/home/dombarker/project-offloads/codex-cx-client-20261110
O=/home/dombarker/project-offloads/codex-cx-devnet-rehearse-20261029
H=/home/dombarker
N=4
cd $W
mkdir -p target-$N cargo-home-$N
IMG=$(docker image inspect alpine:3.22 --format "{{.Id}}")
echo "$IMG" > receipts/NPJ_attempt$N.image
timeout 1800 systemd-run --user --scope --unit=NPJ-client-build$N -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 \
 docker run --rm --name npj-client-build$N --network none --user 1000:1000 \
  --memory=8g --memory-swap=8g --memory-reservation=6g --pids-limit=64 \
  -v /usr:/usr:ro -v /usr/bin:/bin:ro -v /usr/lib:/lib:ro -v /usr/lib64:/lib64:ro -v /usr/sbin:/sbin:ro -v /etc:/etc:ro \
  --tmpfs /tmp:rw,size=2g,exec \
  -v $W/cargo-home-$N:$H/.cargo \
  -v $H/.cargo/bin:$H/.cargo/bin:ro -v $H/.cargo/registry:$H/.cargo/registry:ro -v $H/.cargo/git:$H/.cargo/git:ro \
  -v $H/.rustup:$H/.rustup:ro \
  -v $W/NDZ_src:$O/NDZ_src:ro -v $W/target-$N:$O/NDZ_native-target \
  -v $W/receipts:/receipts \
  -w $O -e HOME=$H -e PATH=$H/.cargo/bin:/usr/bin:/bin -e CARGO_TARGET_DIR=$O/NDZ_native-target \
  "$IMG" /usr/bin/bash -c "rustc -vV > /receipts/NPJ_attempt$N.rustc; cargo -vV > /receipts/NPJ_attempt$N.cargo; env | grep -E \"^(RUST|CARGO)\" | sort > /receipts/NPJ_attempt$N.env; /usr/bin/time -v -o /receipts/NPJ_attempt$N.time $H/.cargo/bin/cargo build --manifest-path NDZ_src/tools/r1-cost-probe/Cargo.toml --release --locked --offline -j \${JOBS:-1} --features r1p-check --bin devnet_spend > /receipts/NPJ_attempt$N.log 2>&1; echo exit=\$? > /receipts/NPJ_attempt$N.exit"
echo "docker_exit=$?" >> receipts/NPJ_attempt$N.exit
sha256sum target-$N/release/devnet_spend >> receipts/NPJ_attempt$N.exit 2>&1
