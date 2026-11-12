#!/bin/bash
# X1: the privacy lead's Box control case with this tool pair, in a scratch workspace under W/x1/probe/boxcase.
# Root form: Charon on boxlib itself (--mir built). Dependency form: Charon on boxroot with boxlib included (boxlib
# read from optimized MIR). Same Charon flags as the X1 emission; Aeneas with -abort-on-error. Runs INSIDE fv_slot.sh.
set -u
W=/home/dombarker/project-offloads/future-version-20261111; X=$W/x1/probe/boxcase
BIN=/home/dombarker/project-offloads/codex-pc-prov-p4x-20261110/PCWH_T004_out/bin
rm -rf $X; mkdir -p $X/boxlib/src $X/boxroot/src
cat > $X/Cargo.toml <<T
[workspace]
members = ["boxlib", "boxroot"]
resolver = "2"
T
cat > $X/boxlib/Cargo.toml <<T
[package]
name = "boxlib"
version = "0.1.0"
edition = "2021"
T
cat > $X/boxroot/Cargo.toml <<T
[package]
name = "boxroot"
version = "0.1.0"
edition = "2021"
[dependencies]
boxlib = { path = "../boxlib" }
T
cat > $X/boxlib/src/lib.rs <<'T'
pub struct S { pub x: u64, pub y: u64 }
pub fn n_set(b: &mut Box<S>, v: u64) { b.x = v }
pub fn n_set_slice(b: &mut Box<[u64]>, v: u64) { b[0] = v }
pub fn n_set_array(b: &mut Box<[u64; 4]>, v: u64) { b[1] = v }
T
cat > $X/boxroot/src/lib.rs <<'T'
pub fn root_set(b: &mut Box<boxlib::S>, v: u64) { boxlib::n_set(b, v) }
pub fn root_set_slice(b: &mut Box<[u64]>, v: u64) { boxlib::n_set_slice(b, v) }
pub fn root_set_array(b: &mut Box<[u64; 4]>, v: u64) { boxlib::n_set_array(b, v) }
T
export PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin RUSTUP_TOOLCHAIN=nightly-2026-09-17 CARGO_NET_OFFLINE=true RUSTFLAGS='-Zthreads=1 -C link-arg=-Wl,--threads=1' CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=false
for form in root dep; do
  if [ $form = root ]; then M=$X/boxlib/Cargo.toml; S="--start-from crate::n_set --start-from crate::n_set_slice --start-from crate::n_set_array"; I=""
  else M=$X/boxroot/Cargo.toml; S="--start-from crate::root_set --start-from crate::root_set_slice --start-from crate::root_set_array"; I="--include boxlib"; fi
  mkdir -p $X/$form
  ( cd $X && CARGO_TARGET_DIR=$X/target-$form $BIN/charon cargo --preset aeneas --mir built --sysroot default $S $I --dest-file $X/$form/out.llbc -- --manifest-path $M --offline --release --lib ) > $X/$form/charon.log 2>&1
  echo "$form charon $?"
  ( cd $X/$form && $BIN/aeneas -diagnose-translation -sequential -no-progress-bar -abort-on-error -backend lean -namespace Box_$form -dest $X/$form/raw -subdir Box_$form -split-files $X/$form/out.llbc ) > $X/$form/aeneas.log 2>&1
  echo "$form aeneas $?"
  sed -n '/n_set/,/^$/p' $X/$form/raw/Box_$form/Funs.lean
done
