#!/bin/bash
# Runs INSIDE a scope. Usage: fv_replay.sh <adapter-elf-attempt> <transfer|withdrawal>
set -u
W=/home/dombarker/project-offloads/future-version-20261111
E=$1; OP=$2
mkdir -p $W/replays
ASPIS_SOURCE_REVISION=$(cat $W/SOURCE_REVISION) $W/target/native/release/one_tx_replay $W/devnet/PIN2_TRANSACTIONS.json $W/devnet/pool.so $W/devnet/verifier-pin2.so \
  $W/out/$E/artifacts/aspis_r1_cost_probe_program.so $OP $W/replays/$E-$OP.json
