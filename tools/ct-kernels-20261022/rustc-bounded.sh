#!/bin/sh
# SBF Cargo suppresses RUSTFLAGS for host build scripts; bound their lld too.
case " $* " in
  *" --target sbpf-solana-solana "*|*" --target sbf-solana-solana "*) exec "$@" ;;
  *) exec "$@" -C link-arg=-Wl,--threads=4 ;;
esac
