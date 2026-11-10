#!/bin/bash
# usage: bash pc_log.sh ATTEMPT [bytes] : show decompressed stdout log tail
cd "$(dirname "$0")"; xz -dc "$1/stdout.log.xz" 2>/dev/null || cat "$1/stdout.log"
