#!/bin/bash
# usage: check_native.sh LEAN_PATH [DATA_DIR] [NCHUNKS]
#   Runs tools/check_native.lean against a built olean tree: LEAN_PATH lists the olean roots (colon-separated) that hold
#   WormN/, WormCore/ and MoserWorm/; DATA_DIR (optional) is the data directory whose chunks/cNNNNN.txt must equal the
#   txt_cNNNNN literals; NCHUNKS defaults to 4625. Prints the summary; exit status 0 iff ALL CHECKS PASSED.
set -u
here=$(cd "$(dirname "$0")" && pwd)
export LEAN_PATH=$1 WORMN_NCHUNKS=${3:-4625} LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-4}
[ -n "${2:-}" ] && export WORMN_DATA=$2
exec lean "$here/check_native.lean"
