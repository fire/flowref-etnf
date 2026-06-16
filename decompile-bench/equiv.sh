#!/usr/bin/env bash
# flowref ⇆ Decompile-Bench equivalence oracle.
#
# The oracle is now LIFTED INTO LEAN: `flowref-equiv` (EquivCheck.lean) lifts the
# binary region with flowref, compiles the (reference, candidate) pair, and runs
# a PLAUSIBLE counterexample search over their inputs — `∀ args, ref == cand` —
# iteratively deepened. A counterexample is the disproof (NOT-EQUIVALENT); its
# absence after the deepest level is the equivalence witness (EQUIVALENT). Inputs
# flowref cannot lift faithfully are INCOMPARABLE — never a false EQUIVALENT.
#
# The BINARY is the reference: no source needed. Thin wrapper, CLI:
#   equiv.sh <binary> <arch> <fnVaddrHex> <fileOffHex> <vaddrHex> <lenHex>
set -uo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
export FLOWREF="${FLOWREF:-$here/../.lake/build/bin/flowref}"
EQUIV="${FLOWREF_EQUIV:-$here/../.lake/build/bin/flowref-equiv}"

[ $# -eq 6 ] || { echo "usage: equiv.sh <binary> <arch> <fnVaddrHex> <fileOffHex> <vaddrHex> <lenHex>" >&2; exit 2; }
[ -x "$EQUIV" ] || { echo "INCOMPARABLE  (flowref-equiv not built — run 'lake build flowref-equiv')"; exit 3; }

# A hard wall-clock cap so a pathological case can never hang the harness.
exec timeout "${FLOWREF_EQUIV_TIMEOUT:-60}" "$EQUIV" "$@"
