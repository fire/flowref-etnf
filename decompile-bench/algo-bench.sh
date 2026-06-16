#!/usr/bin/env bash
# algo-bench.sh — decompilation faithfulness on our own textbook algorithms.
#
# We wrote decompile-bench/algorithms.c, so we own the ground truth. This
# compiles it, then for each function reports:
#   STRICT : the equivalence oracle's verdict on flowref's faithful-or-refuse
#            lift — EQUIVALENT (proven) / INCOMPARABLE (refused, never wrong).
#   UNSAFE : whether flowref's --unsafe best-effort C at least compiles
#            (syntax-correct C), a coverage signal for the refused class.
set -uo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
FR="${FLOWREF:-$here/../.lake/build/bin/flowref-decompiler}"
CC="${CC:-cc}"
obj="$(mktemp /tmp/algos.XXXXXX.o)"

"$CC" -O1 -fcf-protection=none -fno-stack-protector -c "$here/algorithms.c" -o "$obj" \
  || { echo "cannot compile algorithms.c" >&2; exit 1; }

read TVMA TOFF < <(readelf -SW "$obj" | awk '/[ \t]\.text[ \t]/{for(i=1;i<=NF;i++)if($i=="PROGBITS"){print "0x"$(i+1),"0x"$(i+2);exit}}')

# Every function in algorithms.c (keep in sync with the source).
FUNCS="id32 add2 umax umin abs_diff gray_code avg_floor \
       sum_to_n factorial fib_iter popcount log2_floor reverse_bits \
       gcd isqrt pow_uint is_prime collatz_steps lcm"

total=0; proven=0; unsafe_ok=0; violations=0
printf "%-15s %-14s %s\n" "function" "STRICT" "UNSAFE-compiles"
printf "%-15s %-14s %s\n" "--------" "------" "---------------"
for f in $FUNCS; do
  read SVAL SSIZE < <(readelf -sW "$obj" | awk -v s="$f" '$8==s{print "0x"$2,"0x"$3}')
  [ -n "${SVAL:-}" ] || { printf "%-15s %s\n" "$f" "(symbol not found)"; continue; }
  total=$((total+1))
  FOFF=$(printf "0x%x" $((SVAL - TVMA + TOFF)))

  verdict="$("$here/equiv.sh" "$obj" x64 "$SVAL" "$FOFF" "$SVAL" "$SSIZE" 2>/dev/null | awk '{print $1; exit}')"
  case "$verdict" in
    EQUIVALENT)     proven=$((proven+1));;
    NOT-EQUIVALENT) violations=$((violations+1));;   # SOUNDNESS BUG: strict emitted wrong C
  esac

  if "$FR" decompile "$obj" x64 "$SVAL" "$FOFF" "$SVAL" "$SSIZE" --unsafe 2>/dev/null \
       | "$CC" -xc -std=c11 -w -fsyntax-only - 2>/dev/null; then uc="yes"; unsafe_ok=$((unsafe_ok+1)); else uc="no"; fi

  printf "%-15s %-14s %s\n" "$f" "${verdict:-?}" "$uc"
done
rm -f "$obj"
echo
echo "STRICT  : $proven/$total proven EQUIVALENT (machine-checked)"
echo "UNSAFE  : $unsafe_ok/$total emit C that compiles (best-effort coverage signal)"
if [ "$violations" -gt 0 ]; then
  echo "SOUNDNESS: $violations/$total strict lifts were NOT-EQUIVALENT — flowref emitted"
  echo "           wrong C while claiming 'faithful'. This must be 0; the faithfulness"
  echo "           gate must REFUSE instructions it cannot model (e.g. cmov/setcc)."
  exit 1
fi
echo "SOUNDNESS: 0 violations (no strict lift was wrong)."
