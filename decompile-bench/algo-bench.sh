#!/usr/bin/env bash
# algo-bench.sh — decompilation faithfulness on our own textbook algorithms.
#
# We wrote decompile-bench/algorithms/*.c (one function per file), so we own the
# ground truth. For each file this compiles it to its own object, then reports:
#   STRICT : the equivalence oracle's verdict on flowref's faithful-or-refuse
#            lift — EQUIVALENT (proven) / INCOMPARABLE (refused, never wrong).
#   UNSAFE : whether flowref's --unsafe best-effort C at least compiles
#            (syntax-correct C), a coverage signal for the refused class.
set -uo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
FR="${FLOWREF:-$here/../.lake/build/bin/flowref-decompiler}"
CC="${CC:-cc}"
SRCDIR="$here/algorithms"

# Order mirrors the structural grouping of the source set: leaves, bit tricks /
# multi-cmov, counted loops, data-dependent loops, then a call. Keep in sync with
# the files in algorithms/ (each file defines exactly the function it is named).
FUNCS="id32 add2 umax umin abs_diff gray_code avg_floor \
       isolate_lowest_bit clear_lowest_bit clamp max3 min3 sat_add sat_sub diff_or_zero \
       parity bit_merge mul5 lin2 combine4 pack16 \
       sum_to_n factorial fib_iter popcount log2_floor reverse_bits ctz digit_count \
       gcd isqrt pow_uint is_prime collatz_steps lcm"

total=0; proven=0; unsafe_ok=0; violations=0
printf "%-15s %-14s %s\n" "function" "STRICT" "UNSAFE-compiles"
printf "%-15s %-14s %s\n" "--------" "------" "---------------"
for f in $FUNCS; do
  src="$SRCDIR/$f.c"
  [ -f "$src" ] || { printf "%-15s %s\n" "$f" "(source not found)"; continue; }
  obj="$(mktemp /tmp/algo.$f.XXXXXX.o)"
  if ! "$CC" -O1 -fcf-protection=none -fno-stack-protector -c "$src" -o "$obj" 2>/dev/null; then
    printf "%-15s %s\n" "$f" "(cannot compile)"; rm -f "$obj"; continue
  fi

  # .text section file offset (sh_offset), from section headers — metadata only.
  read TVMA TOFF < <(readelf -SW "$obj" | awk '/[ \t]\.text[ \t]/{for(i=1;i<=NF;i++)if($i=="PROGBITS"){print "0x"$(i+1),"0x"$(i+2);exit}}')
  # readelf -s prints Value in hex but Size in DECIMAL; convert the size to hex.
  read SVAL SZDEC < <(readelf -sW "$obj" | awk -v s="$f" '$8==s{print "0x"$2, $3}')
  [ -n "${SVAL:-}" ] || { printf "%-15s %s\n" "$f" "(symbol not found)"; rm -f "$obj"; continue; }
  SSIZE=$(printf "0x%x" "$SZDEC")
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
  rm -f "$obj"
done
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
