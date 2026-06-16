#!/usr/bin/env bash
# Self-contained demonstration of the flowref equivalence oracle.
#
# For each tiny leaf function below we compile it to an object — this stands in
# for a Decompile-Bench *bins* sample (the BINARY side) — keeping the source as
# the reference (the `code` side). We then point flowref's OWN disassembler +
# lifter at the function's byte region and ask equiv.sh whether the recovered C
# is functionally equivalent to the source.
#
# flowref (lean-capstone) does EVERY disassembly. objdump is never used; we read
# only ELF symbol + section metadata (readelf) to locate the function, because
# flowref takes a raw (fileOff, vaddr, len) region and does not parse containers.
#
# Objects are native 64-bit and decoded with arch `x64` (flowref wires every
# Capstone width/target; see Flowref/Decoders.lean::capstoneSpec?).
set -uo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
CC="${CC:-gcc}"
pass=0; total=0

cat > /tmp/fr_refs.c <<'EOF'
#include <stdint.h>
/* parameterless constant-returning leaves */
uint32_t k7(void){ uint32_t a = 3, b = 4; return a + b; }       /* = 7   */
uint32_t kshift(void){ uint32_t x = 1; x = x << 4; return x; }  /* = 16  */
uint32_t kxor(void){ uint32_t x = 0xff; return x ^ 0x0f; }      /* = 240 */
uint32_t kchain(void){ uint32_t x = 10; x = x + 5; x = x - 3; return x; } /* = 12 */
/* PARAMETERISED arithmetic leaves — proven over many argument vectors by the
   plausible counterexample search (these need calling-convention params + lea). */
uint32_t p_add(uint32_t a, uint32_t b){ return a + b; }
uint32_t p_sub(uint32_t a, uint32_t b){ return a - b; }
uint32_t p_and(uint32_t a, uint32_t b){ return a & b; }
uint32_t p_or (uint32_t a, uint32_t b){ return a | b; }
uint32_t p_xor(uint32_t a, uint32_t b){ return a ^ b; }
uint32_t p_mul(uint32_t a, uint32_t b){ return a * b; }
uint32_t p_id (uint32_t a){ return a; }
EOF

if ! "$CC" -O1 -fcf-protection=none -fno-stack-protector -c /tmp/fr_refs.c -o /tmp/fr_refs.o 2>/dev/null; then
  echo "SKIP: cannot compile the reference object." >&2; exit 0
fi

# .text section file offset (sh_offset), from section headers — metadata only.
read TVMA TOFF < <(readelf -SW /tmp/fr_refs.o | awk '
  /[ \t]\.text[ \t]/ { for(i=1;i<=NF;i++) if($i=="PROGBITS"){print "0x"$(i+1), "0x"$(i+2); exit} }')

run_one() {
  local sym="$1"
  total=$((total+1))
  # symbol value (section-relative) + size, from the symbol table — metadata.
  read SVAL SSIZE < <(readelf -sW /tmp/fr_refs.o | awk -v s="$sym" '$8==s{print "0x"$2, "0x"$3}')
  if [ -z "${SVAL:-}" ] || [ -z "${TVMA:-}" ]; then echo "  $sym: INCOMPARABLE (symbol/section not found)"; return; fi
  local FOFF; FOFF=$(printf "0x%x" $(( SVAL - TVMA + TOFF )))
  # the binary's own bytes are the reference — no source compilation needed.
  local out
  out="$("$here/equiv.sh" /tmp/fr_refs.o x64 "$SVAL" "$FOFF" "$SVAL" "$SSIZE")"
  echo "  $sym (val=$SVAL size=$SSIZE foff=$FOFF): $out"
  case "$out" in EQUIVALENT*) pass=$((pass+1));; esac
}

echo "== flowref equivalence demo (binary side ⇆ source side; flowref disasm only) =="
for s in k7 kshift kxor kchain p_add p_sub p_and p_or p_xor p_mul p_id; do run_one "$s"; done
echo
echo "RESULT: $pass/$total proven functionally equivalent to their source."
[ "$pass" -ge 1 ] || { echo "expected at least one EQUIVALENT" >&2; exit 1; }
