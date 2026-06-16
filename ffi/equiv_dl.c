/* flowref equivalence FFI — the BINARY is the reference.

   No source compilation is needed: the reference behaviour is the real compiled
   function in the dataset binary. We map its raw bytes into executable memory and
   call them directly; the candidate is flowref's lifted C (compiled into a shared
   object). The Lean `equiv-check` exe then drives a plausible counterexample
   search comparing the two over many argument vectors.

   This is only ever applied to flowref's FAITHFUL class — a straight-line,
   register-only leaf (no calls, no memory, no relocations) — so the raw bytes are
   position-independent and self-contained, hence safe to relocate and execute.

   Both are called through the SysV integer-arg registers (six uint32 args; a
   lower-arity function ignores the extra registers). */

#include <lean/lean.h>
#include <dlfcn.h>
#include <string.h>
#include <stdint.h>
#include <sys/mman.h>

typedef uint32_t (*fn6)(uint32_t, uint32_t, uint32_t, uint32_t, uint32_t, uint32_t);
static fn6 g_ref = 0, g_cand = 0;

/* Reference = the binary's own function bytes, mapped executable and called in
   place. Returns 1 on success. */
LEAN_EXPORT uint8_t lean_equiv_load_ref(b_lean_obj_arg bytes) {
  size_t n = lean_sarray_size(bytes);
  if (n == 0) return 0;
  const uint8_t *p = (const uint8_t *)lean_sarray_cptr(bytes);
  void *m = mmap(0, n, PROT_READ | PROT_WRITE | PROT_EXEC,
                 MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  if (m == MAP_FAILED) return 0;
  memcpy(m, p, n);
  __builtin___clear_cache((char *)m, (char *)m + n);
  g_ref = (fn6)m;
  return 1;
}

/* Candidate = flowref's lifted C, compiled to a shared object exporting
   `flowref_cand`. Returns 1 on success. */
LEAN_EXPORT uint8_t lean_equiv_load_cand(b_lean_obj_arg path_obj) {
  void *h = dlopen(lean_string_cstr(path_obj), RTLD_NOW | RTLD_LOCAL);
  if (!h) return 0;
  g_cand = (fn6)dlsym(h, "flowref_cand");
  return g_cand ? 1 : 0;
}

LEAN_EXPORT uint32_t lean_equiv_ref(uint32_t a, uint32_t b, uint32_t c,
                                    uint32_t d, uint32_t e, uint32_t f) {
  return g_ref ? g_ref(a, b, c, d, e, f) : 0;
}
LEAN_EXPORT uint32_t lean_equiv_cand(uint32_t a, uint32_t b, uint32_t c,
                                     uint32_t d, uint32_t e, uint32_t f) {
  return g_cand ? g_cand(a, b, c, d, e, f) : 0;
}
