/* flowref FFI shim — self-contained ELF parser (no external library).

   Exposes one primitive to Lean: `lean_elf_dump`, which reads an ELF file and
   returns a newline-separated, TAB-delimited dump that the Lean side parses.

   Deliberately depends on NOTHING but libc + the standard `<elf.h>` struct
   definitions: no libelf/gelf, so there is no library to link, no pkg-config
   discovery, no CI package, and no runtime `.so`. Parsing is done directly over
   the file bytes using the canonical ELF structs, handling ELFCLASS32/64 and
   both byte orders (byte-swapping when the file's endianness differs from the
   host's). This mirrors the lean-capstone FFI pattern (one C primitive, TSV
   transport, typed wrapper on the Lean side).

   Transport grammar (one record per line, fields TAB-separated):
     H <machine> <is64:0|1> <littleEndian:0|1> <entryHex>
     S <name> <addrHex> <offsetHex> <sizeHex>            (one per section)
     F <name> <valueHex> <sizeHex>                       (one per FUNC symbol)

   `machine` is the raw `e_machine` (EM_*) so the Lean side owns the arch-token
   mapping. Empty string on any open/parse error (Lean treats that as "not an
   ELF / unreadable"). The file buffer is allocated with a trailing NUL sentinel
   so string-table names are always terminated; all header/symbol accesses are
   bounds-checked against the file size (untrusted-input safe). */

#include <lean/lean.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <elf.h>

/* A tiny growable char buffer (same shape as the capstone shim's accumulator). */
typedef struct { char *p; size_t len, cap; } buf_t;

static void buf_init(buf_t *b) { b->cap = 8192; b->len = 0; b->p = (char *)malloc(b->cap); b->p[0] = '\0'; }
static void buf_add(buf_t *b, const char *s) {
  size_t m = strlen(s);
  if (b->len + m + 1 > b->cap) { while (b->len + m + 1 > b->cap) b->cap *= 2; b->p = (char *)realloc(b->p, b->cap); }
  memcpy(b->p + b->len, s, m);
  b->len += m;
  b->p[b->len] = '\0';
}

/* Byte-swap helpers, active only when the file's endianness differs from the
   host's (set in g_swap). ELF on a same-endian host reads through directly. */
static int g_swap;
static uint16_t rd16(uint16_t v) { return g_swap ? __builtin_bswap16(v) : v; }
static uint32_t rd32(uint32_t v) { return g_swap ? __builtin_bswap32(v) : v; }
static uint64_t rd64(uint64_t v) { return g_swap ? __builtin_bswap64(v) : v; }

static int host_is_le(void) { const uint16_t one = 1; return *(const uint8_t *)&one; }

/* Is the byte range [off, off+n) fully inside a buffer of `sz` bytes? */
static int in_range(size_t sz, size_t off, size_t n) { return off <= sz && n <= sz - off; }

static lean_obj_res empty_with(buf_t *b, uint8_t *d, FILE *f) {
  if (f) fclose(f);
  free(d);
  free(b->p);
  return lean_mk_string("");
}

LEAN_EXPORT lean_obj_res lean_elf_dump(b_lean_obj_arg path_obj) {
  const char *path = lean_string_cstr(path_obj);
  buf_t b; buf_init(&b);

  FILE *f = fopen(path, "rb");
  if (!f) return empty_with(&b, NULL, NULL);
  if (fseek(f, 0, SEEK_END) != 0) return empty_with(&b, NULL, f);
  long fl = ftell(f);
  if (fl < (long)sizeof(Elf32_Ehdr)) return empty_with(&b, NULL, f);
  rewind(f);

  size_t sz = (size_t)fl;
  uint8_t *d = (uint8_t *)malloc(sz + 1);          /* +1 for a NUL sentinel */
  if (!d) return empty_with(&b, NULL, f);
  if (fread(d, 1, sz, f) != sz) return empty_with(&b, d, f);
  fclose(f); f = NULL;
  d[sz] = '\0';                                    /* terminates any name string */

  if (sz < EI_NIDENT ||
      d[EI_MAG0] != ELFMAG0 || d[EI_MAG1] != ELFMAG1 ||
      d[EI_MAG2] != ELFMAG2 || d[EI_MAG3] != ELFMAG3)
    return empty_with(&b, d, NULL);

  int cls = d[EI_CLASS];
  int file_le = (d[EI_DATA] == ELFDATA2LSB);
  g_swap = (file_le != host_is_le());

  char line[1024];

  if (cls == ELFCLASS64) {
    Elf64_Ehdr eh;
    if (!in_range(sz, 0, sizeof eh)) return empty_with(&b, d, NULL);
    memcpy(&eh, d, sizeof eh);
    uint16_t machine = rd16(eh.e_machine);
    uint64_t entry   = rd64(eh.e_entry);
    uint64_t shoff   = rd64(eh.e_shoff);
    uint16_t shent   = rd16(eh.e_shentsize);
    uint16_t shnum   = rd16(eh.e_shnum);
    uint16_t shstrndx = rd16(eh.e_shstrndx);

    snprintf(line, sizeof line, "H\t%u\t1\t%d\t%llx\n",
             (unsigned)machine, file_le ? 1 : 0, (unsigned long long)entry);
    buf_add(&b, line);

    if (shent < sizeof(Elf64_Shdr)) return empty_with(&b, d, NULL); /* malformed */

    /* string table for section names */
    uint64_t shstr_off = 0;
    if (shstrndx < shnum) {
      size_t so = (size_t)shoff + (size_t)shstrndx * shent;
      Elf64_Shdr sh;
      if (in_range(sz, so, sizeof sh)) { memcpy(&sh, d + so, sizeof sh); shstr_off = rd64(sh.sh_offset); }
    }

    for (uint16_t k = 0; k < shnum; k++) {
      size_t so = (size_t)shoff + (size_t)k * shent;
      Elf64_Shdr sh;
      if (!in_range(sz, so, sizeof sh)) continue;
      memcpy(&sh, d + so, sizeof sh);
      uint32_t nameoff = rd32(sh.sh_name);
      uint32_t type    = rd32(sh.sh_type);
      uint64_t addr    = rd64(sh.sh_addr);
      uint64_t offv    = rd64(sh.sh_offset);
      uint64_t size    = rd64(sh.sh_size);
      const char *snm = (shstr_off && (size_t)shstr_off + nameoff < sz)
                        ? (const char *)(d + shstr_off + nameoff) : "";
      snprintf(line, sizeof line, "S\t%s\t%llx\t%llx\t%llx\n",
               snm, (unsigned long long)addr, (unsigned long long)offv, (unsigned long long)size);
      buf_add(&b, line);

      if (type == SHT_SYMTAB || type == SHT_DYNSYM) {
        uint64_t entsize = rd64(sh.sh_entsize);
        uint32_t link    = rd32(sh.sh_link);
        if (entsize < sizeof(Elf64_Sym)) continue;
        uint64_t str_off = 0;
        if (link < shnum) {
          size_t lso = (size_t)shoff + (size_t)link * shent;
          Elf64_Shdr ls;
          if (in_range(sz, lso, sizeof ls)) { memcpy(&ls, d + lso, sizeof ls); str_off = rd64(ls.sh_offset); }
        }
        uint64_t n = size / entsize;
        for (uint64_t i = 0; i < n; i++) {
          size_t syo = (size_t)offv + (size_t)i * entsize;
          Elf64_Sym sym;
          if (!in_range(sz, syo, sizeof sym)) break;
          memcpy(&sym, d + syo, sizeof sym);
          if ((sym.st_info & 0xf) != STT_FUNC) continue;       /* ELF64_ST_TYPE */
          uint64_t val = rd64(sym.st_value);
          if (val == 0) continue;
          uint64_t ssize = rd64(sym.st_size);
          uint32_t no = rd32(sym.st_name);
          const char *fnm = (str_off && (size_t)str_off + no < sz)
                            ? (const char *)(d + str_off + no) : "";
          if (fnm[0] == '\0') continue;
          snprintf(line, sizeof line, "F\t%s\t%llx\t%llx\n",
                   fnm, (unsigned long long)val, (unsigned long long)ssize);
          buf_add(&b, line);
        }
      }
    }
  } else if (cls == ELFCLASS32) {
    Elf32_Ehdr eh;
    if (!in_range(sz, 0, sizeof eh)) return empty_with(&b, d, NULL);
    memcpy(&eh, d, sizeof eh);
    uint16_t machine = rd16(eh.e_machine);
    uint32_t entry   = rd32(eh.e_entry);
    uint32_t shoff   = rd32(eh.e_shoff);
    uint16_t shent   = rd16(eh.e_shentsize);
    uint16_t shnum   = rd16(eh.e_shnum);
    uint16_t shstrndx = rd16(eh.e_shstrndx);

    snprintf(line, sizeof line, "H\t%u\t0\t%d\t%llx\n",
             (unsigned)machine, file_le ? 1 : 0, (unsigned long long)entry);
    buf_add(&b, line);

    if (shent < sizeof(Elf32_Shdr)) return empty_with(&b, d, NULL);

    uint32_t shstr_off = 0;
    if (shstrndx < shnum) {
      size_t so = (size_t)shoff + (size_t)shstrndx * shent;
      Elf32_Shdr sh;
      if (in_range(sz, so, sizeof sh)) { memcpy(&sh, d + so, sizeof sh); shstr_off = rd32(sh.sh_offset); }
    }

    for (uint16_t k = 0; k < shnum; k++) {
      size_t so = (size_t)shoff + (size_t)k * shent;
      Elf32_Shdr sh;
      if (!in_range(sz, so, sizeof sh)) continue;
      memcpy(&sh, d + so, sizeof sh);
      uint32_t nameoff = rd32(sh.sh_name);
      uint32_t type    = rd32(sh.sh_type);
      uint32_t addr    = rd32(sh.sh_addr);
      uint32_t offv    = rd32(sh.sh_offset);
      uint32_t size    = rd32(sh.sh_size);
      const char *snm = (shstr_off && (size_t)shstr_off + nameoff < sz)
                        ? (const char *)(d + shstr_off + nameoff) : "";
      snprintf(line, sizeof line, "S\t%s\t%llx\t%llx\t%llx\n",
               snm, (unsigned long long)addr, (unsigned long long)offv, (unsigned long long)size);
      buf_add(&b, line);

      if (type == SHT_SYMTAB || type == SHT_DYNSYM) {
        uint32_t entsize = rd32(sh.sh_entsize);
        uint32_t link    = rd32(sh.sh_link);
        if (entsize < sizeof(Elf32_Sym)) continue;
        uint32_t str_off = 0;
        if (link < shnum) {
          size_t lso = (size_t)shoff + (size_t)link * shent;
          Elf32_Shdr ls;
          if (in_range(sz, lso, sizeof ls)) { memcpy(&ls, d + lso, sizeof ls); str_off = rd32(ls.sh_offset); }
        }
        uint32_t n = size / entsize;
        for (uint32_t i = 0; i < n; i++) {
          size_t syo = (size_t)offv + (size_t)i * entsize;
          Elf32_Sym sym;
          if (!in_range(sz, syo, sizeof sym)) break;
          memcpy(&sym, d + syo, sizeof sym);
          if ((sym.st_info & 0xf) != STT_FUNC) continue;       /* ELF32_ST_TYPE */
          uint32_t val = rd32(sym.st_value);
          if (val == 0) continue;
          uint32_t ssize = rd32(sym.st_size);
          uint32_t no = rd32(sym.st_name);
          const char *fnm = (str_off && (size_t)str_off + no < sz)
                            ? (const char *)(d + str_off + no) : "";
          if (fnm[0] == '\0') continue;
          snprintf(line, sizeof line, "F\t%s\t%llx\t%llx\n",
                   fnm, (unsigned long long)val, (unsigned long long)ssize);
          buf_add(&b, line);
        }
      }
    }
  } else {
    return empty_with(&b, d, NULL);
  }

  free(d);
  lean_object *s = lean_mk_string(b.p);
  free(b.p);
  return s;
}
