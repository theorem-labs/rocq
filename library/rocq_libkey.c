/************************************************************************/
/*         *      The Rocq Prover / The Rocq Development Team           */
/*  v      *         Copyright INRIA, CNRS and contributors             */
/* <O___,, * (see version control and CREDITS file for authors & dates) */
/*   \VV/  **************************************************************/
/*    //   *    This file is distributed under the terms of the         */
/*         *     GNU Lesser General Public License Version 2.1          */
/*         *     (see LICENSE file for the text of the license)         */
/************************************************************************/

/* The canonical encoding of library/libkey.mli and SHA-256 (FIPS 180-4).

   The walk allocates nothing in the OCaml heap and never calls back into
   OCaml, so no collection runs while it reads the value: a block's address
   identifies it for the whole walk. Its tables live in the C heap. */

#define CAML_NAME_SPACE
#include <setjmp.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <caml/alloc.h>
#include <caml/callback.h>
#include <caml/fail.h>
#include <caml/memory.h>
#include <caml/mlvalues.h>

/* {1 SHA-256} */

static const uint32_t sha_k[64] = {
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2 };

#define ROR(x, n) (((x) >> (n)) | ((x) << (32 - (n))))

static void sha_blocks_portable(uint32_t st[8], const uint8_t *p, size_t nblocks)
{
  uint32_t w[64];
  for (; nblocks > 0; nblocks--, p += 64) {
    for (int i = 0; i < 16; i++)
      w[i] = ((uint32_t)p[4 * i] << 24) | ((uint32_t)p[4 * i + 1] << 16)
        | ((uint32_t)p[4 * i + 2] << 8) | (uint32_t)p[4 * i + 3];
    for (int i = 16; i < 64; i++) {
      uint32_t s0 = ROR(w[i - 15], 7) ^ ROR(w[i - 15], 18) ^ (w[i - 15] >> 3);
      uint32_t s1 = ROR(w[i - 2], 17) ^ ROR(w[i - 2], 19) ^ (w[i - 2] >> 10);
      w[i] = w[i - 16] + s0 + w[i - 7] + s1;
    }
    uint32_t a = st[0], b = st[1], c = st[2], d = st[3];
    uint32_t e = st[4], f = st[5], g = st[6], h = st[7];
    for (int i = 0; i < 64; i++) {
      uint32_t s1 = ROR(e, 6) ^ ROR(e, 11) ^ ROR(e, 25);
      uint32_t ch = (e & f) ^ (~e & g);
      uint32_t t1 = h + s1 + ch + sha_k[i] + w[i];
      uint32_t s0 = ROR(a, 2) ^ ROR(a, 13) ^ ROR(a, 22);
      uint32_t maj = (a & b) ^ (a & c) ^ (b & c);
      uint32_t t2 = s0 + maj;
      h = g; g = f; f = e; e = d + t1; d = c; c = b; b = a; a = t1 + t2;
    }
    st[0] += a; st[1] += b; st[2] += c; st[3] += d;
    st[4] += e; st[5] += f; st[6] += g; st[7] += h;
  }
}

#if defined(__x86_64__) && (defined(__GNUC__) || defined(__clang__))
#include <cpuid.h>
#include <immintrin.h>
#define HAVE_SHA_NI_CODE 1

/* The x86 SHA extensions. Each of the 16 steps does four rounds; the
   message schedule keeps the last four groups of four words. */
__attribute__((target("sha,sse4.1,ssse3")))
static void sha_blocks_shani(uint32_t st[8], const uint8_t *p, size_t nblocks)
{
  const __m128i bswap = _mm_set_epi64x(0x0c0d0e0f08090a0bULL, 0x0405060700010203ULL);
  __m128i tmp = _mm_loadu_si128((const __m128i *)&st[0]);
  __m128i state1 = _mm_loadu_si128((const __m128i *)&st[4]);
  tmp = _mm_shuffle_epi32(tmp, 0xB1);              /* CDAB */
  state1 = _mm_shuffle_epi32(state1, 0x1B);        /* EFGH */
  __m128i state0 = _mm_alignr_epi8(tmp, state1, 8); /* ABEF */
  state1 = _mm_blend_epi16(state1, tmp, 0xF0);     /* CDGH */
  for (; nblocks > 0; nblocks--, p += 64) {
    __m128i abef = state0, cdgh = state1;
    __m128i w[4];
    for (int i = 0; i < 16; i++) {
      __m128i m;
      if (i < 4) {
        m = _mm_shuffle_epi8(_mm_loadu_si128((const __m128i *)(p + 16 * i)), bswap);
      } else {
        __m128i w4 = w[i & 3], w3 = w[(i + 1) & 3], w2 = w[(i + 2) & 3], w1 = w[(i + 3) & 3];
        m = _mm_sha256msg1_epu32(w4, w3);
        m = _mm_add_epi32(m, _mm_alignr_epi8(w1, w2, 4));
        m = _mm_sha256msg2_epu32(m, w1);
      }
      w[i & 3] = m;
      __m128i msg = _mm_add_epi32(m, _mm_loadu_si128((const __m128i *)&sha_k[4 * i]));
      state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
      msg = _mm_shuffle_epi32(msg, 0x0E);
      state0 = _mm_sha256rnds2_epu32(state0, state1, msg);
    }
    state0 = _mm_add_epi32(state0, abef);
    state1 = _mm_add_epi32(state1, cdgh);
  }
  tmp = _mm_shuffle_epi32(state0, 0x1B);           /* FEBA */
  state1 = _mm_shuffle_epi32(state1, 0xB1);        /* DCHG */
  state0 = _mm_blend_epi16(tmp, state1, 0xF0);     /* DCBA */
  state1 = _mm_alignr_epi8(state1, tmp, 8);        /* ABEF */
  _mm_storeu_si128((__m128i *)&st[0], state0);
  _mm_storeu_si128((__m128i *)&st[4], state1);
}

static int cpu_has_sha_ni(void)
{
  unsigned int a, b, c, d;
  if (!__get_cpuid(1, &a, &b, &c, &d)) return 0;
  if (!(c & (1u << 19)) || !(c & (1u << 9))) return 0; /* SSE4.1, SSSE3 */
  if (__get_cpuid_max(0, NULL) < 7) return 0;
  __cpuid_count(7, 0, a, b, c, d);
  return (b >> 29) & 1;
}
#endif

typedef void (*sha_blocks_fn)(uint32_t *, const uint8_t *, size_t);
static sha_blocks_fn sha_blocks = NULL;

static sha_blocks_fn sha_choose(void)
{
#ifdef HAVE_SHA_NI_CODE
  if (cpu_has_sha_ni()) return sha_blocks_shani;
#endif
  return sha_blocks_portable;
}

/* The padded message is the message, 0x80, zeroes, and its length in bits
   as a big-endian 64-bit integer, to a multiple of 64 bytes. A short
   message (most nodes) is padded in one buffer and compressed in one call;
   a long one has its full blocks compressed in place. */
#define SHORT_MESSAGE 256

static void sha256(const uint8_t *msg, size_t len, uint8_t out[32])
{
  uint32_t st[8] = { 0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
                     0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19 };
  uint8_t pad[SHORT_MESSAGE + 128];
  size_t full = len < SHORT_MESSAGE ? 0 : len / 64, rest = len - 64 * full;
  size_t padded = (rest + 9 + 63) / 64 * 64;
  if (sha_blocks == NULL) sha_blocks = sha_choose();
  if (full > 0) sha_blocks(st, msg, full);
  memcpy(pad, msg + 64 * full, rest);
  memset(pad + rest, 0, padded - rest);
  pad[rest] = 0x80;
  uint64_t bits = (uint64_t)len * 8;
  for (int i = 0; i < 8; i++) pad[padded - 1 - i] = (uint8_t)(bits >> (8 * i));
  sha_blocks(st, pad, padded / 64);
  for (int i = 0; i < 8; i++) {
    out[4 * i] = (uint8_t)(st[i] >> 24); out[4 * i + 1] = (uint8_t)(st[i] >> 16);
    out[4 * i + 2] = (uint8_t)(st[i] >> 8); out[4 * i + 3] = (uint8_t)st[i];
  }
}

value rocq_libkey_sha256(value s)
{
  CAMLparam1(s);
  CAMLlocal1(r);
  uint8_t out[32];
  /* [s] is read before the result is allocated: no collection in between. */
  sha256((const uint8_t *)String_val(s), caml_string_length(s), out);
  r = caml_alloc_initialized_string(32, (const char *)out);
  CAMLreturn(r);
}

/* Whether the compression in use is the x86 SHA extensions'. */
value rocq_libkey_sha_extensions(value unit)
{
  (void)unit;
  if (sha_blocks == NULL) sha_blocks = sha_choose();
#ifdef HAVE_SHA_NI_CODE
  return Val_bool(sha_blocks == sha_blocks_shani);
#else
  return Val_false;
#endif
}

/* Selects the portable compression even where the SHA extensions exist, so
   that the tests check both. */
value rocq_libkey_force_portable(value b)
{
  sha_blocks = Bool_val(b) ? sha_blocks_portable : sha_choose();
  return Val_unit;
}

/* {1 The encoding} */

#define INLINE_LIMIT 64
#if defined(__GNUC__) || defined(__clang__)
#define PREFETCH(p) __builtin_prefetch(p)
#else
#define PREFETCH(p) ((void)0)
#endif
#define IN_PROGRESS ((int64_t)-1)

enum { ERR_NONE, ERR_MEMORY, ERR_UNSUPPORTED };

typedef struct { uint8_t *p; size_t len, cap; } buf;

typedef struct { uintptr_t key; int64_t val; } entry;

typedef struct {
  jmp_buf fail;
  char reason[64];
  /* Digests by address (see [memo_set]); a [key] 0 is a free slot. */
  entry *tab;
  size_t mask, count;
  buf digests;
  /* The block being finished, and a leaf's encoding before it is hashed. */
  buf sc, leaf;
  /* The [repr]s of finished blocks whose parent is not finished, end to end
     in [res]; the [k]-th starts at [roff[k]]. */
  buf res;
  size_t *roff, rsp, rcap;
  /* Blocks to visit (an even address) or to finish (address + 1). */
  uintptr_t *stk;
  size_t sp, scap;
} ctx;

static void fail(ctx *c, int err) { longjmp(c->fail, err); }

static void unsupported(ctx *c, const char *what)
{
  snprintf(c->reason, sizeof c->reason, "%s", what);
  fail(c, ERR_UNSUPPORTED);
}

static void *grow(ctx *c, void *p, size_t bytes)
{
  void *q = realloc(p, bytes);
  if (q == NULL) fail(c, ERR_MEMORY);
  return q;
}

static inline void reserve(ctx *c, buf *b, size_t n)
{
  if (b->len + n > b->cap) {
    size_t cap = 2 * b->cap;
    if (cap < b->len + n) cap = b->len + n;
    b->p = grow(c, b->p, cap);
    b->cap = cap;
  }
}

static inline void put_byte(ctx *c, buf *b, uint8_t x)
{
  reserve(c, b, 1);
  b->p[b->len++] = x;
}

static inline void put_bytes(ctx *c, buf *b, const uint8_t *s, size_t n)
{
  reserve(c, b, n);
  memcpy(b->p + b->len, s, n);
  b->len += n;
}

static inline void put_uvar(ctx *c, buf *b, uint64_t n)
{
  reserve(c, b, 10);
  while (n >= 0x80) { b->p[b->len++] = (uint8_t)(n | 0x80); n >>= 7; }
  b->p[b->len++] = (uint8_t)n;
}

static inline size_t uvar_length(uint64_t n)
{
  size_t k = 1;
  while (n >= 0x80) { n >>= 7; k++; }
  return k;
}

/* An OCaml integer as the LEB128 of its zigzag form. */
static inline void put_int(ctx *c, buf *b, intnat n)
{
  put_byte(c, b, 0x00);
  put_uvar(c, b, ((uint64_t)n << 1) ^ (uint64_t)(n >> (8 * sizeof(intnat) - 1)));
}

static inline void put_f64(ctx *c, buf *b, double d)
{
  uint64_t u;
  memcpy(&u, &d, 8);
  reserve(c, b, 8);
  for (int i = 0; i < 8; i++) b->p[b->len++] = (uint8_t)(u >> (8 * i));
}

static inline size_t slot_of(ctx *c, uintptr_t a)
{
  return (size_t)(((uint64_t)a >> 3) * 0x9E3779B97F4A7C15ULL >> 20) & c->mask;
}

static inline size_t find(ctx *c, uintptr_t a)
{
  size_t i = slot_of(c, a);
  while (c->tab[i].key != 0 && c->tab[i].key != a) i = (i + 1) & c->mask;
  return i;
}

static void memo_set(ctx *c, uintptr_t a, int64_t v);

static void rehash(ctx *c)
{
  entry *tab = c->tab;
  size_t old = c->mask + 1, n = 2 * old;
  c->tab = calloc(n, sizeof *c->tab);
  if (c->tab == NULL) { c->tab = tab; fail(c, ERR_MEMORY); }
  c->mask = n - 1;
  c->count = 0;
  for (size_t i = 0; i < old; i++) if (tab[i].key != 0) memo_set(c, tab[i].key, tab[i].val);
  free(tab);
}

/* A value [d >= 0]: the [repr] is 0x07 and the 32 bytes at [32 * d] of
   [digests]. [IN_PROGRESS]: the block's fields are being encoded. */
static void memo_set(ctx *c, uintptr_t a, int64_t v)
{
  if (2 * (c->count + 1) > c->mask + 1) rehash(c);
  size_t i = find(c, a);
  if (c->tab[i].key == 0) { c->tab[i].key = a; c->count++; }
  c->tab[i].val = v;
}

/* Deletes the entry at slot [i], and moves back the later entries of its
   probe run that would otherwise no longer be found. */
static void memo_remove_at(ctx *c, size_t i)
{
  size_t hole = i, j = i;
  for (;;) {
    j = (j + 1) & c->mask;
    uintptr_t k = c->tab[j].key;
    if (k == 0) break;
    size_t h = slot_of(c, k);
    /* [k] stays at [j] when its home lies cyclically in (hole, j]. */
    int stays = hole <= j ? (hole < h && h <= j) : (hole < h || h <= j);
    if (!stays) { c->tab[hole] = c->tab[j]; hole = j; }
  }
  c->tab[hole].key = 0;
  c->count--;
}

/* Appends 0x07 and the digest of [n] bytes at [s] to [dst]; returns the
   digest's index in [digests]. */
static int64_t put_new_digest(ctx *c, const uint8_t *s, size_t n, buf *dst)
{
  reserve(c, &c->digests, 32);
  int64_t idx = (int64_t)(c->digests.len / 32);
  sha256(s, n, c->digests.p + c->digests.len);
  c->digests.len += 32;
  put_byte(c, dst, 0x07);
  put_bytes(c, dst, c->digests.p + 32 * idx, 32);
  return idx;
}

static inline void put_known_digest(ctx *c, int64_t idx, buf *dst)
{
  put_byte(c, dst, 0x07);
  put_bytes(c, dst, c->digests.p + 32 * idx, 32);
}

static inline int is_structural(value v) { return Is_block(v) && Tag_val(v) < Lazy_tag; }

/* Appends the [repr] of a string, float or float array to [dst]. A long
   string's digest is kept by address like a block's. */
static void put_leaf(ctx *c, buf *dst, value o)
{
  tag_t tag = Tag_val(o);
  if (tag == String_tag) {
    size_t n = caml_string_length(o);
    const uint8_t *s = (const uint8_t *)String_val(o);
    if (1 + uvar_length(n) + n < INLINE_LIMIT) {
      put_byte(c, dst, 0x01); put_uvar(c, dst, n); put_bytes(c, dst, s, n);
    } else {
      size_t i = find(c, (uintptr_t)o);
      if (c->tab[i].key == (uintptr_t)o) put_known_digest(c, c->tab[i].val, dst);
      else {
        c->leaf.len = 0;
        put_byte(c, &c->leaf, 0x01); put_uvar(c, &c->leaf, n); put_bytes(c, &c->leaf, s, n);
        int64_t idx = put_new_digest(c, c->leaf.p, c->leaf.len, dst);
        memo_set(c, (uintptr_t)o, idx);
      }
    }
  } else if (tag == Double_tag) {
    put_byte(c, dst, 0x02); put_f64(c, dst, Double_val(o));
  } else if (tag == Double_array_tag) {
    size_t n = Wosize_val(o) / Double_wosize;
    c->leaf.len = 0;
    put_byte(c, &c->leaf, 0x03); put_uvar(c, &c->leaf, n);
    for (size_t i = 0; i < n; i++) put_f64(c, &c->leaf, Double_flat_field(o, i));
    if (c->leaf.len < INLINE_LIMIT) put_bytes(c, dst, c->leaf.p, c->leaf.len);
    else (void)put_new_digest(c, c->leaf.p, c->leaf.len, dst);
  } else if (tag == Custom_tag) unsupported(c, "custom block");
  else if (tag == Closure_tag || tag == Infix_tag) unsupported(c, "closure");
  else if (tag == Lazy_tag || tag == Forward_tag) unsupported(c, "lazy value");
  else if (tag == Object_tag) unsupported(c, "object");
  else {
    char what[32];
    snprintf(what, sizeof what, "block of tag %d", (int)tag);
    unsupported(c, what);
  }
}

static inline void push(ctx *c, uintptr_t e)
{
  if (c->sp == c->scap) {
    c->scap *= 2;
    c->stk = grow(c, c->stk, c->scap * sizeof *c->stk);
  }
  c->stk[c->sp++] = e;
}

static inline void push_result(ctx *c)
{
  if (c->rsp == c->rcap) {
    c->rcap *= 2;
    c->roff = grow(c, c->roff, c->rcap * sizeof *c->roff);
  }
  c->roff[c->rsp++] = c->res.len;
}

/* Encodes block [o] into [sc]; the [repr]s of its [nstruct] structural
   fields are the last ones in [res], in field order, and are popped. */
static void encode_block(ctx *c, value o, size_t nstruct)
{
  mlsize_t size = Wosize_val(o);
  size_t base = c->rsp - nstruct, k = base;
  buf *sc = &c->sc;
  sc->len = 0;
  put_byte(c, sc, 0x04); put_byte(c, sc, (uint8_t)Tag_val(o)); put_uvar(c, sc, size);
  for (mlsize_t i = 0; i < size; i++) {
    value f = Field(o, i);
    if (Is_long(f)) put_int(c, sc, Long_val(f));
    else if (Tag_val(f) < Lazy_tag) {
      size_t start = c->roff[k], stop = k + 1 == c->rsp ? c->res.len : c->roff[k + 1];
      put_bytes(c, sc, c->res.p + start, stop - start);
      k++;
    } else put_leaf(c, sc, f);
  }
  if (nstruct > 0) { c->res.len = c->roff[base]; c->rsp = base; }
}

static inline size_t count_structural(value o)
{
  size_t n = 0;
  for (mlsize_t i = 0, size = Wosize_val(o); i < size; i++) n += is_structural(Field(o, i));
  return n;
}

/* Postorder over [stk]. Every visit of a structural block leaves exactly one
   [repr] in [res], so when a block is finished the [repr]s of its
   structural fields are the last ones in [res], in field order. A block
   with no structural field is finished when it is visited. */
static void walk(ctx *c, value root)
{
  push(c, (uintptr_t)root);
  while (c->sp > 0) {
    uintptr_t e = c->stk[--c->sp];
    if (e & 1) {
      value o = (value)(e - 1);
      encode_block(c, o, count_structural(o));
      push_result(c);
      size_t i = find(c, (uintptr_t)o);
      if (c->sc.len < INLINE_LIMIT) {
        put_bytes(c, &c->res, c->sc.p, c->sc.len);
        memo_remove_at(c, i);
      } else
        c->tab[i].val = put_new_digest(c, c->sc.p, c->sc.len, &c->res);
    } else {
      value o = (value)e;
      size_t i = find(c, e);
      if (c->tab[i].key == e) {
        /* A block met again while its own fields are being encoded is
           reachable from itself. */
        if (c->tab[i].val == IN_PROGRESS) unsupported(c, "cyclic value");
        push_result(c);
        put_known_digest(c, c->tab[i].val, &c->res);
      } else if (count_structural(o) == 0) {
        encode_block(c, o, 0);
        push_result(c);
        if (c->sc.len < INLINE_LIMIT) put_bytes(c, &c->res, c->sc.p, c->sc.len);
        else memo_set(c, e, put_new_digest(c, c->sc.p, c->sc.len, &c->res));
      } else {
        memo_set(c, e, IN_PROGRESS);
        push(c, e + 1);
        for (mlsize_t j = Wosize_val(o); j > 0; j--) {
          value f = Field(o, j - 1);
          if (is_structural(f)) {
            /* Its header and its table slot are read when it is visited. */
            PREFETCH((const void *)&Field(f, 0));
            PREFETCH(&c->tab[slot_of(c, (uintptr_t)f)]);
            push(c, (uintptr_t)f);
          }
        }
      }
    }
  }
}

static void ctx_free(ctx *c)
{
  free(c->tab); free(c->digests.p); free(c->sc.p); free(c->leaf.p);
  free(c->res.p); free(c->roff); free(c->stk);
  free(c);
}

static void raise_unsupported(const char *what)
{
  const value *exn = caml_named_value("Libkey.Unsupported");
  if (exn == NULL) caml_failwith(what);
  caml_raise_with_string(*exn, what);
}

value rocq_libkey_encode(value root)
{
  CAMLparam1(root);
  CAMLlocal1(r);
  char reason[64];
  ctx *c = calloc(1, sizeof *c);
  if (c == NULL) caml_raise_out_of_memory();
  int err = setjmp(c->fail);
  if (err == ERR_NONE) {
    c->mask = 65535;
    c->tab = calloc(c->mask + 1, sizeof *c->tab);
    c->scap = 1024; c->stk = malloc(c->scap * sizeof *c->stk);
    c->rcap = 1024; c->roff = malloc(c->rcap * sizeof *c->roff);
    if (c->tab == NULL || c->stk == NULL || c->roff == NULL)
      fail(c, ERR_MEMORY);
    buf *out;
    if (is_structural(root)) { walk(c, root); out = &c->res; }
    else {
      out = &c->sc;
      if (Is_long(root)) put_int(c, out, Long_val(root));
      else put_leaf(c, out, root);
    }
    /* A [repr] is at most 63 bytes (an inline encoding is shorter than 64,
       a digest is 33). It is copied out and the walk's buffers are freed
       before allocating, which may raise [Out_of_memory] or move the
       value. */
    char repr[INLINE_LIMIT];
    size_t len = out->len;
    memcpy(repr, out->p, len);
    ctx_free(c);
    r = caml_alloc_initialized_string(len, repr);
    CAMLreturn(r);
  }
  memcpy(reason, c->reason, sizeof reason);
  ctx_free(c);
  if (err == ERR_MEMORY) caml_raise_out_of_memory();
  raise_unsupported(reason);
  CAMLreturn(Val_unit);
}
