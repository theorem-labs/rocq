/************************************************************************/
/*         *      The Rocq Prover / The Rocq Development Team           */
/*  v      *         Copyright INRIA, CNRS and contributors             */
/* <O___,, * (see version control and CREDITS file for authors & dates) */
/*   \VV/  **************************************************************/
/*    //   *    This file is distributed under the terms of the         */
/*         *     GNU Lesser General Public License Version 2.1          */
/*         *     (see LICENSE file for the text of the license)         */
/************************************************************************/

/* The routines of the BINNUM and BINNUMCALL instructions.

   Each routine computes what its reference term in kernel/vmbinnum.ml
   computes. The arguments are trees of constructor values with the VM
   representation that vmbinnum.ml checks on the inductive types (the
   [mind_reloc_tbl] of kernel/indtypes.ml). A positive is a chain of nodes,
   a packed block (rocq_binnum.h), or a chain over a packed tail; every
   positive is read through a cursor (below), which reads a packed block as
   its number and never reads its fields as chain nodes. A Z, an N and a
   nat are read through the same cursor, because their constructors have
   the tags of a positive's (see cur_node_nat).

   A routine reads at least the nodes that the bytecode of the reference
   reads, and stops at the first node that is not a constructor of the
   expected type, such as an accumulator: it then refuses the call, and the
   bytecode of the function runs as if the instruction were not there. It
   checks each node in the same walk that decodes it, and writes nothing
   that outlives the call before its last read. The nodes that it does not
   read are those that the bytecode does not read either, and the bytecode's
   result holds them unchanged; so does the routine's, which takes them from
   the argument. A packed block holds no accumulator, so reading it whole
   reads no more than the bytecode could.

   A positive result that the routine computes whole, rather than over a
   shared subterm of a chain argument, is packed when it has 2 to 62 bits
   and packing is on.

   Numbers are decoded into a 64-bit word when they have at most 64 bits,
   and into 32-bit limbs otherwise; the bits of a fresh chain likewise.

   The routine numbers and arities below must be those of the table
   [routines] of vmbinnum.ml, which compares them with [rocq_binnum_arities]
   when it is loaded. */

#include <stdint.h>
#include <stdlib.h>
#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>

#include "rocq_binnum.h"

/* The routine numbers: append only, as the opcodes of genOpcodeFiles.ml. A
   new routine goes at the end, and no routine is moved or removed, because
   the number is stored in the bytecode of .vo files (see [routines] in
   vmbinnum.ml). */
enum {
  BINNUM_POS_COMPARE_CONT,
  BINNUM_POS_EQB,
  BINNUM_POS_SUCC,
  BINNUM_POS_ADD,
  BINNUM_POS_ADD_CARRY,
  BINNUM_POS_PRED_DOUBLE,
  BINNUM_POS_MUL,
  BINNUM_POS_DIV2,
  BINNUM_POS_OF_SUCC_NAT,
  BINNUM_Z_DOUBLE,
  BINNUM_Z_SUCC_DOUBLE,
  BINNUM_Z_PRED_DOUBLE,
  BINNUM_Z_POS_SUB,
  BINNUM_Z_ADD,
  BINNUM_Z_MUL,
  BINNUM_Z_COMPARE,
  BINNUM_Z_LEB,
  BINNUM_Z_LTB,
  BINNUM_Z_EQB,
  BINNUM_Z_DIV2,
  BINNUM_Z_OF_NAT,
  BINNUM_Z_POS_DIV_EUCL,
  BINNUM_NAT_EQB,
  BINNUM_NAT_LEB,
  BINNUM_UINT63_TO_Z_REC,
  BINNUM_UINT63_OF_POS_REC,
  BINNUM_Z_POW,
  BINNUM_COUNT
};

static const int binnum_arity[BINNUM_COUNT] = {
  3, 2, 1, 2, 2, 1, 2, 1, 1,
  1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 1, 2,
  2, 2,
  2, 2, 2
};

/* Counters, printed by vmbinnum.ml when ROCQ_VM_BINNUM_STATS is set, and
   kept only then: the calls of each routine, the calls it refused, and the
   nodes it read (in accepted and refused calls), at function entry (site 0)
   and at call sites (site 1); the arguments whose nodes it started to read
   (a positive, a Z, an N or a nat), those that were a packed block and
   those that were a chain over a packed tail; the packed results it made;
   the expansions of packed blocks by SWITCH (0), rocq_binnum_expand (1)
   and PROJ (2), with the nodes they made; and the literals packed, with
   their nodes. */
int rocq_binnum_stats;
static uint64_t binnum_calls[2][BINNUM_COUNT];
static uint64_t binnum_refusals[2][BINNUM_COUNT];
static uint64_t binnum_words[2][BINNUM_COUNT];
static uint64_t binnum_args[BINNUM_COUNT];
static uint64_t binnum_args_packed[BINNUM_COUNT];
static uint64_t binnum_args_tail[BINNUM_COUNT];
static uint64_t binnum_packed_results[BINNUM_COUNT];
static uint64_t binnum_expansions[3];
static uint64_t binnum_expansion_nodes[3];
static uint64_t binnum_literals, binnum_literal_nodes;

/* Packing of results: on unless ROCQ_VM_BINNUM=-pack, and never where
   ROCQ_BINNUM_PACKING is 0. */
static int binnum_pack = ROCQ_BINNUM_PACKING;

/* Packing of the chains in the VM values of structured constants: on unless
   ROCQ_VM_BINNUM=-pack or -packlit. Vmbinnum sets both flags when it is
   loaded, before any constant is compiled. */
static int binnum_packlit = ROCQ_BINNUM_PACKING;

/* The result of the call in progress. */
static struct binnum_result R;

/* Adds to a counter of the call in progress, when the statistics are on. */
#define COUNT(field, n) do { if (rocq_binnum_stats) R.field += (n); } while (0)

/* The cursor's functions and the cores that walk numbers are inlined in
   each routine, so that its cursors stay in registers. */
#define HOT static inline __attribute__((always_inline))

/* comparison: Eq | Lt | Gt, three constant constructors. */
#define CMP_EQ Val_int(0)
#define CMP_LT Val_int(1)
#define CMP_GT Val_int(2)

/* bool: true | false, two constant constructors. */
#define BOOL_TRUE Val_int(0)
#define BOOL_FALSE Val_int(1)

/* A node of a positive: xI and xO are the blocks of tag 1 and 2 with one
   field, xH is the constant Val_int(0). */
#define POS_XH 0
#define POS_XI 1
#define POS_XO 2

/* A node of a Z: Z0 is Val_int(0), Zpos and Zneg the blocks of tag 1 and 2
   with one field (a positive). A node of an N: N0 is Val_int(0), Npos the
   block of tag 1. A node of a nat: O is Val_int(0), S the block of tag 1.

   The three sets of tags are those of a positive, so cur_node reads a node
   of any of them, and a packed block stands for any of them (rocq_binnum.h).
   A reader of an N or of a nat refuses tag 2 (cur_node_nat). */
#define Z_ZERO 0
#define Z_POS 1
#define Z_NEG 2

/** The cursor.

    Every walk over a positive goes through a cursor. In chain mode it is
    at the node [v], the subterm of argument [arg] at [depth] steps through
    field 0. When it reads a packed block it goes to packed mode, where [m]
    is the rest of the number, from the bit at the cursor up (1 is xH): it
    reads the bits of [m] without memory reads, and never reads the block's
    fields again, in particular not as chain nodes. So a chain, a packed
    block and a chain over a packed tail are all read as the same number. A
    cursor counts one word per chain node it reads and one per packed
    block, only when the statistics are on. */

struct cursor {
  value v;
  uint64_t m;
  int packed;
  int arg;
  uint64_t depth;
  uint64_t start;
};

HOT void cur_init(struct cursor *c, value v, int arg, uint64_t depth)
{
  c->v = v;
  c->m = 0;
  c->packed = 0;
  c->arg = arg;
  c->depth = depth;
  c->start = depth;
  COUNT(args, 1);
}

static __attribute__((noinline)) int cur_enter(struct cursor *c, value v)
{
  c->m = binnum_packed_number(v);
  c->packed = 1;
  if (rocq_binnum_stats) {
    if (c->depth == c->start) R.args_packed++;
    else R.args_tail++;
  }
  return c->m & 1 ? POS_XI : POS_XO;
}

/* The node at the cursor: POS_XI, POS_XO, POS_XH, or -1 for any other
   value, such as an accumulator. */
HOT int cur_node(struct cursor *c)
{
  value v;
  tag_t t;
  if (c->packed) return c->m == 1 ? POS_XH : c->m & 1 ? POS_XI : POS_XO;
  v = c->v;
  COUNT(words, 1);
  if (Is_long(v)) return v == Val_int(0) ? POS_XH : -1;
  t = Tag_val(v);
  if (t == POS_XI || t == POS_XO) return Wosize_val(v) == 1 ? (int) t : -1;
  if (ROCQ_BINNUM_PACKING && t == BINNUM_PACKED_TAG) return cur_enter(c, v);
  return -1;
}

/* Moves past the node at the cursor, which cur_node read as xI or xO. In
   chain mode that node is a block of tag 1 or 2, never a packed block. */
HOT void cur_next(struct cursor *c)
{
  if (c->packed) c->m >>= 1;
  else c->v = Field(c->v, 0);
  c->depth++;
}

/* Reads the rest of the positive at the cursor. Returns 1 if it is closed. */
HOT int cur_closed(struct cursor *c)
{
  for (;;) {
    int k = cur_node(c);
    if (k < 0) return 0;
    if (k == POS_XH || c->packed) return 1;
    cur_next(c);
  }
}

/* The node of an N or of a nat at the cursor: POS_XH (0) for N0 or O,
   POS_XI (1) for Npos or S, -1 for any other value. Tag 2 is a constructor
   of neither type: a packed even number is refused here, as is a block of
   tag 2. */
HOT int cur_node_nat(struct cursor *c)
{
  int k = cur_node(c);
  return k == POS_XO ? -1 : k;
}

/* The number of S nodes of the nat of the packed rest [m] (m > 1), or -1
   when it is not one. The chain of m is a nat only if every node is tag 1,
   that is if every bit of m is set: S^k O is 2^(k+1) - 1. */
HOT int64_t nat_packed_length(uint64_t m)
{
  if ((m & (m + 1)) != 0) return -1;
  return (int64_t)(binnum_bitlen(m) - 1);
}

/* The number of S nodes of the nat at the cursor, or -1 when one of its
   nodes is not a constructor of nat. A packed rest is read whole, in O(1).
   A nat has no sharing to keep, so no routine needs its cursor afterwards. */
HOT int64_t nat_length(struct cursor *c)
{
  int64_t k = 0;
  for (;;) {
    int kn = cur_node_nat(c);
    if (kn < 0) return -1;
    if (kn == POS_XH) return k;
    if (c->packed) {
      int64_t rest = nat_packed_length(c->m);
      return rest < 0 ? -1 : k + rest;
    }
    k++;
    cur_next(c);
  }
}

/** Large numbers, in C buffers: little-endian arrays of 32-bit limbs. A
    number is normalized when its top limb is not zero. The same type holds
    the bits of a long chain of fresh nodes. The buffers are static and grow
    as needed; a routine whose buffer cannot grow refuses the call. */

typedef uint32_t limb;

struct num { limb *d; size_t n; size_t cap; };

static struct num num_a, num_b, num_r, num_q, num_m;

/* Three more buffers, for the powers of Z.pow alone. */
static struct num num_p1, num_p2, num_p3;

static int num_reserve(struct num *x, size_t n)
{
  limb *d;
  size_t cap;
  if (n <= x->cap) return 1;
  cap = x->cap ? x->cap : 16;
  while (cap < n) cap *= 2;
  d = realloc(x->d, cap * sizeof(limb));
  if (d == NULL) return 0;
  x->d = d;
  x->cap = cap;
  return 1;
}

/* Sets bit i of x to b. The bits must be put in order from bit 0: the
   first bit of each limb clears the limb. */
static int bits_put(struct num *x, uint64_t i, int b)
{
  size_t l = (size_t)(i >> 5);
  if (!num_reserve(x, l + 1)) return 0;
  if ((i & 31) == 0) x->d[l] = 0;
  if (b) x->d[l] |= (limb)1 << (i & 31);
  return 1;
}

/* Puts the bits of m >= 1, from bit i up, after bits 0 to i - 1; x then
   has i + bitlen(m) bits. */
static int bits_put_number(struct num *x, uint64_t i, uint64_t m)
{
  unsigned b, len = binnum_bitlen(m);
  for (b = 0; b < len; b++)
    if (!bits_put(x, i + b, (m >> b) & 1)) return 0;
  x->n = (size_t)((i + len - 1) >> 5) + 1;
  return 1;
}

static void num_norm(struct num *x)
{
  while (x->n > 0 && x->d[x->n - 1] == 0) x->n--;
}

static uint64_t num_bitlen(const struct num *x)
{
  limb top;
  uint64_t b;
  if (x->n == 0) return 0;
  top = x->d[x->n - 1];
  b = (uint64_t)(x->n - 1) * 32;
  while (top) { b++; top >>= 1; }
  return b;
}

static int num_cmp(const struct num *a, const struct num *b)
{
  size_t i;
  if (a->n != b->n) return a->n < b->n ? -1 : 1;
  for (i = a->n; i-- > 0;)
    if (a->d[i] != b->d[i]) return a->d[i] < b->d[i] ? -1 : 1;
  return 0;
}

/* r = a - b, for a >= b; r may be a. */
static int num_sub(struct num *r, const struct num *a, const struct num *b)
{
  size_t i;
  uint64_t borrow = 0;
  if (!num_reserve(r, a->n)) return 0;
  for (i = 0; i < a->n; i++) {
    uint64_t s = (uint64_t)(i < b->n ? b->d[i] : 0) + borrow;
    uint64_t ai = a->d[i];
    r->d[i] = (limb)(ai - s);
    borrow = ai < s;
  }
  r->n = a->n;
  num_norm(r);
  return 1;
}

/* r = a * b; r is neither a nor b. */
static int num_mul(struct num *r, const struct num *a, const struct num *b)
{
  size_t i, j, n = a->n + b->n;
  if (!num_reserve(r, n)) return 0;
  for (i = 0; i < n; i++) r->d[i] = 0;
  for (i = 0; i < a->n; i++) {
    uint64_t c = 0;
    for (j = 0; j < b->n; j++) {
      uint64_t t = (uint64_t)a->d[i] * b->d[j] + r->d[i + j] + c;
      r->d[i + j] = (limb)t;
      c = t >> 32;
    }
    r->d[i + b->n] = (limb)c;
  }
  r->n = n;
  num_norm(r);
  return 1;
}

/* q = a / b and m = a mod b, for b > 0; q and m are neither a nor b. */
static int num_divmod(struct num *q, struct num *m, const struct num *a, const struct num *b)
{
  size_t i;
  uint64_t bit;
  if (!num_reserve(q, a->n + 1) || !num_reserve(m, b->n + 1)) return 0;
  if (b->n == 1) {
    uint64_t rem = 0, d = b->d[0];
    for (i = a->n; i-- > 0;) {
      uint64_t cur = (rem << 32) | a->d[i];
      q->d[i] = (limb)(cur / d);
      rem = cur % d;
    }
    q->n = a->n;
    num_norm(q);
    m->d[0] = (limb)rem;
    m->n = 1;
    num_norm(m);
    return 1;
  }
  /* One bit at a time, from the top bit of a: m = 2 m + bit, and m < b. */
  for (i = 0; i < a->n; i++) q->d[i] = 0;
  q->n = a->n;
  m->n = 0;
  for (bit = num_bitlen(a); bit-- > 0;) {
    limb carry = (a->d[bit >> 5] >> (bit & 31)) & 1;
    size_t j;
    for (j = 0; j < m->n; j++) {
      limb hi = m->d[j] >> 31;
      m->d[j] = (m->d[j] << 1) | carry;
      carry = hi;
    }
    if (carry) m->d[m->n++] = carry;
    if (num_cmp(m, b) >= 0) {
      num_sub(m, m, b);
      q->d[bit >> 5] |= (limb)1 << (bit & 31);
    }
  }
  num_norm(q);
  return 1;
}

static int num_set_u64(struct num *x, uint64_t v)
{
  if (!num_reserve(x, 2)) return 0;
  x->d[0] = (limb)v;
  x->d[1] = (limb)(v >> 32);
  x->n = 2;
  num_norm(x);
  return 1;
}

static int num_is_pow2(const struct num *x)
{
  size_t i;
  for (i = 0; i + 1 < x->n; i++) if (x->d[i] != 0) return 0;
  return x->n > 0 && (x->d[x->n - 1] & (x->d[x->n - 1] - 1)) == 0;
}

static int num_copy(struct num *d, const struct num *s)
{
  size_t i;
  if (!num_reserve(d, s->n + 1)) return 0;
  for (i = 0; i < s->n; i++) d->d[i] = s->d[i];
  d->n = s->n;
  return 1;
}

/* num_r = base^e, for e >= 1, by squaring. The three buffers it works in
   are always distinct, because each step swaps two of the three pointers,
   and num_mul needs a result that is neither of its arguments. */
static int num_pow(const struct num *base, uint64_t e)
{
  struct num *acc = &num_p1, *sq = &num_p2, *tmp = &num_p3, *swap;
  int started = 0;
  if (!num_copy(sq, base)) return 0;
  for (;;) {
    if (e & 1) {
      if (!started) {
        if (!num_copy(acc, sq)) return 0;
        started = 1;
      } else {
        if (!num_mul(tmp, acc, sq)) return 0;
        swap = acc; acc = tmp; tmp = swap;
      }
    }
    e >>= 1;
    if (e == 0) break;
    if (!num_mul(tmp, sq, sq)) return 0;
    swap = sq; sq = tmp; tmp = swap;
  }
  return num_copy(&num_r, acc);
}

/* Reads the rest of the positive at the cursor, to its end: returns its
   number of bits L, with its value in *w when L <= 64, and in x otherwise.
   Returns 0 if one of its nodes is not a constructor of positive. */
HOT uint64_t read_pos(struct cursor *c, uint64_t *w, struct num *x)
{
  uint64_t i, acc = 0;
  int k;
  for (i = 0; i < 64; i++) {
    k = cur_node(c);
    if (k < 0) return 0;
    if (c->packed) {
      /* The rest is the number m: the value is acc + m 2^i. */
      uint64_t len = i + binnum_bitlen(c->m);
      if (len <= 64) {
        *w = acc | c->m << i;
        return len;
      }
      if (!num_reserve(x, 4)) return 0;
      x->d[0] = (limb)acc;
      x->d[1] = (limb)(acc >> 32);
      return bits_put_number(x, i, c->m) ? len : 0;
    }
    if (k == POS_XH) {
      *w = acc | (uint64_t)1 << i;
      return i + 1;
    }
    if (k == POS_XI) acc |= (uint64_t)1 << i;
    cur_next(c);
  }
  /* More than 64 bits: go on in limbs. */
  if (!num_reserve(x, 4)) return 0;
  x->d[0] = (limb)acc;
  x->d[1] = (limb)(acc >> 32);
  for (;;) {
    k = cur_node(c);
    if (k < 0) return 0;
    if (c->packed) return bits_put_number(x, i, c->m) ? i + binnum_bitlen(c->m) : 0;
    if (!bits_put(x, i, k != POS_XO)) return 0;
    if (k == POS_XH) {
      x->n = (size_t)(i >> 5) + 1;
      return i + 1;
    }
    cur_next(c);
    i++;
  }
}

/* The positive at the cursor when it is at most [cap], which is a power of
   two: 1 with its value in *out, and 0 when it is larger or is not a
   positive. It stops reading as soon as the number is known to be larger. */
HOT int read_pos_small(struct cursor *c, uint64_t cap, uint64_t *out)
{
  uint64_t acc = 0, i = 0, v;
  for (;;) {
    int k = cur_node(c);
    if (k < 0) return 0;
    if (c->packed) {
      if (c->m > (cap >> i)) return 0;
      v = acc | c->m << i;
      break;
    }
    if (k == POS_XH) {
      v = acc | (uint64_t)1 << i;
      break;
    }
    if (k == POS_XI) acc |= (uint64_t)1 << i;
    i++;
    if (((uint64_t)1 << i) > cap) return 0;
    cur_next(c);
  }
  if (v > cap) return 0;
  *out = v;
  return 1;
}

/** The bits of a chain of fresh nodes, from the outermost: in a word while
    there are at most 64, then in the limbs of num_r. At most one sink is
    used in a call. */

struct sink { uint64_t word; uint64_t n; };

static int sink_spill(struct sink *s, int b)
{
  if (s->n == 64) {
    if (!num_reserve(&num_r, 4)) return 0;
    num_r.d[0] = (limb)s->word;
    num_r.d[1] = (limb)(s->word >> 32);
  }
  if (!bits_put(&num_r, s->n, b)) return 0;
  s->n++;
  return 1;
}

HOT int sink_put(struct sink *s, int b)
{
  if (s->n < 64) {
    s->word |= (uint64_t)b << s->n;
    s->n++;
    return 1;
  }
  return sink_spill(s, b);
}

/** Results */

static void part_imm(struct binnum_part *p, value v)
{
  p->kind = BINNUM_IMM;
  p->imm = v;
}

/* The chain of the bits of s over a base: xH (BINNUM_BASE_XH), or the
   subterm of argument [arg] at [depth]. */
static int part_sink(struct binnum_part *p, int wrap, const struct sink *s, int arg,
                     uint64_t depth)
{
  p->kind = BINNUM_CHAIN;
  p->imm = Val_unit;
  p->wrap = wrap;
  p->nnodes = s->n;
  p->word = s->word;
  p->bits = num_r.d;
  p->base_arg = arg;
  p->base_depth = depth;
  p->base_num = 0;
  return 1;
}

/* A subterm of an argument, with no fresh node, wrapped if [wrap]. */
static int part_share(struct binnum_part *p, int wrap, int arg, uint64_t depth)
{
  struct sink s = { 0, 0 };
  return part_sink(p, wrap, &s, arg, depth);
}

/* The positive v >= 1, computed whole, wrapped in a block of tag [wrap] if
   not 0: one packed block when packing is on and 2 <= v < 2^62, otherwise
   a chain over xH. */
static int part_word(struct binnum_part *p, uint64_t v, int wrap)
{
  struct sink s;
  if (binnum_pack && v >= 2 && v < BINNUM_PACKED_LIMIT) {
    s.word = 0;
    s.n = 0;
    part_sink(p, wrap, &s, BINNUM_BASE_PACKED, 0);
    p->base_num = v;
    return 1;
  }
  s.word = v;
  s.n = binnum_bitlen(v) - 1;
  return part_sink(p, wrap, &s, BINNUM_BASE_XH, 0);
}

/* The positive x > 0, computed whole, in limbs. A chain of exactly 64
   nodes is built from [word] (rocq_interp.c), so [word] holds the low 64
   bits too. */
static int part_num(struct binnum_part *p, const struct num *x, int wrap)
{
  uint64_t n = num_bitlen(x) - 1;
  uint64_t low = (uint64_t)x->d[0] | (x->n > 1 ? (uint64_t)x->d[1] << 32 : 0);
  if (n < 64) return part_word(p, low, wrap);
  p->kind = BINNUM_CHAIN;
  p->imm = Val_unit;
  p->wrap = wrap;
  p->nnodes = n;
  p->word = low;
  p->bits = x->d;
  p->base_arg = BINNUM_BASE_XH;
  p->base_depth = 0;
  p->base_num = 0;
  return 1;
}

/* The positive s + h 2^(s->n), h >= 1, computed whole. */
static int part_sink_high(struct binnum_part *p, int wrap, struct sink *s, uint64_t h)
{
  unsigned b, len = binnum_bitlen(h);
  if (s->n + len <= 64) return part_word(p, s->word | h << s->n, wrap);
  /* Longer: the bits of h below its top bit go into the sink, over xH. */
  for (b = 0; b + 1 < len; b++)
    if (!sink_put(s, (h >> b) & 1)) return 0;
  return part_sink(p, wrap, s, BINNUM_BASE_XH, 0);
}

/* The Z of magnitude v (a word or limbs) and sign Zpos. */
static int part_z_word(struct binnum_part *p, uint64_t v)
{
  if (v == 0) {
    part_imm(p, Val_int(0));
    return 1;
  }
  return part_word(p, v, Z_POS);
}

static int part_z_num(struct binnum_part *p, const struct num *x)
{
  if (x->n == 0) {
    part_imm(p, Val_int(0));
    return 1;
  }
  return part_num(p, x, Z_POS);
}

/** Positive numbers */

/* Pos.compare_cont r x y {struct y}:
     x~1, y~1 -> compare_cont r x y      x~0, y~1 -> compare_cont Lt x y
     x~1, y~0 -> compare_cont Gt x y     x~0, y~0 -> compare_cont r x y
     x~1, 1   -> Gt                      x~0, 1   -> Gt
     1,   y~1 -> Lt     1, y~0 -> Lt     1,   1   -> r
   The loop runs these steps on both numbers at once, from their outermost
   constructors; r is the result if both end together. It reads both numbers
   to their ends. When both cursors are in packed mode, the rests of the two
   numbers are known: the one with the larger rest is the larger number, and
   equal rests leave r. */
HOT int pos_compare_core(value r, struct cursor *x, struct cursor *y, value *res)
{
  int kx, ky;
  for (;;) {
    kx = cur_node(x);
    ky = cur_node(y);
    if (kx < 0 || ky < 0) return 0;
    if (x->packed && y->packed) {
      if (x->m != y->m) r = x->m < y->m ? CMP_LT : CMP_GT;
      *res = r;
      return 1;
    }
    if (kx == POS_XH || ky == POS_XH) break;
    if (kx != ky) r = kx == POS_XI ? CMP_GT : CMP_LT;
    cur_next(x);
    cur_next(y);
  }
  if (kx == ky) {
    *res = r;
    return 1;
  }
  if (kx == POS_XH) {
    cur_next(y);
    if (!cur_closed(y)) return 0;
    *res = CMP_LT;
    return 1;
  }
  cur_next(x);
  if (!cur_closed(x)) return 0;
  *res = CMP_GT;
  return 1;
}

/* Pos.eqb p q {struct q}:
     p~1, q~1 -> eqb p q    p~0, q~0 -> eqb p q    1, 1 -> true    _ -> false
   The loop runs these steps on both numbers at once. After the first step
   that gives false, it still reads both numbers to their ends. When both
   cursors are in packed mode, the numbers are equal if their rests are. */
HOT int pos_eqb_core(struct cursor *x, struct cursor *y, value *res)
{
  int kx, ky, eq = 1;
  for (;;) {
    kx = cur_node(x);
    ky = cur_node(y);
    if (kx < 0 || ky < 0) return 0;
    if (x->packed && y->packed) {
      *res = eq && x->m == y->m ? BOOL_TRUE : BOOL_FALSE;
      return 1;
    }
    if (kx != ky) eq = 0;
    if (kx == POS_XH || ky == POS_XH) break;
    cur_next(x);
    cur_next(y);
  }
  if (kx != POS_XH) {
    cur_next(x);
    if (!cur_closed(x)) return 0;
  }
  if (ky != POS_XH) {
    cur_next(y);
    if (!cur_closed(y)) return 0;
  }
  *res = eq ? BOOL_TRUE : BOOL_FALSE;
  return 1;
}

/* Pos.succ x: succ (p~1) = (succ p)~0, succ (p~0) = p~1, succ 1 = 1~0.
   It reads the xI nodes at the bottom of x and the node above them: an xO
   of a chain, whose subterm the result shares, or the xH. A run of n xI
   over the rest m gives n xO over m + 1: from a packed rest the result is
   computed whole. */
HOT int pos_succ_core(struct cursor *c, int wrap, struct binnum_part *p)
{
  struct sink s = { 0, 0 };
  for (;;) {
    int k = cur_node(c);
    if (k < 0) return 0;
    if (c->packed) return part_sink_high(p, wrap, &s, c->m + 1);
    if (k == POS_XI) {
      if (!sink_put(&s, 0)) return 0;
      cur_next(c);
      continue;
    }
    if (k == POS_XO) {
      if (!sink_put(&s, 1)) return 0;
      cur_next(c);
      return part_sink(p, wrap, &s, c->arg, c->depth);
    }
    return part_sink_high(p, wrap, &s, 2);
  }
}

/* Pos.pred_double x: pred_double (p~1) = p~0~1, pred_double (p~0) =
   (pred_double p)~1, pred_double 1 = 1. It reads the xO nodes at the
   bottom of x and the node above them. A run of n xO over the rest m gives
   n xI over 2 m - 1: from a packed rest the result is computed whole. */
HOT int pos_pred_double_core(struct cursor *c, int wrap, struct binnum_part *p)
{
  struct sink s = { 0, 0 };
  for (;;) {
    int k = cur_node(c);
    if (k < 0) return 0;
    if (c->packed) return part_sink_high(p, wrap, &s, 2 * c->m - 1);
    if (k == POS_XO) {
      if (!sink_put(&s, 1)) return 0;
      cur_next(c);
      continue;
    }
    if (k == POS_XI) {
      if (!sink_put(&s, 1) || !sink_put(&s, 0)) return 0;
      cur_next(c);
      return part_sink(p, wrap, &s, c->arg, c->depth);
    }
    return part_sink_high(p, wrap, &s, 1);
  }
}

/* Pos.add x y + c (Pos.add_carry if c is 1), as the bytecode computes it:
   bit by bit while both numbers go on, reading the node of each at each
   step; when one of them ends, the rest of the other plus the carry, which
   is that rest unchanged (and shared) or its successor (as Pos.succ). When
   both rests are packed, or the rest to add to is packed, the result is
   computed whole from the numbers. */
HOT int pos_add_core(struct cursor *x, struct cursor *y, int c, int wrap,
                     struct binnum_part *p)
{
  struct sink s = { 0, 0 };
  int t;
  for (;;) {
    int kx = cur_node(x), ky = cur_node(y);
    if (kx < 0 || ky < 0) return 0;
    if (x->packed && y->packed) return part_sink_high(p, wrap, &s, x->m + y->m + c);
    if (kx != POS_XH && ky != POS_XH) {
      t = (kx == POS_XI) + (ky == POS_XI) + c;
      if (!sink_put(&s, t & 1)) return 0;
      c = t >> 1;
      cur_next(x);
      cur_next(y);
      continue;
    }
    if (kx == POS_XH && ky == POS_XH) return part_sink_high(p, wrap, &s, 2 + c);
    {
      struct cursor *o = kx == POS_XH ? y : x;
      int ko = kx == POS_XH ? ky : kx;
      /* The other number is 1: the rest of o plus 1 + c. */
      if (o->packed) return part_sink_high(p, wrap, &s, o->m + 1 + c);
      t = (ko == POS_XI) + 1 + c;
      if (!sink_put(&s, t & 1)) return 0;
      cur_next(o);
      if (!(t >> 1)) return part_sink(p, wrap, &s, o->arg, o->depth);
      /* The successor of the rest, as pos_succ_core, after these bits. */
      for (;;) {
        int k = cur_node(o);
        if (k < 0) return 0;
        if (o->packed) return part_sink_high(p, wrap, &s, o->m + 1);
        if (k == POS_XI) {
          if (!sink_put(&s, 0)) return 0;
          cur_next(o);
          continue;
        }
        if (k == POS_XO) {
          if (!sink_put(&s, 1)) return 0;
          cur_next(o);
          return part_sink(p, wrap, &s, o->arg, o->depth);
        }
        return part_sink_high(p, wrap, &s, 2);
      }
    }
  }
}

/* Pos.mul x y {struct x}: mul (p~1) y = add y (mul p y)~0,
   mul (p~0) y = (mul p y)~0, mul 1 y = y. It reads all of x. If x is a power
   of two, 2^t, the bytecode does not read y and the result is y below t xO
   nodes; otherwise the bytecode reads all of y (in add y _, whose second
   argument is longer), and so does the routine, and the result is computed
   whole. [y] is a cursor that the caller has set up and not read, unless it
   is already inside a packed block, which holds nothing to share. */
HOT int pos_mul_core(struct cursor *x, struct cursor *y, int wrap,
                     struct binnum_part *p)
{
  uint64_t wx = 0, wy = 0, prod, lx, ly;
  lx = read_pos(x, &wx, &num_a);
  if (lx == 0) return 0;
  if (lx <= 64 ? (wx & (wx - 1)) == 0 : num_is_pow2(&num_a)) {
    uint64_t t = lx - 1, j;
    struct sink s = { 0, 0 };
    for (j = 0; j < t; j++) if (!sink_put(&s, 0)) return 0;
    if (y->packed) return part_sink_high(p, wrap, &s, y->m);
    return part_sink(p, wrap, &s, y->arg, y->depth);
  }
  ly = read_pos(y, &wy, &num_b);
  if (ly == 0) return 0;
  if (lx <= 64 && ly <= 64 && !__builtin_mul_overflow(wx, wy, &prod))
    return part_word(p, prod, wrap);
  if (lx <= 64 && !num_set_u64(&num_a, wx)) return 0;
  if (ly <= 64 && !num_set_u64(&num_b, wy)) return 0;
  if (!num_mul(&num_r, &num_a, &num_b)) return 0;
  return part_num(p, &num_r, wrap);
}

/* Z.pos_sub x y: the Z x - y. It reads both numbers to their ends. */
HOT int pos_sub_core(struct cursor *x, struct cursor *y, struct binnum_part *p)
{
  uint64_t wx = 0, wy = 0, lx, ly;
  int c;
  lx = read_pos(x, &wx, &num_a);
  if (lx == 0) return 0;
  ly = read_pos(y, &wy, &num_b);
  if (ly == 0) return 0;
  if (lx <= 64 && ly <= 64) {
    if (wx == wy) {
      part_imm(p, Val_int(0));
      return 1;
    }
    return wx > wy ? part_word(p, wx - wy, Z_POS) : part_word(p, wy - wx, Z_NEG);
  }
  if (lx <= 64 && !num_set_u64(&num_a, wx)) return 0;
  if (ly <= 64 && !num_set_u64(&num_b, wy)) return 0;
  c = num_cmp(&num_a, &num_b);
  if (c == 0) {
    part_imm(p, Val_int(0));
    return 1;
  }
  if (!num_sub(&num_r, c > 0 ? &num_a : &num_b, c > 0 ? &num_b : &num_a)) return 0;
  return part_num(p, &num_r, c > 0 ? Z_POS : Z_NEG);
}

/* Z.compare x y, as the bytecode: the node of x, the node of y, and
   Pos.compare (compare_cont Eq) of their numbers when both have the same
   sign, through CompOpp when both are negative. */
HOT int z_compare_core(const value *a, value *res)
{
  struct cursor cx, cy;
  int kx, ky;
  value c;
  cur_init(&cx, a[0], 0, 0);
  kx = cur_node(&cx);
  if (kx < 0) return 0;
  cur_init(&cy, a[1], 1, 0);
  ky = cur_node(&cy);
  if (ky < 0) return 0;
  if (kx == Z_ZERO) {
    *res = ky == Z_ZERO ? CMP_EQ : ky == Z_POS ? CMP_LT : CMP_GT;
    return 1;
  }
  if (kx != ky) {
    *res = kx == Z_POS ? CMP_GT : CMP_LT;
    return 1;
  }
  cur_next(&cx);
  cur_next(&cy);
  if (!pos_compare_core(CMP_EQ, &cx, &cy, &c)) return 0;
  *res = kx == Z_POS ? c : c == CMP_LT ? CMP_GT : c == CMP_GT ? CMP_LT : CMP_EQ;
  return 1;
}

/** The routines: each reads its arguments [a] and sets the result R. */

static int r_pos_compare_cont(const value *a)
{
  value r = a[0], c;
  struct cursor x, y;
  COUNT(words, 1);
  if (r != CMP_EQ && r != CMP_LT && r != CMP_GT) return 0;
  cur_init(&x, a[1], 1, 0);
  cur_init(&y, a[2], 2, 0);
  if (!pos_compare_core(r, &x, &y, &c)) return 0;
  part_imm(&R.part[0], c);
  return 1;
}

static int r_pos_eqb(const value *a)
{
  value b;
  struct cursor x, y;
  cur_init(&x, a[0], 0, 0);
  cur_init(&y, a[1], 1, 0);
  if (!pos_eqb_core(&x, &y, &b)) return 0;
  part_imm(&R.part[0], b);
  return 1;
}

static int r_pos_succ(const value *a)
{
  struct cursor x;
  cur_init(&x, a[0], 0, 0);
  return pos_succ_core(&x, 0, &R.part[0]);
}

static int pos_add_routine(const value *a, int c)
{
  struct cursor x, y;
  cur_init(&x, a[0], 0, 0);
  cur_init(&y, a[1], 1, 0);
  return pos_add_core(&x, &y, c, 0, &R.part[0]);
}

static int r_pos_add(const value *a)
{
  return pos_add_routine(a, 0);
}

static int r_pos_add_carry(const value *a)
{
  return pos_add_routine(a, 1);
}

static int r_pos_pred_double(const value *a)
{
  struct cursor x;
  cur_init(&x, a[0], 0, 0);
  return pos_pred_double_core(&x, 0, &R.part[0]);
}

static int r_pos_mul(const value *a)
{
  struct cursor x, y;
  cur_init(&x, a[0], 0, 0);
  cur_init(&y, a[1], 1, 0);
  return pos_mul_core(&x, &y, 0, &R.part[0]);
}

/* Pos.div2 p: 1 for 1, and the number below the node of p otherwise: the
   subterm of a chain, or m >> 1 for a packed m. */
static int r_pos_div2(const value *a)
{
  struct cursor x;
  int k;
  cur_init(&x, a[0], 0, 0);
  k = cur_node(&x);
  if (k < 0) return 0;
  if (x.packed) return part_word(&R.part[0], x.m >> 1, 0);
  if (k == POS_XH) part_imm(&R.part[0], Val_int(0));
  else part_share(&R.part[0], 0, 0, 1);
  return 1;
}

/* Pos.of_succ_nat n: of_succ_nat O = 1, of_succ_nat (S x) = succ
   (of_succ_nat x). It reads all of n; the result is n + 1. */
static int r_pos_of_succ_nat(const value *a)
{
  struct cursor c;
  int64_t k;
  cur_init(&c, a[0], 0, 0);
  k = nat_length(&c);
  if (k < 0) return 0;
  return part_word(&R.part[0], (uint64_t)k + 1, 0);
}

/* Z.double, Z.succ_double, Z.pred_double: the node of x. On a Zpos or Zneg
   of a chain, the result shares the chain below one fresh node; of a packed
   p, it is computed whole (2 p or 2 p + 1). Z.succ_double of a Zneg and
   Z.pred_double of a Zpos run Pos.pred_double on the number. */
static int r_z_double(const value *a)
{
  struct cursor c;
  int k;
  cur_init(&c, a[0], 0, 0);
  k = cur_node(&c);
  if (k < 0) return 0;
  if (k == Z_ZERO) {
    part_imm(&R.part[0], Val_int(0));
    return 1;
  }
  cur_next(&c);
  if (!c.packed && binnum_is_packed(c.v)) cur_node(&c);
  if (c.packed) return part_word(&R.part[0], c.m << 1, k);
  {
    struct sink s = { 0, 1 };
    return part_sink(&R.part[0], k, &s, c.arg, c.depth);
  }
}

/* Z.succ_double and Z.pred_double on a Zpos and a Zneg: [k] is the sign
   that keeps the number, whose result is 2 p + 1. */
static int z_double_plus_one(const value *a, int k, int other)
{
  struct cursor c;
  int kz;
  cur_init(&c, a[0], 0, 0);
  kz = cur_node(&c);
  if (kz < 0) return 0;
  if (kz == Z_ZERO) return part_share(&R.part[0], k, BINNUM_BASE_XH, 0);
  cur_next(&c);
  if (kz != k) return pos_pred_double_core(&c, other, &R.part[0]);
  if (!c.packed && binnum_is_packed(c.v)) cur_node(&c);
  if (c.packed) return part_word(&R.part[0], (c.m << 1) + 1, k);
  {
    struct sink s = { 1, 1 };
    return part_sink(&R.part[0], k, &s, c.arg, c.depth);
  }
}

/* Z.succ_double: Z0 -> Zpos 1, Zpos p -> Zpos p~1,
   Zneg p -> Zneg (Pos.pred_double p). */
static int r_z_succ_double(const value *a)
{
  return z_double_plus_one(a, Z_POS, Z_NEG);
}

/* Z.pred_double: Z0 -> Zneg 1, Zneg p -> Zneg p~1,
   Zpos p -> Zpos (Pos.pred_double p). */
static int r_z_pred_double(const value *a)
{
  return z_double_plus_one(a, Z_NEG, Z_POS);
}

static int r_z_pos_sub(const value *a)
{
  struct cursor x, y;
  cur_init(&x, a[0], 0, 0);
  cur_init(&y, a[1], 1, 0);
  return pos_sub_core(&x, &y, &R.part[0]);
}

/* Z.add x y: x = 0 gives y and y = 0 gives x, unread; numbers of the same
   sign are added as Pos.add; of opposite signs, subtracted as Z.pos_sub. */
static int r_z_add(const value *a)
{
  struct cursor x, y;
  int kx, ky;
  cur_init(&x, a[0], 0, 0);
  kx = cur_node(&x);
  if (kx < 0) return 0;
  if (kx == Z_ZERO) return part_share(&R.part[0], 0, 1, 0);
  cur_init(&y, a[1], 1, 0);
  ky = cur_node(&y);
  if (ky < 0) return 0;
  if (ky == Z_ZERO) return part_share(&R.part[0], 0, 0, 0);
  cur_next(&x);
  cur_next(&y);
  if (kx == ky) return pos_add_core(&x, &y, 0, kx, &R.part[0]);
  if (kx == Z_POS) return pos_sub_core(&x, &y, &R.part[0]);
  return pos_sub_core(&y, &x, &R.part[0]);
}

static int r_z_mul(const value *a)
{
  struct cursor x, y;
  int kx, ky;
  cur_init(&x, a[0], 0, 0);
  kx = cur_node(&x);
  if (kx < 0) return 0;
  if (kx == Z_ZERO) {
    part_imm(&R.part[0], Val_int(0));
    return 1;
  }
  cur_init(&y, a[1], 1, 0);
  ky = cur_node(&y);
  if (ky < 0) return 0;
  if (ky == Z_ZERO) {
    part_imm(&R.part[0], Val_int(0));
    return 1;
  }
  cur_next(&x);
  cur_next(&y);
  return pos_mul_core(&x, &y, kx == ky ? Z_POS : Z_NEG, &R.part[0]);
}

static int r_z_compare(const value *a)
{
  value c;
  if (!z_compare_core(a, &c)) return 0;
  part_imm(&R.part[0], c);
  return 1;
}

/* Z.leb: true unless Gt; Z.ltb: true if Lt. */
static int r_z_leb(const value *a)
{
  value c;
  if (!z_compare_core(a, &c)) return 0;
  part_imm(&R.part[0], c == CMP_GT ? BOOL_FALSE : BOOL_TRUE);
  return 1;
}

static int r_z_ltb(const value *a)
{
  value c;
  if (!z_compare_core(a, &c)) return 0;
  part_imm(&R.part[0], c == CMP_LT ? BOOL_TRUE : BOOL_FALSE);
  return 1;
}

/* Z.eqb x y: the node of x and of y, and Pos.eqb of their numbers when both
   have the same sign. */
static int r_z_eqb(const value *a)
{
  struct cursor x, y;
  int kx, ky;
  value b;
  cur_init(&x, a[0], 0, 0);
  kx = cur_node(&x);
  if (kx < 0) return 0;
  cur_init(&y, a[1], 1, 0);
  ky = cur_node(&y);
  if (ky < 0) return 0;
  if (kx == Z_ZERO || kx != ky) b = kx == ky ? BOOL_TRUE : BOOL_FALSE;
  else {
    cur_next(&x);
    cur_next(&y);
    if (!pos_eqb_core(&x, &y, &b)) return 0;
  }
  part_imm(&R.part[0], b);
  return 1;
}

/* Z.div2 z: Z0 -> Z0; Zpos p -> Z0 if p is 1, else Zpos (Pos.div2 p), the
   number below the node of p; Zneg p -> Zneg (Pos.div2_up p), where
   div2_up (p~1) = succ p, div2_up (p~0) = p, div2_up 1 = 1. For a packed
   p = m, Pos.div2 p is m >> 1 and div2_up p is (m + 1) >> 1. The node is
   tested before the rest, because a packed rest of 1 is the node xH, whose
   Pos.div2 is 1 and not m >> 1 = 0. */
HOT int z_div2_core(int kz, struct cursor *c)
{
  int kp = cur_node(c);
  if (kp < 0) return 0;
  if (kz == Z_POS) {
    if (kp == POS_XH) {
      part_imm(&R.part[0], Val_int(0));
      return 1;
    }
    if (c->packed) return part_word(&R.part[0], c->m >> 1, Z_POS);
    part_share(&R.part[0], Z_POS, c->arg, c->depth + 1);
    return 1;
  }
  if (kp == POS_XH) return part_share(&R.part[0], Z_NEG, BINNUM_BASE_XH, 0);
  if (c->packed) return part_word(&R.part[0], (c->m + 1) >> 1, Z_NEG);
  if (kp == POS_XO) return part_share(&R.part[0], Z_NEG, c->arg, c->depth + 1);
  cur_next(c);
  return pos_succ_core(c, Z_NEG, &R.part[0]);
}

static int r_z_div2(const value *a)
{
  struct cursor c;
  int kz;
  cur_init(&c, a[0], 0, 0);
  kz = cur_node(&c);
  if (kz < 0) return 0;
  if (kz == Z_ZERO) {
    part_imm(&R.part[0], Val_int(0));
    return 1;
  }
  cur_next(&c);
  return z_div2_core(kz, &c);
}

/* Z.of_nat n: O -> Z0, S n0 -> Zpos (of_succ_nat n0), that is Zpos n. */
static int r_z_of_nat(const value *a)
{
  struct cursor c;
  int64_t k;
  cur_init(&c, a[0], 0, 0);
  k = nat_length(&c);
  if (k < 0) return 0;
  return part_z_word(&R.part[0], (uint64_t)k);
}

/* Z.pos_div_eucl a b: for b > 0, the pair (a / b, a mod b) (by induction on
   a, the body keeps a = q b + r with 0 <= r < b). The routine refuses
   b <= 0, which the bytecode then computes. */
static int r_z_pos_div_eucl(const value *a)
{
  uint64_t wa = 0, wb = 0, la, lb;
  struct cursor ca, cb;
  cur_init(&ca, a[0], 0, 0);
  la = read_pos(&ca, &wa, &num_a);
  if (la == 0) return 0;
  cur_init(&cb, a[1], 1, 0);
  if (cur_node(&cb) != Z_POS) return 0;
  cur_next(&cb);
  lb = read_pos(&cb, &wb, &num_b);
  if (lb == 0) return 0;
  R.nparts = 2;
  if (la <= 64 && lb <= 64)
    return part_z_word(&R.part[0], wa / wb) && part_z_word(&R.part[1], wa % wb);
  if (la <= 64 && !num_set_u64(&num_a, wa)) return 0;
  if (lb <= 64 && !num_set_u64(&num_b, wb)) return 0;
  if (!num_divmod(&num_q, &num_m, &num_a, &num_b)) return 0;
  return part_z_num(&R.part[0], &num_q) && part_z_num(&R.part[1], &num_m);
}

/* Nat.eqb n m {struct n}: both O -> true; one O -> false; S n', S m' ->
   eqb n' m'. It reads the node of n, then of m, at each step. */
static int r_nat_eqb(const value *a)
{
  struct cursor x, y;
  cur_init(&x, a[0], 0, 0);
  cur_init(&y, a[1], 1, 0);
  for (;;) {
    int kn = cur_node_nat(&x), km;
    if (kn < 0) return 0;
    km = cur_node_nat(&y);
    if (km < 0) return 0;
    if (kn == POS_XH || km == POS_XH) {
      part_imm(&R.part[0], kn == km ? BOOL_TRUE : BOOL_FALSE);
      return 1;
    }
    if (x.packed && y.packed) {
      int64_t ln = nat_packed_length(x.m), lm = nat_packed_length(y.m);
      if (ln < 0 || lm < 0) return 0;
      part_imm(&R.part[0], ln == lm ? BOOL_TRUE : BOOL_FALSE);
      return 1;
    }
    cur_next(&x);
    cur_next(&y);
  }
}

/* Nat.leb n m {struct n}: O, _ -> true (m unread); S _, O -> false;
   S n', S m' -> leb n' m'. */
static int r_nat_leb(const value *a)
{
  struct cursor x, y;
  cur_init(&x, a[0], 0, 0);
  cur_init(&y, a[1], 1, 0);
  for (;;) {
    int kn = cur_node_nat(&x), km;
    if (kn < 0) return 0;
    if (kn == POS_XH) {
      part_imm(&R.part[0], BOOL_TRUE);
      return 1;
    }
    km = cur_node_nat(&y);
    if (km < 0) return 0;
    if (km == POS_XH) {
      part_imm(&R.part[0], BOOL_FALSE);
      return 1;
    }
    if (x.packed && y.packed) {
      int64_t ln = nat_packed_length(x.m), lm = nat_packed_length(y.m);
      if (ln < 0 || lm < 0) return 0;
      part_imm(&R.part[0], ln <= lm ? BOOL_TRUE : BOOL_FALSE);
      return 1;
    }
    cur_next(&x);
    cur_next(&y);
  }
}

/** The conversions between primitive 63-bit integers and binary numbers
    (Corelib.Numbers.Cyclic.Int63.Uint63Axioms), and Z.pow.

    On a 64-bit build a closed primitive integer is the immediate Val_long
    of its value (rocq_uint63_native.h:11-14: Is_uint63 is Is_long, and
    uint63_of_value is the value shifted right by one). That header defines
    functions that are not static, so including it here would define them
    twice in one program; the three macros below are its two definitions
    and their inverse, for this file alone.

    On a 32-bit build a primitive integer is a custom block
    (rocq_uint63_emul.h:17), which these two routines do not read: their
    table entries stay, because the table is append only, and every call is
    refused. */
#ifdef ARCH_SIXTYFOUR

#define BINNUM_IS_UINT63(v) Is_long(v)
#define BINNUM_UINT63_OF_VALUE(v) (((uint64_t)(v)) >> 1)
#define BINNUM_UINT63_TO_VALUE(n) ((value)((((uint64_t)(n)) << 1) | 1))
#define BINNUM_UINT63_MASK ((((uint64_t)1) << 63) - 1)

/* Uint63Axioms.to_Z_rec n i {struct n}: O -> Z0; S n0 -> (if is_even i
   then IntDef.Z.double else IntDef.Z.succ_double) (to_Z_rec n0 (lsr i 1)).
   It reads n down to O, as the bytecode does, and reads i only where the
   bytecode does, that is where n is not O. Each level takes the lowest bit
   of i and shifts i right, and lsr shifts in zeros, so the result is the Z
   of i mod 2^k for k the length of n, which is i itself for k >= 63. */
static int r_uint63_to_Z_rec(const value *a)
{
  struct cursor c;
  int64_t k;
  uint64_t i;
  cur_init(&c, a[0], 0, 0);
  k = nat_length(&c);
  if (k < 0) return 0;
  if (k == 0) {
    part_imm(&R.part[0], Val_int(0));
    return 1;
  }
  if (!BINNUM_IS_UINT63(a[1])) return 0;
  i = BINNUM_UINT63_OF_VALUE(a[1]);
  if (k < 63) i &= ((uint64_t)1 << k) - 1;
  return part_z_word(&R.part[0], i);
}

/* Uint63Axioms.of_pos_rec n p {struct p}: O -> 0; S n0 -> (xI p0 ->
   lor (lsl (of_pos_rec n0 p0) 1) 1; xO p0 -> lsl (of_pos_rec n0 p0) 1;
   xH -> 1).

   The fixpoint is structural on p, so the bytecode needs the node of p at
   every level, even at the level where n is O and the body does not look at
   p: of_pos_rec 2 (xO (xO q)) with q an accumulator is a stuck term. The
   routine therefore reads the node of p and then the node of n at each
   level, and stops at the first O of n or xH of p. Below that level the
   value is 0 (for O) or 1 (for xH); above it, each level shifts left by one
   and adds its bit. lsl drops the bits above 63, so the value is
   p mod 2^min(length of n, bits of p, 63). */
static int r_uint63_of_pos_rec(const value *a)
{
  struct cursor cn, cp;
  uint64_t bits = 0, t = 0, term, v;
  cur_init(&cn, a[0], 0, 0);
  cur_init(&cp, a[1], 1, 0);
  for (;;) {
    int kp = cur_node(&cp), kn;
    if (kp < 0) return 0;
    kn = cur_node_nat(&cn);
    if (kn < 0) return 0;
    if (kn == POS_XH) { term = 0; break; }
    if (kp == POS_XH) { term = 1; break; }
    if (cn.packed && cp.packed) {
      /* Both rests are numbers: the levels below cost nothing. */
      int64_t rest = nat_packed_length(cn.m);
      uint64_t k;
      if (rest < 0) return 0;
      k = (uint64_t) rest;
      if (k > 63) k = 63;
      term = k >= binnum_bitlen(cp.m) ? cp.m : cp.m & (((uint64_t)1 << k) - 1);
      break;
    }
    if (kp == POS_XI && t < 63) bits |= (uint64_t)1 << t;
    t++;
    cur_next(&cn);
    cur_next(&cp);
  }
  v = t >= 63 ? bits : (term << t | bits);
  part_imm(&R.part[0], BINNUM_UINT63_TO_VALUE(v & BINNUM_UINT63_MASK));
  return 1;
}

#else

static int r_uint63_to_Z_rec(const value *a)
{
  (void) a;
  return 0;
}

static int r_uint63_of_pos_rec(const value *a)
{
  (void) a;
  return 0;
}

#endif /* ARCH_SIXTYFOUR */

/* The largest result of Z.pow, in bits. */
#define BINNUM_POW_BITS 4096

/* Z.pow x y: Z0 -> 1 and Zneg _ -> 0, both with x unread, as the bytecode
   leaves it; Zpos p -> Z.pow_pos x p, that is Pos.iter (Z.mul x) 1 p, which
   applies the multiplication by x exactly p times to 1, whatever order the
   calls nest in, and so is x^p. The bytecode reads p to its end and x at
   every one of those multiplications, and so does the routine.

   One call allocates at most BINNUM_POW_BITS bits. With b the bits of |x|,
   the result has at most b p bits, so the routine refuses b p larger than
   BINNUM_POW_BITS, and it stops reading p as soon as p is larger. For
   1 <= p <= BINNUM_POW_BITS, the test b > BINNUM_POW_BITS / p is exactly
   b p > BINNUM_POW_BITS, with no product to overflow; it also refuses
   b > BINNUM_POW_BITS with p >= 2. */
static int r_z_pow(const value *a)
{
  struct cursor cx, cy;
  int kx, ky, sign;
  uint64_t p = 0, wx = 0, b;
  cur_init(&cy, a[1], 1, 0);
  ky = cur_node(&cy);
  if (ky < 0) return 0;
  if (ky == Z_NEG) {
    part_imm(&R.part[0], Val_int(0));
    return 1;
  }
  if (ky == Z_ZERO) return part_word(&R.part[0], 1, Z_POS);
  cur_next(&cy);
  if (!read_pos_small(&cy, BINNUM_POW_BITS, &p)) return 0;
  cur_init(&cx, a[0], 0, 0);
  kx = cur_node(&cx);
  if (kx < 0) return 0;
  if (kx == Z_ZERO) {
    part_imm(&R.part[0], Val_int(0));
    return 1;
  }
  cur_next(&cx);
  b = read_pos(&cx, &wx, &num_a);
  if (b == 0) return 0;
  if (b > BINNUM_POW_BITS / p) return 0;
  sign = kx == Z_NEG && (p & 1) ? Z_NEG : Z_POS;
  if (b <= 64 && !num_set_u64(&num_a, wx)) return 0;
  if (!num_pow(&num_a, p)) return 0;
  return part_num(&R.part[0], &num_r, sign);
}

typedef int (*binnum_fn)(const value *);

static const binnum_fn binnum_fns[BINNUM_COUNT] = {
  r_pos_compare_cont, r_pos_eqb, r_pos_succ, r_pos_add, r_pos_add_carry,
  r_pos_pred_double, r_pos_mul, r_pos_div2, r_pos_of_succ_nat,
  r_z_double, r_z_succ_double, r_z_pred_double, r_z_pos_sub, r_z_add, r_z_mul,
  r_z_compare, r_z_leb, r_z_ltb, r_z_eqb, r_z_div2, r_z_of_nat, r_z_pos_div_eucl,
  r_nat_eqb, r_nat_leb,
  r_uint63_to_Z_rec, r_uint63_of_pos_rec, r_z_pow
};

static void count_call(int k, int site, int ok)
{
  int p;
  site = site != 0;
  binnum_calls[site][k]++;
  binnum_words[site][k] += R.words;
  if (!ok) binnum_refusals[site][k]++;
  binnum_args[k] += R.args;
  binnum_args_packed[k] += R.args_packed;
  binnum_args_tail[k] += R.args_tail;
  if (ok)
    for (p = 0; p < R.nparts; p++)
      if (R.part[p].kind == BINNUM_CHAIN && R.part[p].base_arg == BINNUM_BASE_PACKED
          && R.part[p].nnodes == 0)
        binnum_packed_results[k]++;
}

const struct binnum_result *rocq_binnum_run(int k, int n, const value *args, int site)
{
  int ok;
  if ((unsigned)k >= BINNUM_COUNT || n != binnum_arity[k]) return NULL;
  R.nparts = 1;
  if (rocq_binnum_stats) {
    R.words = 0;
    R.args = R.args_packed = R.args_tail = 0;
  }
  ok = binnum_fns[k](args);
  if (rocq_binnum_stats) count_call(k, site, ok);
  return ok ? &R : NULL;
}

void rocq_binnum_count_expansion(int where, uint64_t nodes)
{
  if (rocq_binnum_stats) {
    if (where < 0 || where > 2) abort();
    binnum_expansions[where]++;
    binnum_expansion_nodes[where] += nodes;
  }
}

/* The chain of the packed block v, for whd_val (kernel/vmvalues.ml): the
   chain it keeps when it has one, and otherwise a fresh head, a block of
   tag 1 or 2, as SWITCH builds it. The block itself is not changed. */
value rocq_binnum_expand(value v)
{
  CAMLparam1(v);
  CAMLlocal2(res, block);
  uint64_t n = binnum_packed_number(v);
  value kept = binnum_packed_chain(v);
  unsigned i, nodes;
  if (kept != 0) CAMLreturn(kept);
  nodes = binnum_bitlen(n) - 1;
  res = Val_int(0);
  for (i = nodes; i-- > 0;) {
    block = caml_alloc_small(1, BINNUM_NODE_TAG(n, i));
    Field(block, 0) = res;
    res = block;
  }
  rocq_binnum_count_expansion(1, nodes);
  CAMLreturn(res);
}

/* Packs the chain v into a block of tag BINNUM_PACKED_TAG and size 2 whose
   field 1 is v itself. It returns v unchanged when v is not a chain of 1 to
   61 nodes, or when the packing of literals is off.
   Vmvalues.val_of_str_const calls it on the subterms of the VM value of a
   structured constant (Const_val alone), from the outside in, so v never
   holds a packed block.

   The number is derived with the cursor that the routines read with, and
   the expansion of that number is then compared with the chain, node by
   node. Fields 0 and 1 that disagreed would make the routines (which read
   field 0) and the bytecode (which reads field 1) compute different values,
   so a disagreement stops the process. Structured constants are cached
   (Vmsymtable.slot_for_str_cst), so this runs once per literal. */
value rocq_binnum_pack_literal(value v)
{
  CAMLparam1(v);
  CAMLlocal1(res);
  uint64_t n = 0, i = 0, j;
  value w;
  int saved;
  if (!binnum_packlit || !Is_block(v)) CAMLreturn(v);
  /* The nodes this reads belong to no routine call, so they are not counted
     as the words of one. */
  saved = rocq_binnum_stats;
  rocq_binnum_stats = 0;
  {
    struct cursor c;
    cur_init(&c, v, 0, 0);
    for (;;) {
      int k = cur_node(&c);
      if (k < 0 || c.packed) { i = 0; break; }
      if (k == POS_XH) break;
      if (k == POS_XI) n |= (uint64_t)1 << i;
      i++;
      if (i > 61) { i = 0; break; }
      cur_next(&c);
    }
  }
  rocq_binnum_stats = saved;
  if (i == 0) CAMLreturn(v);
  n |= (uint64_t)1 << i;
  w = v;
  for (j = 0; j < i; j++) {
    if (!Is_block(w) || Wosize_val(w) != 1 || Tag_val(w) != BINNUM_NODE_TAG(n, j))
      abort();
    w = Field(w, 0);
  }
  if (w != Val_int(0)) abort();
  res = caml_alloc_small(2, BINNUM_PACKED_TAG);
  Field(res, 0) = Val_long(n);
  Field(res, 1) = v;
  if (rocq_binnum_stats) {
    binnum_literals++;
    binnum_literal_nodes += i;
  }
  CAMLreturn(res);
}

value rocq_binnum_arities(value unit)
{
  CAMLparam1(unit);
  CAMLlocal1(res);
  int k;
  res = caml_alloc(BINNUM_COUNT, 0);
  for (k = 0; k < BINNUM_COUNT; k++) Store_field(res, k, Val_int(binnum_arity[k]));
  CAMLreturn(res);
}

value rocq_binnum_set_stats(value on)
{
  rocq_binnum_stats = Bool_val(on);
  return Val_unit;
}

value rocq_binnum_set_pack(value on)
{
  binnum_pack = ROCQ_BINNUM_PACKING && Bool_val(on);
  return Val_unit;
}

value rocq_binnum_set_packlit(value on)
{
  binnum_packlit = ROCQ_BINNUM_PACKING && Bool_val(on);
  return Val_unit;
}

/* Of each routine, in routine order: [entry calls; entry refusals; entry
   words; site calls; site refusals; site words; arguments; packed
   arguments; arguments with a packed tail; packed results]; then [SWITCH
   expansions; their nodes; whd_val expansions; their nodes; PROJ
   expansions; their nodes; literals packed; their nodes; packing of
   results; packing of literals]. */
#define BINNUM_ROUTINE_COUNTERS 10
#define BINNUM_TAIL_COUNTERS 10

value rocq_binnum_counters(value unit)
{
  CAMLparam1(unit);
  CAMLlocal1(res);
  int k, s, b;
  res = caml_alloc(BINNUM_ROUTINE_COUNTERS * BINNUM_COUNT + BINNUM_TAIL_COUNTERS, 0);
  for (k = 0; k < BINNUM_COUNT; k++) {
    b = BINNUM_ROUTINE_COUNTERS * k;
    for (s = 0; s < 2; s++) {
      Store_field(res, b + 3 * s, Val_long(binnum_calls[s][k]));
      Store_field(res, b + 3 * s + 1, Val_long(binnum_refusals[s][k]));
      Store_field(res, b + 3 * s + 2, Val_long(binnum_words[s][k]));
    }
    Store_field(res, b + 6, Val_long(binnum_args[k]));
    Store_field(res, b + 7, Val_long(binnum_args_packed[k]));
    Store_field(res, b + 8, Val_long(binnum_args_tail[k]));
    Store_field(res, b + 9, Val_long(binnum_packed_results[k]));
  }
  b = BINNUM_ROUTINE_COUNTERS * BINNUM_COUNT;
  for (s = 0; s < 3; s++) {
    Store_field(res, b + 2 * s, Val_long(binnum_expansions[s]));
    Store_field(res, b + 2 * s + 1, Val_long(binnum_expansion_nodes[s]));
  }
  Store_field(res, b + 6, Val_long(binnum_literals));
  Store_field(res, b + 7, Val_long(binnum_literal_nodes));
  Store_field(res, b + 8, Val_long(binnum_pack));
  Store_field(res, b + 9, Val_long(binnum_packlit));
  CAMLreturn(res);
}

value rocq_binnum_reset_counters(value unit)
{
  int k, s;
  for (k = 0; k < BINNUM_COUNT; k++) {
    for (s = 0; s < 2; s++) {
      binnum_calls[s][k] = 0;
      binnum_refusals[s][k] = 0;
      binnum_words[s][k] = 0;
    }
    binnum_args[k] = 0;
    binnum_args_packed[k] = 0;
    binnum_args_tail[k] = 0;
    binnum_packed_results[k] = 0;
  }
  for (s = 0; s < 3; s++) {
    binnum_expansions[s] = 0;
    binnum_expansion_nodes[s] = 0;
  }
  binnum_literals = 0;
  binnum_literal_nodes = 0;
  return Val_unit;
}
