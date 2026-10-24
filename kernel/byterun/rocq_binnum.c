/************************************************************************/
/*         *      The Rocq Prover / The Rocq Development Team           */
/*  v      *         Copyright INRIA, CNRS and contributors             */
/* <O___,, * (see version control and CREDITS file for authors & dates) */
/*   \VV/  **************************************************************/
/*    //   *    This file is distributed under the terms of the         */
/*         *     GNU Lesser General Public License Version 2.1          */
/*         *     (see LICENSE file for the text of the license)         */
/************************************************************************/

/* The routines of the BINNUM instruction.

   Each routine computes what its reference term in kernel/vmbinnum.ml
   computes. The arguments are trees of constructor values with the VM
   representation that vmbinnum.ml checks on the inductive types (the
   [mind_reloc_tbl] of kernel/indtypes.ml). A routine reads at least the
   nodes that the bytecode of the reference reads, in the order the bytecode
   reads them, and stops at the first node that is not a constructor of the
   expected type, such as an accumulator: it then refuses the call, and the
   bytecode of the function runs as if the instruction were not there. The
   nodes that it does not read are those that the bytecode does not read
   either, and the bytecode's result holds them unchanged; so does the
   routine's, which takes them from the argument.

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
  BINNUM_COUNT
};

static const int binnum_arity[BINNUM_COUNT] = {
  3, 2, 1, 2, 2, 1, 2, 1, 1,
  1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 1, 2,
  2, 2
};

/* Counters, printed by vmbinnum.ml when ROCQ_VM_BINNUM_STATS is set: the
   calls of each routine, the calls it refused, and the nodes it read (in
   accepted and refused calls). */
static uint64_t binnum_calls[BINNUM_COUNT];
static uint64_t binnum_refusals[BINNUM_COUNT];
static uint64_t binnum_words[BINNUM_COUNT];

/* comparison: Eq | Lt | Gt, three constant constructors. */
#define CMP_EQ Val_int(0)
#define CMP_LT Val_int(1)
#define CMP_GT Val_int(2)

/* bool: true | false, two constant constructors. */
#define BOOL_TRUE Val_int(0)
#define BOOL_FALSE Val_int(1)

/* A node of a positive. xI and xO are the blocks of tag 1 and 2 with one
   field, xH is the constant Val_int(0). The result is the tag for xI and
   xO, 0 for xH, and -1 for any other value, such as an accumulator. */
#define POS_XH 0
#define POS_XI 1
#define POS_XO 2

static inline int pos_node(value v)
{
  if (Is_long(v)) return v == Val_int(0) ? POS_XH : -1;
  if (Wosize_val(v) != 1) return -1;
  if (Tag_val(v) == POS_XI) return POS_XI;
  if (Tag_val(v) == POS_XO) return POS_XO;
  return -1;
}

/* A node of a Z: Z0 is Val_int(0), Zpos and Zneg the blocks of tag 1 and 2
   with one field (a positive). */
#define Z_ZERO 0
#define Z_POS 1
#define Z_NEG 2

static inline int z_node(value v)
{
  if (Is_long(v)) return v == Val_int(0) ? Z_ZERO : -1;
  if (Wosize_val(v) != 1) return -1;
  if (Tag_val(v) == Z_POS) return Z_POS;
  if (Tag_val(v) == Z_NEG) return Z_NEG;
  return -1;
}

/* A node of a nat: O is Val_int(0), S the block of tag 1 with one field. 0
   for O, 1 for S, -1 for any other value. */
static inline int nat_node(value v)
{
  if (Is_long(v)) return v == Val_int(0) ? 0 : -1;
  return Wosize_val(v) == 1 && Tag_val(v) == 1 ? 1 : -1;
}

/* Reads the rest of a positive. Returns 1 if it is closed. */
static int pos_closed(value v, uint64_t *words)
{
  uint64_t n = 0;
  int k;
  while ((k = pos_node(v)) > 0) {
    n++;
    v = Field(v, 0);
  }
  *words += n + 1;
  return k == POS_XH;
}

/** Numbers, in C buffers: little-endian arrays of 32-bit limbs. A number is
    normalized when its top limb is not zero (zero has no limb). The same
    type holds the bits of a chain of fresh nodes. The buffers are static and
    grow as needed; a routine whose buffer cannot grow refuses the call. */

typedef uint32_t limb;

struct num { limb *d; size_t n; size_t cap; };

static struct num num_a, num_b, num_r, num_q, num_m;

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

/* Reads the positive v to its end into x. 0 if one of its nodes is not a
   constructor of positive. */
static int read_pos(value v, struct num *x, uint64_t *words)
{
  uint64_t i = 0;
  for (;;) {
    int k = pos_node(v);
    (*words)++;
    if (k < 0) return 0;
    if (!bits_put(x, i, k != POS_XO)) return 0;
    if (k == POS_XH) {
      x->n = (size_t)(i >> 5) + 1;
      return 1;
    }
    v = Field(v, 0);
    i++;
  }
}

/** Results */

static void part_imm(struct binnum_part *p, value v)
{
  p->kind = BINNUM_IMM;
  p->imm = v;
}

static int part_chain(struct binnum_part *p, int wrap, const struct num *bits,
                      uint64_t nnodes, int arg, uint64_t depth)
{
  p->kind = BINNUM_CHAIN;
  p->imm = Val_unit;
  p->wrap = wrap;
  p->bits = bits == NULL ? NULL : bits->d;
  p->nnodes = nnodes;
  p->base_arg = arg;
  p->base_depth = depth;
  return 1;
}

/* The positive x > 0, fresh, wrapped in a block of tag [wrap] if not 0. */
static void part_pos(struct binnum_part *p, const struct num *x, int wrap)
{
  part_chain(p, wrap, x, num_bitlen(x) - 1, -1, 0);
}

/* The Z of magnitude x and sign [sign] (Z_POS or Z_NEG). */
static void part_z(struct binnum_part *p, const struct num *x, int sign)
{
  if (x->n == 0) part_imm(p, Val_int(0));
  else part_pos(p, x, sign);
}

/* A positive within the arguments: the value v, which is the subterm of
   argument [arg] at [depth] steps through field 0. */
struct operand { value v; int arg; uint64_t depth; };

static struct operand operand(value v, int arg, uint64_t depth)
{
  struct operand o;
  o.v = v;
  o.arg = arg;
  o.depth = depth;
  return o;
}

/** Positive numbers */

/* Pos.compare_cont r x y {struct y}:
     x~1, y~1 -> compare_cont r x y      x~0, y~1 -> compare_cont Lt x y
     x~1, y~0 -> compare_cont Gt x y     x~0, y~0 -> compare_cont r x y
     x~1, 1   -> Gt                      x~0, 1   -> Gt
     1,   y~1 -> Lt     1, y~0 -> Lt     1,   1   -> r
   The loop runs these steps on both numbers at once, from their outermost
   constructors; r is the result if both end together. It reads both numbers
   to their ends. */
static int pos_compare_core(value r, value x, value y, value *res, uint64_t *words)
{
  uint64_t n = 0;
  int kx, ky, ok = 0;
  for (;;) {
    kx = pos_node(x);
    ky = pos_node(y);
    n += 2;
    if (kx < 0 || ky < 0) goto done;
    if (kx == POS_XH || ky == POS_XH) break;
    if (kx != ky) r = kx == POS_XI ? CMP_GT : CMP_LT;
    x = Field(x, 0);
    y = Field(y, 0);
  }
  if (kx == ky) {
    *res = r;
    ok = 1;
  } else if (kx == POS_XH) {
    ok = pos_closed(Field(y, 0), &n);
    *res = CMP_LT;
  } else {
    ok = pos_closed(Field(x, 0), &n);
    *res = CMP_GT;
  }
 done:
  *words += n;
  return ok;
}

/* Pos.eqb p q {struct q}:
     p~1, q~1 -> eqb p q    p~0, q~0 -> eqb p q    1, 1 -> true    _ -> false
   The loop runs these steps on both numbers at once. After the first step
   that gives false, it still reads both numbers to their ends. */
static int pos_eqb_core(value x, value y, value *res, uint64_t *words)
{
  uint64_t n = 0;
  int kx, ky, eq = 1, ok = 0;
  for (;;) {
    kx = pos_node(x);
    ky = pos_node(y);
    n += 2;
    if (kx < 0 || ky < 0) goto done;
    if (kx != ky) eq = 0;
    if (kx == POS_XH || ky == POS_XH) break;
    x = Field(x, 0);
    y = Field(y, 0);
  }
  if (kx != POS_XH && !pos_closed(Field(x, 0), &n)) goto done;
  if (ky != POS_XH && !pos_closed(Field(y, 0), &n)) goto done;
  *res = eq ? BOOL_TRUE : BOOL_FALSE;
  ok = 1;
 done:
  *words += n;
  return ok;
}

/* Pos.succ x: succ (p~1) = (succ p)~0, succ (p~0) = p~1, succ 1 = 1~0.
   It reads the xI nodes at the bottom of x and the node above them: an xO,
   whose subterm the result shares, or the xH. */
static int pos_succ_core(struct operand x, int wrap, struct binnum_part *p, uint64_t *w)
{
  struct num *f = &num_r;
  uint64_t i = 0;
  value v = x.v;
  for (;;) {
    int k = pos_node(v);
    (*w)++;
    if (k < 0) return 0;
    if (k == POS_XI) {
      if (!bits_put(f, i, 0)) return 0;
      i++;
      v = Field(v, 0);
      continue;
    }
    if (k == POS_XO) {
      if (!bits_put(f, i, 1)) return 0;
      i++;
      return part_chain(p, wrap, f, i, x.arg, x.depth + i);
    }
    if (!bits_put(f, i, 0)) return 0;
    return part_chain(p, wrap, f, i + 1, -1, 0);
  }
}

/* Pos.pred_double x: pred_double (p~1) = p~0~1, pred_double (p~0) =
   (pred_double p)~1, pred_double 1 = 1. It reads the xO nodes at the
   bottom of x and the node above them. */
static int pos_pred_double_core(struct operand x, int wrap, struct binnum_part *p, uint64_t *w)
{
  struct num *f = &num_r;
  uint64_t i = 0;
  value v = x.v;
  for (;;) {
    int k = pos_node(v);
    (*w)++;
    if (k < 0) return 0;
    if (k == POS_XO) {
      if (!bits_put(f, i, 1)) return 0;
      i++;
      v = Field(v, 0);
      continue;
    }
    if (k == POS_XI) {
      uint64_t depth = x.depth + i + 1;
      if (!bits_put(f, i, 1) || !bits_put(f, i + 1, 0)) return 0;
      return part_chain(p, wrap, f, i + 2, x.arg, depth);
    }
    return part_chain(p, wrap, f, i, -1, 0);
  }
}

/* Pos.add x y + c (Pos.add_carry if c is 1), as the bytecode computes it:
   bit by bit while both numbers go on, reading the node of each at each
   step; when one of them ends, the rest of the other plus the carry, which
   is that rest unchanged (and shared) or its successor (as Pos.succ). */
static int pos_add_core(struct operand x, struct operand y, int c, int wrap,
                        struct binnum_part *p, uint64_t *w)
{
  struct num *f = &num_r;
  uint64_t i = 0;
  for (;;) {
    int kx = pos_node(x.v), ky = pos_node(y.v), s;
    *w += 2;
    if (kx < 0 || ky < 0) return 0;
    if (kx != POS_XH && ky != POS_XH) {
      s = (kx == POS_XI) + (ky == POS_XI) + c;
      if (!bits_put(f, i, s & 1)) return 0;
      c = s >> 1;
      i++;
      x.v = Field(x.v, 0);
      y.v = Field(y.v, 0);
      continue;
    }
    if (kx == POS_XH && ky == POS_XH) {
      /* 1 + 1 + c: the bit c, and a carry, which is the xH above. */
      if (!bits_put(f, i, c)) return 0;
      return part_chain(p, wrap, f, i + 1, -1, 0);
    } else {
      struct operand *o = kx == POS_XH ? &y : &x;
      int ko = kx == POS_XH ? ky : kx;
      struct operand rest;
      s = (ko == POS_XI) + 1 + c;
      if (!bits_put(f, i, s & 1)) return 0;
      i++;
      rest = operand(Field(o->v, 0), o->arg, o->depth + i);
      if (!(s >> 1)) return part_chain(p, wrap, f, i, rest.arg, rest.depth);
      /* The successor of the rest, as pos_succ_core, after bit i. */
      for (;;) {
        int k = pos_node(rest.v);
        (*w)++;
        if (k < 0) return 0;
        if (k == POS_XI) {
          if (!bits_put(f, i, 0)) return 0;
          i++;
          rest.v = Field(rest.v, 0);
          rest.depth++;
          continue;
        }
        if (k == POS_XO) {
          if (!bits_put(f, i, 1)) return 0;
          return part_chain(p, wrap, f, i + 1, rest.arg, rest.depth + 1);
        }
        if (!bits_put(f, i, 0)) return 0;
        return part_chain(p, wrap, f, i + 1, -1, 0);
      }
    }
  }
}

/* Pos.mul x y {struct x}: mul (p~1) y = add y (mul p y)~0,
   mul (p~0) y = (mul p y)~0, mul 1 y = y. It reads all of x. If x is a power
   of two, 2^t, the bytecode does not read y and the result is y below t xO
   nodes; otherwise the bytecode reads all of y (in add y _, whose second
   argument is longer), and so does the routine. */
static int pos_mul_core(struct operand x, struct operand y, int wrap,
                        struct binnum_part *p, uint64_t *w)
{
  size_t i;
  int pow2 = 1;
  if (!read_pos(x.v, &num_a, w)) return 0;
  for (i = 0; i + 1 < num_a.n; i++) if (num_a.d[i] != 0) pow2 = 0;
  if (num_a.d[num_a.n - 1] & (num_a.d[num_a.n - 1] - 1)) pow2 = 0;
  if (pow2) {
    uint64_t t = num_bitlen(&num_a) - 1, j;
    for (j = 0; j < t; j++) if (!bits_put(&num_r, j, 0)) return 0;
    return part_chain(p, wrap, &num_r, t, y.arg, y.depth);
  }
  if (!read_pos(y.v, &num_b, w)) return 0;
  if (!num_mul(&num_r, &num_a, &num_b)) return 0;
  part_pos(p, &num_r, wrap);
  return 1;
}

/* Z.pos_sub x y: the Z x - y. It reads both numbers to their ends. */
static int pos_sub_core(value x, value y, struct binnum_part *p, uint64_t *w)
{
  int c;
  if (!read_pos(x, &num_a, w) || !read_pos(y, &num_b, w)) return 0;
  c = num_cmp(&num_a, &num_b);
  if (c == 0) {
    part_imm(p, Val_int(0));
    return 1;
  }
  if (!num_sub(&num_r, c > 0 ? &num_a : &num_b, c > 0 ? &num_b : &num_a)) return 0;
  part_pos(p, &num_r, c > 0 ? Z_POS : Z_NEG);
  return 1;
}

/* Z.compare x y, as the bytecode: the node of x, the node of y, and
   Pos.compare (compare_cont Eq) of their numbers when both have the same
   sign, through CompOpp when both are negative. */
static int z_compare_core(value x, value y, value *res, uint64_t *w)
{
  int kx = z_node(x), ky;
  value c;
  (*w)++;
  if (kx < 0) return 0;
  ky = z_node(y);
  (*w)++;
  if (ky < 0) return 0;
  if (kx == Z_ZERO) {
    *res = ky == Z_ZERO ? CMP_EQ : ky == Z_POS ? CMP_LT : CMP_GT;
    return 1;
  }
  if (kx != ky) {
    *res = kx == Z_POS ? CMP_GT : CMP_LT;
    return 1;
  }
  if (!pos_compare_core(CMP_EQ, Field(x, 0), Field(y, 0), &c, w)) return 0;
  *res = kx == Z_POS ? c : c == CMP_LT ? CMP_GT : c == CMP_GT ? CMP_LT : CMP_EQ;
  return 1;
}

/** The routines: each reads its arguments [a], and sets [res]. */

static int r_pos_compare_cont(const value *a, struct binnum_result *res, uint64_t *w)
{
  value r = a[0], c;
  (*w)++;
  if (r != CMP_EQ && r != CMP_LT && r != CMP_GT) return 0;
  if (!pos_compare_core(r, a[1], a[2], &c, w)) return 0;
  part_imm(&res->part[0], c);
  return 1;
}

static int r_pos_eqb(const value *a, struct binnum_result *res, uint64_t *w)
{
  value b;
  if (!pos_eqb_core(a[0], a[1], &b, w)) return 0;
  part_imm(&res->part[0], b);
  return 1;
}

static int r_pos_div2(const value *a, struct binnum_result *res, uint64_t *w)
{
  int k = pos_node(a[0]);
  (*w)++;
  if (k < 0) return 0;
  if (k == POS_XH) part_imm(&res->part[0], Val_int(0));
  else part_chain(&res->part[0], 0, NULL, 0, 0, 1);
  return 1;
}

/* Pos.of_succ_nat n: of_succ_nat O = 1, of_succ_nat (S x) = succ
   (of_succ_nat x). It reads all of n; the result is n + 1. */
static int r_pos_of_succ_nat(const value *a, struct binnum_result *res, uint64_t *w)
{
  value v = a[0];
  uint64_t k = 0;
  for (;;) {
    int kn = nat_node(v);
    (*w)++;
    if (kn < 0) return 0;
    if (kn == 0) break;
    k++;
    v = Field(v, 0);
  }
  if (!num_set_u64(&num_r, k + 1)) return 0;
  part_pos(&res->part[0], &num_r, 0);
  return 1;
}

/* Z.double, Z.succ_double, Z.pred_double: the node of x, and for the last
   two, the run of Pos.pred_double on its number in one case. */
static int r_z_double(const value *a, struct binnum_result *res, uint64_t *w)
{
  int k = z_node(a[0]);
  (*w)++;
  if (k < 0) return 0;
  if (k == Z_ZERO) part_imm(&res->part[0], Val_int(0));
  else {
    if (!bits_put(&num_r, 0, 0)) return 0;
    part_chain(&res->part[0], k, &num_r, 1, 0, 1);
  }
  return 1;
}

static int r_z_succ_double(const value *a, struct binnum_result *res, uint64_t *w)
{
  int k = z_node(a[0]);
  (*w)++;
  if (k < 0) return 0;
  if (k == Z_ZERO) return part_chain(&res->part[0], Z_POS, NULL, 0, -1, 0);
  if (k == Z_POS) {
    if (!bits_put(&num_r, 0, 1)) return 0;
    return part_chain(&res->part[0], Z_POS, &num_r, 1, 0, 1);
  }
  return pos_pred_double_core(operand(Field(a[0], 0), 0, 1), Z_NEG, &res->part[0], w);
}

static int r_z_pred_double(const value *a, struct binnum_result *res, uint64_t *w)
{
  int k = z_node(a[0]);
  (*w)++;
  if (k < 0) return 0;
  if (k == Z_ZERO) return part_chain(&res->part[0], Z_NEG, NULL, 0, -1, 0);
  if (k == Z_NEG) {
    if (!bits_put(&num_r, 0, 1)) return 0;
    return part_chain(&res->part[0], Z_NEG, &num_r, 1, 0, 1);
  }
  return pos_pred_double_core(operand(Field(a[0], 0), 0, 1), Z_POS, &res->part[0], w);
}

/* Z.add x y: x = 0 gives y and y = 0 gives x, unread; numbers of the same
   sign are added as Pos.add; of opposite signs, subtracted as Z.pos_sub. */
static int r_z_add(const value *a, struct binnum_result *res, uint64_t *w)
{
  int kx = z_node(a[0]), ky;
  (*w)++;
  if (kx < 0) return 0;
  if (kx == Z_ZERO) return part_chain(&res->part[0], 0, NULL, 0, 1, 0);
  ky = z_node(a[1]);
  (*w)++;
  if (ky < 0) return 0;
  if (ky == Z_ZERO) return part_chain(&res->part[0], 0, NULL, 0, 0, 0);
  if (kx == ky)
    return pos_add_core(operand(Field(a[0], 0), 0, 1), operand(Field(a[1], 0), 1, 1), 0, kx,
                        &res->part[0], w);
  if (kx == Z_POS) return pos_sub_core(Field(a[0], 0), Field(a[1], 0), &res->part[0], w);
  return pos_sub_core(Field(a[1], 0), Field(a[0], 0), &res->part[0], w);
}

static int r_z_mul(const value *a, struct binnum_result *res, uint64_t *w)
{
  int kx = z_node(a[0]), ky;
  (*w)++;
  if (kx < 0) return 0;
  if (kx == Z_ZERO) {
    part_imm(&res->part[0], Val_int(0));
    return 1;
  }
  ky = z_node(a[1]);
  (*w)++;
  if (ky < 0) return 0;
  if (ky == Z_ZERO) {
    part_imm(&res->part[0], Val_int(0));
    return 1;
  }
  return pos_mul_core(operand(Field(a[0], 0), 0, 1), operand(Field(a[1], 0), 1, 1),
                      kx == ky ? Z_POS : Z_NEG, &res->part[0], w);
}

static int r_z_compare(const value *a, struct binnum_result *res, uint64_t *w)
{
  value c;
  if (!z_compare_core(a[0], a[1], &c, w)) return 0;
  part_imm(&res->part[0], c);
  return 1;
}

/* Z.leb: true unless Gt; Z.ltb: true if Lt. */
static int r_z_leb(const value *a, struct binnum_result *res, uint64_t *w)
{
  value c;
  if (!z_compare_core(a[0], a[1], &c, w)) return 0;
  part_imm(&res->part[0], c == CMP_GT ? BOOL_FALSE : BOOL_TRUE);
  return 1;
}

static int r_z_ltb(const value *a, struct binnum_result *res, uint64_t *w)
{
  value c;
  if (!z_compare_core(a[0], a[1], &c, w)) return 0;
  part_imm(&res->part[0], c == CMP_LT ? BOOL_TRUE : BOOL_FALSE);
  return 1;
}

/* Z.eqb x y: the node of x and of y, and Pos.eqb of their numbers when both
   have the same sign. */
static int r_z_eqb(const value *a, struct binnum_result *res, uint64_t *w)
{
  int kx = z_node(a[0]), ky;
  value b;
  (*w)++;
  if (kx < 0) return 0;
  ky = z_node(a[1]);
  (*w)++;
  if (ky < 0) return 0;
  if (kx == Z_ZERO || kx != ky) b = kx == ky ? BOOL_TRUE : BOOL_FALSE;
  else if (!pos_eqb_core(Field(a[0], 0), Field(a[1], 0), &b, w)) return 0;
  part_imm(&res->part[0], b);
  return 1;
}

/* Z.div2 z: Z0 -> Z0; Zpos p -> Z0 if p is 1, else Zpos (Pos.div2 p), the
   number below the node of p; Zneg p -> Zneg (Pos.div2_up p), where
   div2_up (p~1) = succ p, div2_up (p~0) = p, div2_up 1 = 1. */
static int r_z_div2(const value *a, struct binnum_result *res, uint64_t *w)
{
  int kz = z_node(a[0]), kp;
  value p;
  (*w)++;
  if (kz < 0) return 0;
  if (kz == Z_ZERO) {
    part_imm(&res->part[0], Val_int(0));
    return 1;
  }
  p = Field(a[0], 0);
  kp = pos_node(p);
  (*w)++;
  if (kp < 0) return 0;
  if (kz == Z_POS) {
    if (kp == POS_XH) part_imm(&res->part[0], Val_int(0));
    else part_chain(&res->part[0], Z_POS, NULL, 0, 0, 2);
    return 1;
  }
  if (kp == POS_XH) return part_chain(&res->part[0], Z_NEG, NULL, 0, -1, 0);
  if (kp == POS_XO) return part_chain(&res->part[0], Z_NEG, NULL, 0, 0, 2);
  return pos_succ_core(operand(Field(p, 0), 0, 2), Z_NEG, &res->part[0], w);
}

/* Z.of_nat n: O -> Z0, S n0 -> Zpos (of_succ_nat n0), that is Zpos n. */
static int r_z_of_nat(const value *a, struct binnum_result *res, uint64_t *w)
{
  value v = a[0];
  uint64_t k = 0;
  for (;;) {
    int kn = nat_node(v);
    (*w)++;
    if (kn < 0) return 0;
    if (kn == 0) break;
    k++;
    v = Field(v, 0);
  }
  if (k == 0) {
    part_imm(&res->part[0], Val_int(0));
    return 1;
  }
  if (!num_set_u64(&num_r, k)) return 0;
  part_pos(&res->part[0], &num_r, Z_POS);
  return 1;
}

/* Z.pos_div_eucl a b: for b > 0, the pair (a / b, a mod b) (by induction on
   a, the body keeps a = q b + r with 0 <= r < b). The routine refuses
   b <= 0, which the bytecode then computes. */
static int r_z_pos_div_eucl(const value *a, struct binnum_result *res, uint64_t *w)
{
  int kb;
  if (!read_pos(a[0], &num_a, w)) return 0;
  kb = z_node(a[1]);
  (*w)++;
  if (kb != Z_POS) return 0;
  if (!read_pos(Field(a[1], 0), &num_b, w)) return 0;
  if (!num_divmod(&num_q, &num_m, &num_a, &num_b)) return 0;
  res->nparts = 2;
  part_z(&res->part[0], &num_q, Z_POS);
  part_z(&res->part[1], &num_m, Z_POS);
  return 1;
}

/* Nat.eqb n m {struct n}: both O -> true; one O -> false; S n', S m' ->
   eqb n' m'. It reads the node of n, then of m, at each step. */
static int r_nat_eqb(const value *a, struct binnum_result *res, uint64_t *w)
{
  value n = a[0], m = a[1];
  for (;;) {
    int kn = nat_node(n), km;
    (*w)++;
    if (kn < 0) return 0;
    km = nat_node(m);
    (*w)++;
    if (km < 0) return 0;
    if (kn == 0 || km == 0) {
      part_imm(&res->part[0], kn == km ? BOOL_TRUE : BOOL_FALSE);
      return 1;
    }
    n = Field(n, 0);
    m = Field(m, 0);
  }
}

/* Nat.leb n m {struct n}: O, _ -> true (m unread); S _, O -> false;
   S n', S m' -> leb n' m'. */
static int r_nat_leb(const value *a, struct binnum_result *res, uint64_t *w)
{
  value n = a[0], m = a[1];
  for (;;) {
    int kn = nat_node(n), km;
    (*w)++;
    if (kn < 0) return 0;
    if (kn == 0) {
      part_imm(&res->part[0], BOOL_TRUE);
      return 1;
    }
    km = nat_node(m);
    (*w)++;
    if (km < 0) return 0;
    if (km == 0) {
      part_imm(&res->part[0], BOOL_FALSE);
      return 1;
    }
    n = Field(n, 0);
    m = Field(m, 0);
  }
}

const struct binnum_result *rocq_binnum_run(int k, int n, const value *args)
{
  static struct binnum_result res;
  uint64_t words = 0;
  int ok;
  if (k < 0 || k >= BINNUM_COUNT || n != binnum_arity[k]) return NULL;
  res.nparts = 1;
  switch (k) {
  case BINNUM_POS_COMPARE_CONT: ok = r_pos_compare_cont(args, &res, &words); break;
  case BINNUM_POS_EQB: ok = r_pos_eqb(args, &res, &words); break;
  case BINNUM_POS_SUCC:
    ok = pos_succ_core(operand(args[0], 0, 0), 0, &res.part[0], &words); break;
  case BINNUM_POS_ADD:
  case BINNUM_POS_ADD_CARRY:
    ok = pos_add_core(operand(args[0], 0, 0), operand(args[1], 1, 0),
                      k == BINNUM_POS_ADD_CARRY, 0, &res.part[0], &words);
    break;
  case BINNUM_POS_PRED_DOUBLE:
    ok = pos_pred_double_core(operand(args[0], 0, 0), 0, &res.part[0], &words); break;
  case BINNUM_POS_MUL:
    ok = pos_mul_core(operand(args[0], 0, 0), operand(args[1], 1, 0), 0, &res.part[0], &words);
    break;
  case BINNUM_POS_DIV2: ok = r_pos_div2(args, &res, &words); break;
  case BINNUM_POS_OF_SUCC_NAT: ok = r_pos_of_succ_nat(args, &res, &words); break;
  case BINNUM_Z_DOUBLE: ok = r_z_double(args, &res, &words); break;
  case BINNUM_Z_SUCC_DOUBLE: ok = r_z_succ_double(args, &res, &words); break;
  case BINNUM_Z_PRED_DOUBLE: ok = r_z_pred_double(args, &res, &words); break;
  case BINNUM_Z_POS_SUB: ok = pos_sub_core(args[0], args[1], &res.part[0], &words); break;
  case BINNUM_Z_ADD: ok = r_z_add(args, &res, &words); break;
  case BINNUM_Z_MUL: ok = r_z_mul(args, &res, &words); break;
  case BINNUM_Z_COMPARE: ok = r_z_compare(args, &res, &words); break;
  case BINNUM_Z_LEB: ok = r_z_leb(args, &res, &words); break;
  case BINNUM_Z_LTB: ok = r_z_ltb(args, &res, &words); break;
  case BINNUM_Z_EQB: ok = r_z_eqb(args, &res, &words); break;
  case BINNUM_Z_DIV2: ok = r_z_div2(args, &res, &words); break;
  case BINNUM_Z_OF_NAT: ok = r_z_of_nat(args, &res, &words); break;
  case BINNUM_Z_POS_DIV_EUCL: ok = r_z_pos_div_eucl(args, &res, &words); break;
  case BINNUM_NAT_EQB: ok = r_nat_eqb(args, &res, &words); break;
  case BINNUM_NAT_LEB: ok = r_nat_leb(args, &res, &words); break;
  default: ok = 0;
  }
  binnum_calls[k]++;
  binnum_words[k] += words;
  if (!ok) binnum_refusals[k]++;
  return ok ? &res : NULL;
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

/* [calls; refusals; words] of each routine, in routine order. */
value rocq_binnum_counters(value unit)
{
  CAMLparam1(unit);
  CAMLlocal1(res);
  int k;
  res = caml_alloc(3 * BINNUM_COUNT, 0);
  for (k = 0; k < BINNUM_COUNT; k++) {
    Store_field(res, 3 * k, Val_long(binnum_calls[k]));
    Store_field(res, 3 * k + 1, Val_long(binnum_refusals[k]));
    Store_field(res, 3 * k + 2, Val_long(binnum_words[k]));
  }
  CAMLreturn(res);
}

value rocq_binnum_reset_counters(value unit)
{
  int k;
  for (k = 0; k < BINNUM_COUNT; k++) {
    binnum_calls[k] = 0;
    binnum_refusals[k] = 0;
    binnum_words[k] = 0;
  }
  return Val_unit;
}
