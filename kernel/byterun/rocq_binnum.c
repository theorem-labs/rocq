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
   computes, on arguments that are closed values: trees of constructor values
   with the VM representation that vmbinnum.ml checks on the inductive types
   (the [mind_reloc_tbl] of kernel/indtypes.ml), with no accumulator and no
   other value in them. A routine reads each argument up to its end, or up to
   the first node that is not a constructor of the expected type, and then
   refuses the call: the bytecode of the function then runs as if the
   instruction were not there.

   The routine numbers and arities below must be those of the table
   [routines] of vmbinnum.ml, which compares them with [rocq_binnum_arities]
   when it is loaded. */

#include <stdint.h>
#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>

#include "rocq_binnum.h"

enum {
  BINNUM_POS_COMPARE_CONT,
  BINNUM_POS_EQB,
  BINNUM_COUNT
};

static const int binnum_arity[BINNUM_COUNT] = { 3, 2 };

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

/* Pos.compare_cont r x y {struct y}:
     x~1, y~1 -> compare_cont r x y      x~0, y~1 -> compare_cont Lt x y
     x~1, y~0 -> compare_cont Gt x y     x~0, y~0 -> compare_cont r x y
     x~1, 1   -> Gt                      x~0, 1   -> Gt
     1,   y~1 -> Lt     1, y~0 -> Lt     1,   1   -> r
   The loop runs these steps on both numbers at once, from their outermost
   constructors; r is the result if both end together. */
static int pos_compare_cont(const value *args, value *res, uint64_t *words)
{
  value r = args[0], x = args[1], y = args[2];
  uint64_t n = 1;
  int kx, ky, ok = 0;
  if (r != CMP_EQ && r != CMP_LT && r != CMP_GT) goto done;
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
static int pos_eqb(const value *args, value *res, uint64_t *words)
{
  value x = args[0], y = args[1];
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

int rocq_binnum_run(int k, int n, const value *args, value *res)
{
  uint64_t words = 0;
  value r;
  int ok;
  if (k < 0 || k >= BINNUM_COUNT || n != binnum_arity[k]) return 0;
  switch (k) {
  case BINNUM_POS_COMPARE_CONT: ok = pos_compare_cont(args, &r, &words); break;
  case BINNUM_POS_EQB: ok = pos_eqb(args, &r, &words); break;
  default: ok = 0;
  }
  binnum_calls[k]++;
  binnum_words[k] += words;
  if (ok) *res = r;
  else binnum_refusals[k]++;
  return ok;
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
