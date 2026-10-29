#!/usr/bin/env python3
"""Census check for per-proof replay (dispatch://BET-84, gate part 1).

Lists every site in an OCaml source tree that

  * registers a Summary entry (`Summary.ref`, `Summary.ref_tag`,
    `Summary.declare_summary[_tag]`, `Summary.declare_ml_modules_summary`,
    `Summary.MakeObservable`), kind `summary`;
  * declares a Libobject object (`declare_object` and its `_full`, `_gen`,
    `named_` variants), kind `object`;
  * declares an option outside the Summary (`~no_summary`), kind
    `nosummary-option`;
  * opens or aliases the `Summary` module, so registrations could hide from
    the scan, kind `summary-open`;
  * catches every exception without testing `CErrors.noncritical`: a `_`
    handler (`with _ ->`, `| _ ->` in a `try`, `| exception _ ->`) or a named
    handler that drops the exception instead of re-raising it, kind
    `catchall`.

Each site has a stable key (`<kind>:<path>:<name>`) that does not contain a
line number.  The rulings file maps every key to exactly one disposition:

  {"row": "<census row>"}        the site is covered by that CHANNELS.md row
  {"ruling": "<text or @name>"}  a written ruling (e.g. tactics never reach it)
  {"ineligible": "<text or @name>"}  proofs that reach it are made ineligible

`@name` refers to an entry of the file's top-level "reasons" object.  The
file's "scope" object lists the directories that are scanned ("include") and
the paths under them that are not ("exclude").

The channel check lists the other side, the recorder's own read sites, against
a second rulings file of the same shape (`--channels`; by default the
`channels.json` beside the rulings file, when it names the same "source"):

  * a `Proof_recorder.read` or `Proof_recorder.read_by` call, or a record
    expression with `row` and `channel` fields (the `register_tables`
    entries), kind `read`, key `read:<path>:<row>/<channel>`;
  * a `Proof_recorder.ineligible` call, or a record expression with `reason`
    and `detail` fields, kind `ineligible`, key `ineligible:<path>:<reason>`;
  * an `open`, `include`, alias or local open of `Proof_recorder`, which
    could hide calls from the scan, kind `recorder-open`.

One key covers every read of that row and channel in the file.  When the row,
channel or reason is a parameter of a function of the same file, the scan
follows each call of that function (partial applications included) to the
value it passes.  A value that is still not a string literal gives the key
`<kind>:<path>:<binding>/<part>/...`: the enclosing top-level binding, then
each part, a literal quoted and anything else as written.  A site whose row
is a literal must carry `{"row": "<that row>"}`, and a site whose reason is a
literal must carry `{"ineligible": "@<that reason>"}`.  `lib/proof_record.ml`
(the record format and its reader) is not scanned, and in
`lib/proof_recorder.ml` only literal reasons are: its own records carry the
row, channel and reason of its caller.

Exit status: 0 when every site is ruled and every ruling names a site, 1 when
a site is unmapped or a ruling is stale or invalid (one per line on stdout),
2 on a usage or read error.  Python 3.8+, standard library only.
"""

import argparse
import bisect
import collections
import json
import os
import re
import sys

# --------------------------------------------------------------------------
# Tokenizer

OPCHARS = set("!$%&*+-./:<=>?@^|~#")
IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
NUM_RE = re.compile(r"[0-9][0-9A-Za-z_.]*")
QSTRING_RE = re.compile(r"\{([a-z_]*)\|")
ESC_CHAR_RE = re.compile(r"'\\(?:[\\'\"ntbr ]|[0-9]{3}|x[0-9a-fA-F]{2}|o[0-7]{3})'")

Token = collections.namedtuple("Token", "kind text line col first value")

OPENERS = {"(", "[", "[|", "{", "begin", "struct", "sig", "object", "do"}
CLOSERS = {")", "]", "|]", "}", "end", "done"}
LETS = {"let", "let*", "let+"}
ITEM_KEYWORDS = {"type", "external", "val", "class", "include", ";;"}
KEYWORDS = {
    "and", "as", "assert", "begin", "class", "constraint", "do", "done", "downto", "else", "end",
    "exception", "external", "false", "for", "fun", "function", "functor", "if", "in", "include",
    "inherit", "initializer", "lazy", "let", "match", "method", "module", "mutable", "new", "nonrec",
    "object", "of", "open", "private", "rec", "sig", "struct", "then", "to", "true", "try", "type",
    "val", "virtual", "when", "while", "with",
}


def _skip_comment(src, i):
    """Return the index just past the comment that starts at src[i:i+2] == '(*'."""
    n = len(src)
    depth = 0
    while i < n:
        if src.startswith("(*", i):
            depth += 1
            i += 2
        elif src.startswith("*)", i):
            depth -= 1
            i += 2
            if depth == 0:
                return i
        elif src[i] == '"':
            i = _skip_string(src, i)
        elif src[i] == "'":
            m = ESC_CHAR_RE.match(src, i)
            if m:
                i = m.end()
            elif i + 2 < n and src[i + 2] == "'":
                i += 3
            else:
                i += 1
        elif src[i] == "{":
            m = QSTRING_RE.match(src, i)
            i = _skip_qstring(src, m) if m else i + 1
        else:
            i += 1
    return n


def _skip_string(src, i):
    n = len(src)
    j = i + 1
    while j < n:
        c = src[j]
        if c == "\\":
            j += 2
            continue
        if c == '"':
            return j + 1
        j += 1
    return n


def _skip_qstring(src, m):
    close = "|" + m.group(1) + "}"
    end = src.find(close, m.end())
    return len(src) if end < 0 else end + len(close)


def tokenize(src):
    toks = []
    n = len(src)
    i = 0
    line = 1
    line_start = 0
    last_tok_line = 0

    def add(kind, text, start, value=None):
        nonlocal last_tok_line
        toks.append(Token(kind, text, line, start - line_start, line != last_tok_line, value))
        last_tok_line = line

    def advance(start, end):
        nonlocal line, line_start
        k = src.count("\n", start, end)
        if k:
            line += k
            line_start = src.rfind("\n", start, end) + 1

    while i < n:
        c = src[i]
        if c == "\n":
            line += 1
            line_start = i + 1
            i += 1
            continue
        if c in " \t\r\f":
            i += 1
            continue
        if src.startswith("(*", i):
            j = _skip_comment(src, i)
            advance(i, j)
            i = j
            continue
        if c == '"':
            j = _skip_string(src, i)
            add("str", src[i:j], i, src[i + 1:j - 1])
            advance(i, j)
            i = j
            continue
        if c == "{":
            m = QSTRING_RE.match(src, i)
            if m:
                j = _skip_qstring(src, m)
                add("str", src[i:j], i, src[m.end():j - len(m.group(1)) - 2])
                advance(i, j)
                i = j
                continue
        if c == "'":
            m = ESC_CHAR_RE.match(src, i)
            if m:
                add("char", m.group(0), i)
                i = m.end()
                continue
            if i + 2 < n and src[i + 2] == "'" and src[i + 1] != "\n":
                add("char", src[i:i + 3], i)
                i += 3
                continue
            add("op", "'", i)
            i += 1
            continue
        m = IDENT_RE.match(src, i)
        if m:
            j = m.end()
            text = m.group(0)
            if text in ("let", "and") and j < n and src[j] in "*+" and (j + 1 >= n or src[j + 1] not in OPCHARS):
                text += src[j]
                j += 1
            add("id", text, i)
            i = j
            continue
        m = NUM_RE.match(src, i)
        if m:
            add("num", m.group(0), i)
            i = m.end()
            continue
        if c == "[" and i + 1 < n and src[i + 1] == "|":
            add("punct", "[|", i)
            i += 2
            continue
        if c == "|" and i + 1 < n and src[i + 1] == "]":
            add("punct", "|]", i)
            i += 2
            continue
        if c == ";" and i + 1 < n and src[i + 1] == ";":
            add("punct", ";;", i)
            i += 2
            continue
        if c in "()[]{},;`":
            add("punct", c, i)
            i += 1
            continue
        if c in OPCHARS:
            j = i + 1
            while j < n and src[j] in OPCHARS and not (src[j] == "|" and j + 1 < n and src[j + 1] == "]"):
                j += 1
            add("op", src[i:j], i)
            i = j
            continue
        add("other", c, i)
        i += 1
    return toks


def word(tok):
    """The token's text when it is code (not a string or char literal)."""
    return tok.text if tok.kind in ("id", "op", "punct") else None


def is_lower_ident(tok):
    return tok.kind == "id" and tok.text not in KEYWORDS and (tok.text[0].islower() or tok.text[0] == "_")


def render(toks):
    out = []
    prev = None
    for t in toks:
        s = t.text
        tight = prev is not None and (
            s in (".", ")", "]", ",", ";") or prev == "." or prev in ("(", "[", "~", "?")
            or (s == ":" and prev is not None and out and out[-1] and IDENT_RE.fullmatch(prev) and _label_before(out))
        )
        if out and not tight:
            out.append(" ")
        out.append(s)
        prev = s
    return "".join(out)


def _label_before(out):
    # `~name:x` renders tight: the token before the identifier is `~` or `?`.
    return len(out) >= 2 and out[-2] in ("~", "?")


# --------------------------------------------------------------------------
# Structure: which `let`s are structure items, and the binding each token sits in


class Unit:
    """One tokenized source file with the derived structure."""

    def __init__(self, path, src):
        self.path = path
        self.toks = tokenize(src)
        self._structure()

    def _structure(self):
        toks = self.toks
        stacks = collections.defaultdict(list)
        depth = 0
        toplevel = set()
        for k, t in enumerate(toks):
            w = word(t)
            if w in OPENERS:
                depth += 1
            elif w in CLOSERS:
                toplevel.update(stacks.pop(depth, []))
                depth = max(depth - 1, 0)
            elif w in LETS:
                stacks[depth].append(k)
            elif w == "in" and stacks[depth]:
                stacks[depth].pop()
        for rest in stacks.values():
            toplevel.update(rest)
        self.toplevel_lets = toplevel

        # Second pass: binding name per token, from the nearest structure-level let/and.
        binding = []
        current = "<top>"
        stacks = collections.defaultdict(list)
        depth = 0
        for k, t in enumerate(toks):
            w = word(t)
            if w in OPENERS:
                depth += 1
            elif w in CLOSERS:
                stacks.pop(depth, None)
                depth = max(depth - 1, 0)
            elif w in LETS:
                stacks[depth].append(k)
                if k in toplevel:
                    current = self._binding_name(k)
            elif w in ("and", "and*", "and+"):
                if stacks[depth] and stacks[depth][-1] in toplevel:
                    current = self._binding_name(k)
            elif w == "in" and stacks[depth]:
                stacks[depth].pop()
            binding.append(current)
        self.binding = binding

    def _binding_name(self, k):
        toks = self.toks
        j = k + 1
        while j < len(toks) and word(toks[j]) in ("rec", "nonrec"):
            j += 1
        if j >= len(toks):
            return "<top>"
        t = toks[j]
        if t.kind == "id" and t.text not in KEYWORDS and t.text != "_":
            return t.text
        if word(t) == "(" and j + 2 < len(toks) and toks[j + 1].kind == "op" and word(toks[j + 2]) == ")":
            return "(" + toks[j + 1].text + ")"
        return "<top>"

    def prev_word(self, k):
        return word(self.toks[k - 1]) if k > 0 else None

    # ---- expression helpers

    def match_close(self, k):
        """Index of the closer matching the opener at k."""
        depth = 0
        for j in range(k, len(self.toks)):
            w = word(self.toks[j])
            if w in OPENERS:
                depth += 1
            elif w in CLOSERS:
                depth -= 1
                if depth == 0:
                    return j
        return len(self.toks) - 1

    def simple_expr(self, k):
        """End (exclusive) of the simple expression that starts at k."""
        toks = self.toks
        if k >= len(toks):
            return k
        t = toks[k]
        w = word(t)
        if w in OPENERS:
            return self.match_close(k) + 1
        if t.kind in ("str", "char", "num"):
            return k + 1
        if w == "`" and k + 1 < len(toks):
            return k + 2
        if w in ("!", "-"):
            return self.simple_expr(k + 1)
        if t.kind == "id" and w not in KEYWORDS:
            j = k + 1
            while j + 1 < len(toks) and word(toks[j]) == ".":
                nxt = toks[j + 1]
                if word(nxt) in OPENERS:
                    return self.match_close(j + 1) + 1
                if nxt.kind != "id":
                    break
                j += 2
            return j
        return k + 1

    def skip_labels(self, k):
        toks = self.toks
        while k + 1 < len(toks) and word(toks[k]) in ("~", "?") and toks[k + 1].kind == "id":
            k += 2
            if k < len(toks) and word(toks[k]) == ":":
                k = self.simple_expr(k + 1)
        return k

    def app_extent(self, k):
        """End (exclusive) of the application whose head is the token at k."""
        toks = self.toks
        depth = 0
        j = k + 1
        limit = min(len(toks), k + 400)
        while j < limit:
            t = toks[j]
            w = word(t)
            if w in OPENERS:
                depth += 1
            elif w in CLOSERS:
                if depth == 0:
                    return j
                depth -= 1
            elif depth == 0 and (
                w in LETS or w in ITEM_KEYWORDS
                or w in ("in", ";", "|", "then", "else", "with", "and", "->", "module", "open", "exception")
            ):
                return j
            j += 1
        return j

    def name_expr(self, k, end):
        """Render the expression [k, e) as a key name; a lone string literal renders quoted."""
        e = min(self.simple_expr(k), end)
        part = self.toks[k:e]
        if len(part) == 1 and part[0].kind == "str":
            return True, '"' + part[0].value + '"'
        return False, render(part[:12])


# --------------------------------------------------------------------------
# Site detection

Site = collections.namedtuple("Site", "kind path line key want", defaults=(None,))

SUMMARY_FUNS = {
    "ref", "ref_tag", "declare_summary", "declare_summary_tag", "declare_ml_modules_summary", "MakeObservable",
}
OBJECT_FUNS = {
    "declare_object", "declare_object_full", "declare_object_gen",
    "declare_named_object", "declare_named_object_full", "declare_named_object_gen",
}
OBJECT_MAKERS = {
    "default_object", "local_object", "local_object_nodischarge", "global_object",
    "global_object_nodischarge", "superglobal_object", "superglobal_object_nodischarge",
    "object_with_locality",
}
RAISE_HEADS = [
    ["raise"], ["Stdlib", ".", "raise"], ["iraise"], ["Exninfo", ".", "iraise"], ["Util", ".", "iraise"],
    ["Printexc", ".", "raise_with_backtrace"],
]


def scan_source(path, src, cache=None):
    """All census sites of one file, with stable keys."""
    unit = _unit_of(path, src, cache)
    raw = []  # (kind, line, name)
    raw += _summary_sites(unit)
    raw += _object_sites(unit)
    raw += _nosummary_sites(unit)
    raw += _catchall_sites(unit)
    raw.sort(key=lambda r: (r[1], r[0]))
    seen = collections.Counter()
    sites = []
    for kind, line, name in raw:
        base = "%s:%s:%s" % (kind, path, name)
        seen[base] += 1
        key = base if seen[base] == 1 else "%s#%d" % (base, seen[base])
        sites.append(Site(kind, path, line, key))
    return sites


def _unit_of(path, src, cache):
    """The file's Unit, tokenized once for every scanner that shares `cache`."""
    if cache is None:
        return Unit(path, src)
    if "unit" not in cache:
        cache["unit"] = Unit(path, src)
    return cache["unit"]


def _summary_sites(unit):
    if unit.path.endswith("library/summary.ml"):
        return []
    toks = unit.toks
    out = []
    for k, t in enumerate(toks):
        if t.kind != "id" or t.text != "Summary":
            continue
        nxt = word(toks[k + 1]) if k + 1 < len(toks) else None
        prev = unit.prev_word(k)
        if nxt != ".":
            if prev in ("open", "include", "=") or (prev == "!" and k > 1 and word(toks[k - 2]) == "open"):
                out.append(("summary-open", t.line, unit.binding[k]))
            continue
        if k + 2 >= len(toks):
            continue
        f = toks[k + 2]
        if word(f) == "(":
            out.append(("summary-open", t.line, unit.binding[k]))
            continue
        if f.kind != "id" or f.text not in SUMMARY_FUNS:
            continue
        head = k + 2
        end = unit.app_extent(head)
        name = None
        if f.text in ("ref", "ref_tag"):
            j = head + 1
            depth = 0
            while j < end:
                w = word(toks[j])
                if w in OPENERS:
                    depth += 1
                elif w in CLOSERS:
                    depth -= 1
                elif depth == 0 and w == "~" and j + 2 < end and toks[j + 1].text == "name" and word(toks[j + 2]) == ":":
                    lit, name = unit.name_expr(j + 3, end)
                    if not lit:
                        name = unit.binding[k] + "/" + name
                    break
                j += 1
        elif f.text in ("declare_summary", "declare_summary_tag"):
            j = unit.skip_labels(head + 1)
            if j < end:
                lit, name = unit.name_expr(j, end)
                if not lit:
                    name = unit.binding[k] + "/" + name
        elif f.text == "MakeObservable":
            for j in range(head + 1, end - 3):
                if word(toks[j]) == "let" and toks[j + 1].text == "name" and word(toks[j + 2]) == "=":
                    lit, name = unit.name_expr(j + 3, end)
                    if not lit:
                        name = unit.binding[k] + "/" + name
                    break
        if name is None:
            name = unit.binding[k] + "/" + f.text
        out.append(("summary", t.line, name))
    return out


def _object_sites(unit):
    if unit.path.endswith("library/libobject.ml"):
        return []
    toks = unit.toks
    out = []
    for k, t in enumerate(toks):
        if t.kind != "id" or t.text not in OBJECT_FUNS:
            continue
        if unit.prev_word(k) in ("let", "and", "val", "rec", "external"):
            continue
        end = unit.app_extent(k)
        name = None
        for j in range(k + 1, end):
            if toks[j].kind == "id" and toks[j].text in OBJECT_MAKERS:
                a = unit.skip_labels(j + 1)
                if a < end:
                    lit, name = unit.name_expr(a, end)
                    if not lit:
                        name = unit.binding[k] + "/" + name
                break
        if name is None:
            j = k + 1
            if j < end and word(toks[j]) == "@@":
                j += 1
            arg_end = min(unit.simple_expr(j), end) if j < end else j
            name = unit.binding[k] + "/" + (render(toks[j:arg_end][:16]) or t.text)
        out.append(("object", t.line, name))
    return out


def _nosummary_sites(unit):
    if unit.path.endswith("library/goptions.ml"):
        return []
    toks = unit.toks
    out = []
    for k, t in enumerate(toks):
        if t.kind != "id" or t.text != "no_summary" or unit.prev_word(k) not in ("~", "?"):
            continue
        if k + 2 < len(toks) and word(toks[k + 1]) == ":" and word(toks[k + 2]) == "false":
            continue
        name = None
        for j in range(k + 1, min(len(toks) - 2, k + 300)):
            if word(toks[j]) in LETS and j in unit.toplevel_lets:
                break
            if toks[j].text == "optkey" and word(toks[j + 1]) == "=" and word(toks[j + 2]) == "[":
                close = unit.match_close(j + 2)
                parts = [x.value for x in toks[j + 3:close] if x.kind == "str"]
                name = '"' + " ".join(parts) + '"'
                break
        if name is None:
            name = unit.binding[k] + "/no_summary"
        out.append(("nosummary-option", toks[k - 1].line, name))
    return out


# ---- catch-all handlers


def _find_with(unit, k):
    depth = 0
    pending = 1
    toks = unit.toks
    for j in range(k + 1, len(toks)):
        w = word(toks[j])
        if w in OPENERS:
            depth += 1
        elif w in CLOSERS:
            if depth == 0:
                return None
            depth -= 1
        elif depth == 0:
            if w in ("try", "match"):
                pending += 1
            elif w == "with":
                pending -= 1
                if pending == 0:
                    return j
    return None


def _scan_body(unit, k):
    """Scan a case body from k.  Returns (end, next_case_start or None)."""
    toks = unit.toks
    n = len(toks)
    depth = lets = ifs = pending = 0
    captured = False
    while k < n:
        t = toks[k]
        w = word(t)
        if w in OPENERS:
            depth += 1
        elif w in CLOSERS:
            if depth == 0:
                return k, None
            depth -= 1
        elif depth == 0 and w is not None:
            prev = unit.prev_word(k)
            if w in LETS:
                if k in unit.toplevel_lets:
                    return k, None
                lets += 1
            elif w in ITEM_KEYWORDS or w in ("module", "open") and prev != "let" or w == "exception" and prev not in ("let", "|", "with"):
                return k, None
            elif w == "in":
                if lets == 0:
                    return k, None
                lets -= 1
            elif w in ("and", "and*", "and+"):
                if lets == 0:
                    return k, None
            elif w == "if":
                ifs += 1
            elif w == "then":
                if ifs == 0:
                    return k, None
            elif w == "else":
                if ifs == 0:
                    return k, None
                ifs -= 1
            elif w in ("match", "try"):
                pending += 1
            elif w == "with":
                if pending == 0:
                    return k, None
                pending -= 1
                captured = True
            elif w == "function":
                captured = True
            elif w == "|" and not captured:
                return k, k + 1
        k += 1
    return n, None


def _find_arrow(unit, k):
    depth = 0
    toks = unit.toks
    while k < len(toks):
        w = word(toks[k])
        if w in OPENERS:
            depth += 1
        elif w in CLOSERS:
            if depth == 0:
                return None
            depth -= 1
        elif depth == 0 and w == "->":
            return k
        k += 1
    return None


def _cases(unit, k):
    """Cases (pattern start, arrow, body end) of a handler starting at k."""
    toks = unit.toks
    out = []
    if k < len(toks) and word(toks[k]) == "|":
        k += 1
    while k < len(toks):
        arrow = _find_arrow(unit, k)
        if arrow is None:
            break
        end, nxt = _scan_body(unit, arrow + 1)
        out.append((k, arrow, end))
        if nxt is None:
            break
        k = nxt
    return out


def _split_depth0(toks, seps):
    parts = [[]]
    depth = 0
    for t in toks:
        w = word(t)
        if w in OPENERS:
            depth += 1
        elif w in CLOSERS:
            depth -= 1
        if depth == 0 and w in seps:
            parts.append([])
        else:
            parts[-1].append(t)
    return parts


def _strip_parens(toks):
    while len(toks) >= 2 and (
        (word(toks[0]) == "(" and word(toks[-1]) == ")") or (word(toks[0]) == "begin" and word(toks[-1]) == "end")
    ):
        depth = 0
        whole = True
        for i, t in enumerate(toks):
            w = word(t)
            if w in OPENERS:
                depth += 1
            elif w in CLOSERS:
                depth -= 1
                if depth == 0 and i != len(toks) - 1:
                    whole = False
                    break
        if not whole:
            break
        toks = toks[1:-1]
    return toks


def _pattern_binding(alt):
    """'_' for a wildcard, the variable for a catch-all binding, None for a specific pattern."""
    a = _strip_parens(alt)
    if len(a) == 3 and word(a[1]) == ":":  # (e : exn)
        a = a[:1]
    if len(a) == 1:
        if word(a[0]) == "_":
            return "_"
        if is_lower_ident(a[0]):
            return a[0].text
    if len(a) == 3 and word(a[0]) == "_" and word(a[1]) == "as" and is_lower_ident(a[2]):
        return a[2].text
    return None


def _reraises(body, var):
    """True when the body always ends by re-raising the bound exception."""
    tracked = {var}
    segs = [_strip_parens(s) for s in _split_depth0(_strip_parens(body), {";", "in"})]
    # Follow names bound from the exception.  A binding keeps a name tracked only when its right side is a
    # tracked name or `Exninfo.capture` of one; any other binding of that name (a new exception, a wrapper
    # that may change it) stops tracking it, so the site is listed and needs a written ruling.
    flat = _strip_parens(body)
    for i, t in enumerate(flat):
        if word(t) in LETS:
            j = i + 1
            names = []
            while j < len(flat) and word(flat[j]) != "=":
                if is_lower_ident(flat[j]):
                    names.append(flat[j].text)
                j += 1
            rhs_end = j + 1
            depth = 0
            while rhs_end < len(flat):
                w = word(flat[rhs_end])
                if w in OPENERS:
                    depth += 1
                elif w in CLOSERS:
                    depth -= 1
                elif depth == 0 and w == "in":
                    break
                rhs_end += 1
            rhs = [x.text for x in _strip_parens(flat[j + 1:rhs_end])]
            preserving = (len(rhs) == 1 and rhs[0] in tracked) or (
                len(rhs) == 4 and rhs[:3] == ["Exninfo", ".", "capture"] and rhs[3] in tracked
            )
            if preserving:
                tracked.update(names)
            else:
                tracked.difference_update(names)
    while segs and not segs[-1]:
        segs.pop()
    if not segs:
        return False
    tail = segs[-1]
    while True:
        inner = _strip_parens(tail)
        sub = [s for s in _split_depth0(inner, {";", "in"}) if s]
        if len(sub) > 1:
            tail = sub[-1]
            continue
        tail = inner
        break
    words = [t.text for t in tail]
    for head in RAISE_HEADS:
        if words[:len(head)] == head:
            arg = _strip_parens(tail[len(head):])
            if not arg:
                return False
            first = _split_depth0(arg, {","})[0]
            first = _strip_parens(first)
            if len(first) == 1 and first[0].kind == "id" and first[0].text in tracked:
                return True
            if [t.text for t in first[:3]] == ["Exninfo", ".", "capture"] and len(first) == 4 and first[3].text in tracked:
                return True
            if head[-1] == "raise_with_backtrace" and arg and arg[0].kind == "id" and arg[0].text in tracked:
                return True
            return False
    return False


def _classify(unit, start, arrow, end):
    """Return True when the case catches every exception and drops it."""
    toks = unit.toks
    pat = toks[start:arrow]
    guard = None
    depth = 0
    for i, t in enumerate(pat):
        w = word(t)
        if w in OPENERS:
            depth += 1
        elif w in CLOSERS:
            depth -= 1
        elif depth == 0 and w == "when":
            guard = pat[i + 1:]
            pat = pat[:i]
            break
    binders = [_pattern_binding(alt) for alt in _split_depth0(pat, {"|"})]
    wild = "_" in binders
    var = next((b for b in binders if b not in (None, "_")), None)
    if not wild and var is None:
        return False
    if guard is not None and any(t.text == "noncritical" for t in guard):
        return False
    if wild:
        return True
    body = toks[arrow + 1:end]
    if any(t.text == "noncritical" for t in body):
        return False
    if guard is None and _reraises(body, var):
        return False
    return True


def _catchall_sites(unit):
    toks = unit.toks
    out = []

    def emit(start, arrow, end, prefix=""):
        if _classify(unit, start, arrow, end):
            body = toks[arrow + 1:min(end, arrow + 9)]
            snippet = prefix + render(toks[start:arrow]) + " -> " + render(body)
            line = toks[start - 1].line if prefix else toks[start].line
            out.append(("catchall", line, unit.binding[start] + "/" + snippet.rstrip()))

    for k, t in enumerate(toks):
        w = word(t)
        if w == "try":
            j = _find_with(unit, k)
            if j is None:
                continue
            for start, arrow, end in _cases(unit, j + 1):
                emit(start, arrow, end)
        elif w == "exception" and unit.prev_word(k) in ("|", "with"):
            arrow = _find_arrow(unit, k + 1)
            if arrow is None:
                continue
            end, _ = _scan_body(unit, arrow + 1)
            emit(k + 1, arrow, end, prefix="exception ")
    return out


# --------------------------------------------------------------------------
# Recorder read sites (the channel check)

RECORDER = "Proof_recorder"
RECORDER_CALLS = {"read": ("row", "channel"), "read_by": ("row", "channel"), "ineligible": ("reason",),
                  "trip_fence": ("reason",)}
# The record format and its reader build records from parsed JSON, not from a read.
RECORD_FORMAT_FILE = "lib/proof_record.ml"
# The recorder's own plumbing passes its caller's row, channel and reason on: only its literal reasons are sites.
RECORDER_FILE = "lib/proof_recorder.ml"
CHANNEL_HINT_RE = re.compile(r"Proof_recorder|\b(?:row|reason)\s*[=;}]")
MAX_FOLLOW = 8
NOT_A_CALL = {"let", "and", "rec", "nonrec", "val", "external", "method", "~", "?"}
ANDS = ("and", "and*", "and+")

# A `let`/`and` binding: its name, whether it is a structure item, the index of its `=`, its parameters
# ((kind, label, variable) with kind "pos" or "label"), and the index where its body ends.
Def = collections.namedtuple("Def", "name toplevel eq params end")


def _slot(kind, text, pos, d=None, spec=None):
    """One argument value: kind "lit" (a string literal), "expr" (other code, rendered), "var" (a variable to
    follow) or "param" (parameter `spec` of the definition at d, to follow through its calls)."""
    return (kind, text, pos, d, spec)


def scan_channels(path, src, cache=None):
    """All recorder read sites of one file, with stable keys: one key per row and channel, or per reason."""
    if path.endswith(RECORD_FORMAT_FILE) or not CHANNEL_HINT_RE.search(src):
        return []
    unit = _unit_of(path, src, cache)
    own = path.endswith(RECORDER_FILE)
    raw = []  # (kind, line, name, want)
    for kind, where, slots in _recorder_calls(unit, own) + _record_literals(unit):
        if own and kind != "ineligible":
            continue
        for done, at in _resolve(unit, slots, where):
            if own and done[0][0] != "lit":
                continue
            raw.append(_channel_site(unit, kind, done, at))
    raw.sort(key=lambda r: (r[1], r[0], r[2]))
    seen = set()
    sites = []
    for kind, line, name, want in raw:
        key = "%s:%s:%s" % (kind, path, name)
        if key not in seen:
            seen.add(key)
            sites.append(Site(kind, path, line, key, want))
    return sites


def _channel_site(unit, kind, slots, where):
    line = unit.toks[where].line
    if kind == "recorder-open":
        return kind, line, unit.binding[where], None
    want = None
    if slots[0][0] == "lit":
        want = ("row" if kind == "read" else "ineligible", slots[0][1])
    if all(s[0] == "lit" for s in slots):
        return kind, line, "/".join(s[1] for s in slots), want
    loose = next(s for s in slots if s[0] != "lit")
    parts = ['"%s"' % s[1] if s[0] == "lit" else s[1] for s in slots]
    return kind, line, unit.binding[loose[2]] + "/" + "/".join(parts), want


def _recorder_calls(unit, own):
    """(kind, where, slots) for each recorder call, and for each open or alias of the recorder module."""
    toks = unit.toks
    out = []
    for k, t in enumerate(toks):
        if t.kind != "id":
            continue
        head = None
        if t.text == RECORDER:
            nxt = word(toks[k + 1]) if k + 1 < len(toks) else None
            if nxt != ".":
                prev = unit.prev_word(k)
                if prev in ("open", "include", "=") or (prev == "!" and k > 1 and word(toks[k - 2]) == "open"):
                    out.append(("recorder-open", k, []))
                continue
            if k + 2 < len(toks) and word(toks[k + 2]) in OPENERS:
                out.append(("recorder-open", k, []))
            elif k + 2 < len(toks) and toks[k + 2].kind == "id" and toks[k + 2].text in RECORDER_CALLS:
                head = k + 2
        elif own and t.text == "ineligible" and unit.prev_word(k) not in NOT_A_CALL | {"."}:
            head = k
        if head is None:
            continue
        labels = _call_args(unit, head)[1]
        name = toks[head].text
        slots = []
        for label in RECORDER_CALLS[name]:
            span = labels.get(label)
            slots.append(_arg_value(unit, *span) if span else _slot("expr", "<no %s>" % label, head))
        out.append(("ineligible" if name in ("ineligible", "trip_fence") else "read", head, slots))
    return out


def _record_literals(unit):
    """(kind, where, slots) for each record with `row` and `channel` fields, or `reason` and `detail` fields,
    and for each update `{ r with ... }` that sets one of `row`, `channel` or `reason`."""
    toks = unit.toks
    out = []
    for k, t in enumerate(toks):
        if word(t) != "{":
            continue
        close = unit.match_close(k)
        start = k + 1
        base = None
        j = _depth0_find(unit, k + 1, close, ("with",))
        if j < close:
            start = j + 1
            base = "<" + (render(toks[k + 1:j][:8]) or "?") + ">"
        fields = {}
        j = start
        while j < close:
            e = _depth0_find(unit, j, close, (";",))
            f = j
            while f + 2 < e and toks[f].kind == "id" and toks[f].text[:1].isupper() and word(toks[f + 1]) == ".":
                f += 2
            if f < e and is_lower_ident(toks[f]):
                if f + 1 == e:
                    fields[toks[f].text] = (f, _slot("var", toks[f].text, f))
                elif word(toks[f + 1]) == "=":
                    fields[toks[f].text] = (f, _arg_value(unit, f + 2, e))
            j = e + 1
        if base is not None:
            # An update keeps the fields it does not set: they come from the record it copies.
            if "row" in fields or "channel" in fields:
                for name in ("row", "channel", "detail"):
                    fields.setdefault(name, (k, _slot("expr", base, k)))
            elif "reason" in fields:
                fields.setdefault("detail", (k, _slot("expr", base, k)))
        if "row" in fields and "channel" in fields:
            out.append(("read", min(fields["row"][0], fields["channel"][0]), [fields["row"][1], fields["channel"][1]]))
        if "reason" in fields and "detail" in fields:
            out.append(("ineligible", fields["reason"][0], [fields["reason"][1]]))
    return out


def _depth0_find(unit, j, end, words):
    """Index of the first token in [j, end) at bracket depth 0 that is one of `words`, else end."""
    depth = 0
    toks = unit.toks
    while j < end:
        w = word(toks[j])
        if w in OPENERS:
            depth += 1
        elif w in CLOSERS:
            depth -= 1
        elif depth == 0 and w in words:
            return j
        j += 1
    return end


def _call_args(unit, h):
    """Positional argument spans, labelled argument spans and end of the application headed at h.  A punned
    label `~x` spans the label itself, which names the variable passed."""
    toks = unit.toks
    end = unit.app_extent(h)
    positional, labels = [], {}
    k = h + 1
    while k < end:
        t = toks[k]
        w = word(t)
        if w in ("~", "?") and k + 1 < end and toks[k + 1].kind == "id":
            if k + 2 < end and word(toks[k + 2]) == ":":
                e = min(unit.simple_expr(k + 3), end)
                labels[toks[k + 1].text] = (k + 3, e)
                k = e
            else:
                labels[toks[k + 1].text] = (k + 1, k + 2)
                k += 2
            continue
        if (t.kind == "op" and w not in ("!", "-")) or w == "," or (w in KEYWORDS and w not in ("true", "false", "begin")):
            break
        e = min(unit.simple_expr(k), end)
        if e <= k:
            break
        positional.append((k, e))
        k = e
    return positional, labels, end


def _arg_value(unit, s, e):
    """The slot of the expression toks[s:e]: a string literal, a bare variable, or other code."""
    part = _strip_parens(unit.toks[s:e])
    if len(part) == 1 and part[0].kind == "str":
        return _slot("lit", part[0].value, s)
    if len(part) == 1 and is_lower_ident(part[0]) and part[0].text != "_":
        return _slot("var", part[0].text, s)
    return _slot("expr", render(part[:12]) or "<none>", s)


# ---- following a variable to the values the code passes


def _resolve(unit, slots, where, depth=0):
    """Replace each variable slot by the values the code gives it.  Returns [(slots, where)], where `where` is
    the call that supplied the last value.  Slots bound by one function follow the same call together."""
    pending = [i for i, s in enumerate(slots) if s[0] in ("var", "param")]
    if not pending:
        return [(slots, where)]
    if depth >= MAX_FOLLOW:
        return [([_settle(unit, s) for s in slots], where)]
    _index(unit)
    binders = {i: _slot_binder(unit, slots[i]) for i in pending}
    first = binders[pending[0]]
    if first is None or first[0] == "value":
        new = list(slots)
        i = pending[0]
        new[i] = _settle(unit, slots[i]) if first is None else _value_slot(unit, first[1], slots[i])
        return _resolve(unit, new, where, depth + 1)
    d = first[1]
    group = [(i, b[2]) for i, b in binders.items() if b is not None and b[0] == "param" and b[1] == d]
    calls = _supplying_calls(unit, d, [spec for _, spec in group])
    if not calls:
        new = list(slots)
        for i, _ in group:
            new[i] = _settle(unit, slots[i])
        return _resolve(unit, new, where, depth + 1)
    out = []
    for c, vals in calls:
        new = list(slots)
        for (i, _), v in zip(group, vals):
            new[i] = v
        out.extend(_resolve(unit, new, c, depth + 1))
    return out


def _settle(unit, s):
    """A slot that cannot be followed further, as code: the variable's or parameter's name."""
    if s[0] == "var":
        return _slot("expr", s[1], s[2])
    if s[0] == "param":
        return _slot("expr", _param_name(unit.defs[s[3]], s[4]), s[2])
    return s


def _slot_binder(unit, s):
    if s[0] == "param":
        return ("param", s[3], s[4])
    return _binder(unit, s[1], s[2])


def _value_slot(unit, d, s):
    """The value of the variable slot s, bound by the definition d without parameters."""
    df = unit.defs[d]
    v = _arg_value(unit, df.eq + 1, df.end)
    if v[0] == "lit":
        return _slot("lit", v[1], s[2])
    if v[0] == "var":
        return v
    return _slot("expr", s[1], s[2])


def _param_spec(df, name):
    npos = 0
    for kind, label, var in df.params:
        if var == name:
            return ("label", label) if kind == "label" else ("pos", npos)
        if kind == "pos":
            npos += 1
    return None


def _param_name(df, spec):
    if spec[0] == "label":
        return spec[1]
    positional = [var for kind, _, var in df.params if kind == "pos"]
    if spec[1] < len(positional) and positional[spec[1]]:
        return positional[spec[1]]
    return "<arg %d>" % (spec[1] + 1)


def _binder(unit, name, pos):
    """How the variable `name` at token pos is bound: ("param", def, spec), ("value", def), or None."""
    _index(unit)
    order = unit.def_order
    i = bisect.bisect_left(order, pos)
    while i > 0:
        i -= 1
        d = order[i]
        df = unit.defs[d]
        if df.eq < pos < df.end:
            spec = _param_spec(df, name)
            if spec is not None:
                return None if _rebound(unit, name, df.eq, pos) else ("param", d, spec)
        elif pos >= df.end and df.name == name and _visible(unit, df, pos):
            if df.params or _rebound(unit, name, df.end, pos):
                return None
            return ("value", d)
    return None


def _visible(unit, df, pos):
    if df.toplevel:
        return True
    if df.end >= len(unit.toks) or word(unit.toks[df.end]) != "in":
        return False
    depth = 0
    for k in range(df.end + 1, pos):
        w = word(unit.toks[k])
        if w in OPENERS:
            depth += 1
        elif w in CLOSERS:
            depth -= 1
            if depth < 0:
                return False
        elif k in unit.toplevel_lets:
            return False
    return True


def _rebound(unit, name, start, pos):
    """True when a `fun` between start and pos binds `name` again."""
    toks = unit.toks
    for k in range(start, pos):
        if word(toks[k]) != "fun":
            continue
        for j in range(k + 1, min(pos, k + 40)):
            if word(toks[j]) == "->":
                break
            if toks[j].kind == "id" and toks[j].text == name:
                return True
    return False


def _supplying_calls(unit, d, specs):
    """[(call, [slot per spec])] for each call of the definition at d."""
    out = []
    for c in _calls_of(unit, d):
        positional, labels, end = _call_args(unit, c)
        vals = []
        for spec in specs:
            if spec[0] == "label" and spec[1] in labels:
                vals.append(_arg_value(unit, *labels[spec[1]]))
            elif spec[0] == "pos" and spec[1] < len(positional):
                vals.append(_arg_value(unit, *positional[spec[1]]))
            else:
                vals.append(_inherited(unit, d, c, end, spec, len(positional)))
        out.append((c, vals))
    return out


def _inherited(unit, d, c, end, spec, given):
    """A parameter that the call at c leaves out.  When the call is the whole body of a definition g
    (`let g x = f x`), it is the matching parameter of g; else it stays unresolved."""
    toks = unit.toks
    start = c
    while start >= 2 and word(toks[start - 1]) == "." and toks[start - 2].kind == "id":
        start -= 2
    g = unit.def_at_eq.get(start - 1)
    if g is not None and unit.defs[g].end == end:
        if spec[0] == "pos":
            spec = ("pos", sum(1 for p in unit.defs[g].params if p[0] == "pos") + spec[1] - given)
        return _slot("param", None, c, g, spec)
    return _slot("expr", _param_name(unit.defs[d], spec), c)


def _calls_of(unit, d):
    """Token indexes of the calls of the definition at d: unqualified ones in its scope, and qualified ones
    through a module of this file that holds it."""
    toks = unit.toks
    df = unit.defs[d]
    holders = [(name, e) for name, s, e in unit.mod_spans if s < d < e]
    mods = {name for name, _ in holders}
    stop = min([e for _, e in holders] or [len(toks)])
    if df.toplevel:
        for d2 in unit.def_order[bisect.bisect_right(unit.def_order, d):]:
            if unit.defs[d2].toplevel and unit.defs[d2].name == df.name:
                stop = min(stop, d2)
                break
    else:
        i = bisect.bisect_right(unit.top_starts, d)
        if i < len(unit.top_starts):
            stop = min(stop, unit.top_starts[i])
    out = []
    for k in range(df.end, len(toks)):
        t = toks[k]
        if t.kind != "id" or t.text != df.name:
            continue
        prev = unit.prev_word(k)
        if prev == ".":
            if df.toplevel and k >= 2 and toks[k - 2].text in mods:
                out.append(k)
        elif k < stop and prev not in NOT_A_CALL:
            out.append(k)
    return out


def _index(unit):
    """The `let`/`and` definitions of the unit, and the module spans that hold them."""
    if hasattr(unit, "defs"):
        return
    toks = unit.toks
    top_and, let_and = set(), set()
    stacks = collections.defaultdict(list)
    depth = 0
    for k, t in enumerate(toks):
        w = word(t)
        if w in OPENERS:
            depth += 1
        elif w in CLOSERS:
            stacks.pop(depth, None)
            depth = max(depth - 1, 0)
        elif w in LETS:
            stacks[depth].append(k)
        elif w in ANDS and stacks[depth]:
            let_and.add(k)
            if stacks[depth][-1] in unit.toplevel_lets:
                top_and.add(k)
        elif w == "in" and stacks[depth]:
            stacks[depth].pop()
    unit.top_starts = sorted(unit.toplevel_lets | top_and)
    unit.defs = {}
    for k, t in enumerate(toks):
        if word(t) in LETS or k in let_and:
            parsed = _parse_def(unit, k)
            if parsed:
                name, eq, params = parsed
                unit.defs[k] = Def(name, k in unit.toplevel_lets or k in top_and, eq, params, _def_end(unit, eq))
    unit.def_order = sorted(unit.defs)
    unit.def_at_eq = {df.eq: d for d, df in unit.defs.items()}
    unit.mod_spans = _module_spans(unit)


def _parse_def(unit, d):
    """(name, index of `=`, parameters) of `let [rec] name params [: type] =`, or None for a pattern binding."""
    toks = unit.toks
    n = len(toks)
    j = d + 1
    while j < n and word(toks[j]) in ("rec", "nonrec"):
        j += 1
    if j >= n or not is_lower_ident(toks[j]) or toks[j].text == "_":
        return None
    name = toks[j].text
    params = []
    j += 1
    while j < n:
        t = toks[j]
        w = word(t)
        if w == "=":
            return name, j, params
        if w == ":":
            eq = _depth0_find(unit, j, n, ("=",))
            return (name, eq, params) if eq < n else None
        if w in ("~", "?") and j + 1 < n and toks[j + 1].kind == "id":
            label = toks[j + 1].text
            var = label
            j += 2
            if j < n and word(toks[j]) == ":":
                e = unit.simple_expr(j + 1)
                inner = _strip_parens(toks[j + 1:e])
                var = inner[0].text if inner and is_lower_ident(inner[0]) else None
                j = e
            params.append(("label", label, var))
        elif w in ("~", "?") and j + 1 < n and word(toks[j + 1]) == "(":
            e = unit.match_close(j + 1)
            inner = toks[j + 2:e]
            label = inner[0].text if inner and is_lower_ident(inner[0]) else None
            params.append(("label", label, label))
            j = e + 1
        elif w in ("(", "[", "{"):
            e = unit.match_close(j)
            inner = _strip_parens(toks[j:e + 1])
            simple = inner and is_lower_ident(inner[0]) and (len(inner) == 1 or word(inner[1]) == ":")
            params.append(("pos", None, inner[0].text if simple and w == "(" else None))
            j = e + 1
        elif is_lower_ident(t):
            params.append(("pos", None, None if t.text == "_" else t.text))
            j += 1
        else:
            return None
    return None


def _def_end(unit, eq):
    """Index where the body that starts after the `=` at eq ends."""
    toks = unit.toks
    n = len(toks)
    depth = lets = 0
    k = eq + 1
    while k < n:
        w = word(toks[k])
        if w in OPENERS:
            depth += 1
        elif w in CLOSERS:
            if depth == 0:
                return k
            depth -= 1
        elif depth == 0 and w is not None:
            prev = unit.prev_word(k)
            if w in LETS:
                if k in unit.toplevel_lets:
                    return k
                lets += 1
            elif w == "in":
                if lets == 0:
                    return k
                lets -= 1
            elif w in ANDS:
                if lets == 0:
                    return k
            elif w in ITEM_KEYWORDS or (w in ("module", "open") and prev != "let") or (
                w == "exception" and prev not in ("let", "|", "with")
            ):
                return k
        k += 1
    return n


def _module_spans(unit):
    """(name, start, end) of each `module Name ... = struct ... end` of the unit."""
    toks = unit.toks
    spans = []
    for k, t in enumerate(toks):
        if word(t) != "module" or k + 1 >= len(toks) or toks[k + 1].kind != "id" or not toks[k + 1].text[:1].isupper():
            continue
        depth = 0
        for j in range(k + 2, min(len(toks), k + 200)):
            w = word(toks[j])
            if depth == 0 and w == "struct" and word(toks[j - 1]) == "=":
                spans.append((toks[k + 1].text, j, unit.match_close(j)))
                break
            if w in OPENERS:
                depth += 1
            elif w in CLOSERS:
                depth -= 1
                if depth < 0:
                    break
            elif depth == 0 and (w in LETS or w == "module"):
                break
    return spans


# --------------------------------------------------------------------------
# Tree scan and rulings check

# Census rows: CHANNELS.md rows 1-24, GRADE's M1-M7, CHANNELS.md section 2 items (S2.n), and rows the
# census check itself found missing from CHANNELS.md (N1-N5, defined in README.md).
VALID_ROWS = (
    {str(i) for i in range(1, 25)}
    | {"M%d" % i for i in range(1, 8)}
    | {"S2.%d" % i for i in range(1, 12)}
    | {"N1", "N2", "N3", "N4", "N5"}
)
DISPOSITIONS = ("row", "ruling", "ineligible")


def scan_tree(root, scope, scanners=(scan_source,)):
    """One site list per scanner.  Each file is read and tokenized once, for every scanner."""
    include = scope.get("include") or []
    exclude = [e.rstrip("/") for e in scope.get("exclude") or []]
    files = []
    for inc in include:
        base = os.path.join(root, inc)
        if os.path.isfile(base):
            files.append(inc)
            continue
        for dirpath, dirnames, filenames in os.walk(base):
            dirnames[:] = sorted(d for d in dirnames if d not in ("_build", ".git"))
            for fn in filenames:
                if fn.endswith((".ml", ".mlg")):
                    files.append(os.path.relpath(os.path.join(dirpath, fn), root).replace(os.sep, "/"))
    results = [[] for _ in scanners]
    for rel in sorted(set(files)):
        if any(rel == e or rel.startswith(e + "/") for e in exclude):
            continue
        with open(os.path.join(root, rel), encoding="utf-8", errors="surrogateescape") as f:
            src = f.read()
        cache = {}
        for out, scan in zip(results, scanners):
            out.extend(scan(rel, src, cache))
    return results


def describe(entry):
    for d in DISPOSITIONS:
        if d in entry:
            return "%s: %s" % (d, entry[d])
    return "?"


def validate(key, entry, reasons):
    if not isinstance(entry, dict):
        return "entry is not an object"
    present = [d for d in DISPOSITIONS if d in entry]
    if len(present) != 1:
        return "needs exactly one of row, ruling, ineligible"
    d = present[0]
    v = entry[d]
    if not isinstance(v, str) or not v.strip():
        return "%s must be a non-empty string" % d
    if d == "row" and v not in VALID_ROWS:
        return "unknown census row %r" % v
    if d != "row" and v.startswith("@") and v[1:] not in reasons:
        return "unknown reason %r" % v
    return None


def check(sites, rulings):
    entries = rulings.get("sites") or {}
    reasons = rulings.get("reasons") or {}
    problems = []
    found = set()
    for s in sites:
        found.add(s.key)
        entry = entries.get(s.key)
        if entry is None:
            problems.append("UNMAPPED %s %s:%d" % (s.key, s.path, s.line))
            continue
        err = validate(s.key, entry, reasons)
        if err is None and s.want:
            # A channel site's disposition repeats what the code passes: its row, or `@` and its reason.
            d, v = s.want
            expected = v if d == "row" else "@" + v
            if entry.get(d) != expected:
                err = "the code passes %s %r: the entry must be {%s}" % (d, v, json.dumps({d: expected})[1:-1])
        if err:
            problems.append("INVALID %s %s" % (s.key, err))
    for key in sorted(entries):
        if key not in found:
            problems.append("STALE %s" % key)
    return problems


def load_rulings(path, what):
    """The JSON object in path, or None after an error message on stderr."""
    try:
        with open(path, encoding="utf-8") as f:
            data = json.load(f)
    except (OSError, ValueError) as e:
        print("census_check: cannot read %s: %s" % (what, e), file=sys.stderr)
        return None
    if not isinstance(data, dict):
        print("census_check: %s file is not a JSON object: %s" % (what, path), file=sys.stderr)
        return None
    return data


def channel_rulings(args, rulings):
    """The channel rulings for this run: --channels, else channels.json beside the rulings file when it names
    the same source, else none (so every recorder read site is UNMAPPED).  None after a read error."""
    path = args.channels
    if path is None:
        sibling = os.path.join(os.path.dirname(args.rulings) or ".", "channels.json")
        if not os.path.isfile(sibling) or os.path.abspath(sibling) == os.path.abspath(args.rulings):
            return {"sites": {}}
        path = sibling
    channels = load_rulings(path, "channel rulings")
    if channels is not None and args.channels is None and channels.get("source") != rulings.get("source"):
        return {"sites": {}}
    return channels


def summary(label, sites, problems):
    counts = collections.Counter(s.kind for s in sites)
    return "census_check: %d %s (%s), %d problems" % (
        len(sites), label, ", ".join("%s %d" % kv for kv in sorted(counts.items())), len(problems),
    )


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--root", required=True, help="source tree to scan")
    parser.add_argument("--rulings", required=True, help="rulings JSON file")
    parser.add_argument(
        "--channels",
        help="channel rulings JSON file for the recorder's read sites (default: channels.json beside the rulings "
        "file, when its source is the same; without one, every read site is unmapped)",
    )
    parser.add_argument("--list", action="store_true", help="print every site with its disposition")
    try:
        args = parser.parse_args(argv)
    except SystemExit as e:
        return 0 if e.code == 0 else 2
    if not os.path.isdir(args.root):
        print("census_check: not a directory: %s" % args.root, file=sys.stderr)
        return 2
    rulings = load_rulings(args.rulings, "rulings")
    if rulings is None:
        return 2
    scope = rulings.get("scope")
    if not isinstance(scope, dict) or not scope.get("include"):
        print("census_check: rulings file needs a scope with an include list", file=sys.stderr)
        return 2
    channels = channel_rulings(args, rulings)
    if channels is None:
        return 2
    channel_scope = channels.get("scope")
    if not isinstance(channel_scope, dict) or not channel_scope.get("include"):
        channel_scope = scope
    try:
        if channel_scope == scope:
            sites, channel_sites = scan_tree(args.root, scope, (scan_source, scan_channels))
        else:
            (sites,) = scan_tree(args.root, scope)
            (channel_sites,) = scan_tree(args.root, channel_scope, (scan_channels,))
    except OSError as e:
        print("census_check: cannot read source: %s" % e, file=sys.stderr)
        return 2
    if args.list:
        for group, data in ((sites, rulings), (channel_sites, channels)):
            entries = data.get("sites") or {}
            for s in group:
                entry = entries.get(s.key)
                print("%s:%d\t%s\t%s" % (s.path, s.line, s.key, describe(entry) if entry else "UNMAPPED"))
    state_problems = check(sites, rulings)
    channel_problems = check(channel_sites, channels)
    for p in state_problems + channel_problems:
        print(p)
    print(summary("sites", sites, state_problems), file=sys.stderr)
    print(summary("channel sites", channel_sites, channel_problems), file=sys.stderr)
    return 1 if state_problems or channel_problems else 0


if __name__ == "__main__":
    sys.exit(main())
