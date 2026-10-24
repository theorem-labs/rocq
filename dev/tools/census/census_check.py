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

Exit status: 0 when every site is ruled and every ruling names a site, 1 when
a site is unmapped or a ruling is stale or invalid (one per line on stdout),
2 on a usage or read error.  Python 3.8+, standard library only.
"""

import argparse
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

Site = collections.namedtuple("Site", "kind path line key")

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


def scan_source(path, src):
    """All census sites of one file, with stable keys."""
    unit = Unit(path, src)
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


def scan_tree(root, scope):
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
    sites = []
    for rel in sorted(set(files)):
        if any(rel == e or rel.startswith(e + "/") for e in exclude):
            continue
        with open(os.path.join(root, rel), encoding="utf-8", errors="surrogateescape") as f:
            sites.extend(scan_source(rel, f.read()))
    return sites


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
        if err:
            problems.append("INVALID %s %s" % (s.key, err))
    for key in sorted(entries):
        if key not in found:
            problems.append("STALE %s" % key)
    return problems


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--root", required=True, help="source tree to scan")
    parser.add_argument("--rulings", required=True, help="rulings JSON file")
    parser.add_argument("--list", action="store_true", help="print every site with its disposition")
    try:
        args = parser.parse_args(argv)
    except SystemExit as e:
        return 0 if e.code == 0 else 2
    if not os.path.isdir(args.root):
        print("census_check: not a directory: %s" % args.root, file=sys.stderr)
        return 2
    try:
        with open(args.rulings, encoding="utf-8") as f:
            rulings = json.load(f)
    except (OSError, ValueError) as e:
        print("census_check: cannot read rulings: %s" % e, file=sys.stderr)
        return 2
    scope = rulings.get("scope") if isinstance(rulings, dict) else None
    if not isinstance(scope, dict) or not scope.get("include"):
        print("census_check: rulings file needs a scope with an include list", file=sys.stderr)
        return 2
    try:
        sites = scan_tree(args.root, scope)
    except OSError as e:
        print("census_check: cannot read source: %s" % e, file=sys.stderr)
        return 2
    entries = rulings.get("sites") or {}
    if args.list:
        for s in sites:
            entry = entries.get(s.key)
            print("%s:%d\t%s\t%s" % (s.path, s.line, s.key, describe(entry) if entry else "UNMAPPED"))
    problems = check(sites, rulings)
    for p in problems:
        print(p)
    counts = collections.Counter(s.kind for s in sites)
    print(
        "census_check: %d sites (%s), %d problems"
        % (len(sites), ", ".join("%s %d" % kv for kv in sorted(counts.items())), len(problems)),
        file=sys.stderr,
    )
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
