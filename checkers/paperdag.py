#!/usr/bin/env python3
"""paper-dag/1: lint, score, hash and verify a substitution. Standard library only.

The reference verifier of the paper-dag skill. It implements the structural checks S1 to S10 of
references/format.md and lists the semantic obligations; it judges none of them. S6 includes the
full-proofs floor: a proof that names a removed node or uses deferral or sketch wording is refused.

  python3 paperdag.py lint dag.json
  python3 paperdag.py score dag.json
  python3 paperdag.py hash dag.json
  python3 paperdag.py verify dag.json substitution.json --out result.json [--write-dag new_dag.json]
"""
import hashlib
import json
import math
import re
import sys

RESULTS = ("theorem", "lemma", "proposition", "corollary")

# The full-proofs floor of S6. A proof must be complete in its own words: wording that defers to the paper, to
# the original or a removed proof, or to the reader, and wording that announces a sketch or an idea, is refused
# by code before any reviewer reads it. Passing this floor proves nothing: the reviewer still judges the proof.
DEFERRAL = [
    r"\b(?:the|this|that|their) (?:paper|article|preprint|manuscript|source)\b",
    r"\b(?:original|published|authors'?|author's|base|previous|former|old|replaced|removed|deleted|existing) "
    r"(?:proof|proofs|argument|arguments|derivation|text|version|paper|lemma|node|nodes|dag)\b",
    r"\b(?:same|identical) (?:proof|argument|reasoning|derivation) as\b",
    r"\b(?:proof|argument|derivation|reasoning) (?:is|remains|stays|goes|carries over) (?:the same|unchanged|as before|identical|verbatim)\b",
    r"\bas (?:before|in the original|originally|in the base)\b",
    r"\b(?:unchanged|verbatim|mutatis mutandis)\b",
    r"\bpraxis-lean\b|\beprint\b|\barxiv\b",
    r"\bleft (?:to|for) the reader\b|\bleft as an exercise\b|\bexercise for the reader\b",
    r"\b(?:proof|proofs|details?|verification|calculation|computation|argument|rest|remainder|remaining cases?|other cases?) "
    r"(?:is |are |was |were )?(?:omitted|left out|skipped|routine|not given|not shown)\b",
    r"\bwe (?:omit|skip|leave|do not give|do not prove)\b|\bomitted\b",
    r"\b(?:todo|tbd|to be completed|to be filled|to be written|placeholder)\b",
    r"\b(?:proof )?(?:sketch|outline)\b|\bsketch of\b|\b(?:the|main|key|proof) idea\b|\bidea of (?:the )?proof\b|^\s*idea\b",
    r"\bin (?:brief|outline)\b|\broughly speaking\b|\bheuristically\b|\bintuitively\b",
]
_DEFERRAL = [re.compile(p, re.I) for p in DEFERRAL]


def deferral(proof, removed_nodes):
    """The first wording in `proof` that the full-proofs floor refuses, or "" if there is none."""
    text = norm(proof)
    for rx in _DEFERRAL:
        m = rx.search(text)
        if m:
            return m.group(0)
    for n in removed_nodes:
        for name in (n.get("id"), n.get("label")):
            if isinstance(name, str) and len(name) >= 3:
                m = re.search(r"(?<![\w:.-])" + re.escape(name) + r"(?![\w'\u2032\u2019:-]|\.\d)", text, re.I)
                if m:
                    return m.group(0)
    return ""

SUB_FORMAT = "paper-dag-substitution/1"
DAG_FORMAT = "paper-dag/1"


def load(path):
    with open(path, encoding="utf-8") as handle:
        return json.load(handle)


def norm(text):
    return " ".join(text.split()) if isinstance(text, str) else ""


# Score: proof steps (paper-dag-steps-v1).
# A proof is split into steps: a new line, or the end of a sentence or clause (".", ";" or ":" followed by space).
# A step costs 1, plus 1 for every further STEP_TOKENS canonical tokens in it. Canonical tokens are words, numbers
# and single symbols after LaTeX markup is dropped, so $\mathbf{W}$, \mathbf{W} and W are each one token. A
# result costs the steps of its proof; its statement is free, so merging or splitting results does not change the
# score. A cited theorem costs 1.
STEP_TOKENS = 60
_ENV = re.compile(r"\\(begin|end)\{[^}]*\}(\[[^\]]*\])?")
_REF = re.compile(r"\\(cref|Cref|ref|cite|label|eqref)\*?(\[[^\]]*\])?\{[^}]*\}")
_STYLE = re.compile(r"\\(mathbf|mathrm|mathsf|mathcal|mathbb|mathfrak|mathit|bm|textsf|textit|textbf|textrm|text|"
                    r"emph|operatorname|hat|tilde|bar|overline|left|right|big|Big|bigl|bigr|Bigl|Bigr|displaystyle)\b\s*")
_MACRO = re.compile(r"\\[a-zA-Z]+")
_MARK = re.compile(r"[{}$&]|\\[,;:! ]|~")
_TOKEN = re.compile(r"[^\W\d_]+|\d+|[^\w\s]")
_PUNCT = set(".,;:()[]")
_SPLIT = re.compile(r"(?<=[.;:])\s+|\n+")


def plain(text):
    """Drop LaTeX markup: environments, references, style macros, braces and dollars; other macros become one symbol."""
    t = text if isinstance(text, str) else ""
    t = _ENV.sub(" ", t)
    t = _REF.sub(" R ", t)
    t = _STYLE.sub(" ", t)
    t = _MACRO.sub(" x ", t)
    return _MARK.sub(" ", t)


def tokens(unit):
    return [x for x in _TOKEN.findall(unit) if x not in _PUNCT]


def steps(text):
    total = 0
    for unit in _SPLIT.split(plain(text)):
        n = len(tokens(unit))
        if n:
            total += 1 + (n - 1) // STEP_TOKENS
    return total


def cost(node, width=None):
    kind = node.get("kind")
    if kind in RESULTS:
        return steps(node.get("proof"))
    if kind == "external":
        return 1
    return 0


def score(dag):
    by_node = {n["id"]: cost(n) for n in dag["nodes"] if n.get("kind") != "blob"}
    return {"steps": sum(by_node.values()), "by_node": by_node}


def canonical_hash(dag):
    text = json.dumps(dag, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def _acyclic(ids, edges):
    indegree = {i: 0 for i in ids}
    out = {i: [] for i in ids}
    for a, b in edges:
        if a in out and b in indegree:
            out[a].append(b)
            indegree[b] += 1
    queue = [i for i, d in indegree.items() if d == 0]
    seen = 0
    while queue:
        i = queue.pop()
        seen += 1
        for j in out[i]:
            indegree[j] -= 1
            if indegree[j] == 0:
                queue.append(j)
    return seen == len(indegree)


def _text(value):
    return isinstance(value, str) and bool(value.strip())


def lint(dag):
    errors, warnings = [], []
    if not isinstance(dag, dict) or dag.get("format") != DAG_FORMAT:
        return {"errors": ["format is not " + DAG_FORMAT], "warnings": []}
    ids = set()
    for n in dag.get("nodes", []):
        i = n.get("id")
        if not _text(i) or " " in i or i in ids:
            errors.append(f"node id missing, repeated or with a space: {i!r}")
            continue
        ids.add(i)
        kind = n.get("kind")
        if kind not in RESULTS + ("external", "blob"):
            errors.append(f"{i}: unknown kind {kind!r}")
        if not _text(n.get("statement")):
            errors.append(f"{i}: empty statement")
        if kind in RESULTS and not _text(n.get("proof")):
            errors.append(f"{i}: a result needs a proof")
    kinds = {n.get("id"): n.get("kind") for n in dag.get("nodes", [])}
    for e in dag.get("edges", []):
        a, b = e.get("from"), e.get("to")
        if a not in ids or b not in ids:
            errors.append(f"edge {a} -> {b}: unknown node")
            continue
        if e.get("kind") not in ("uses", "background"):
            errors.append(f"edge {a} -> {b}: kind must be uses or background")
        if e.get("kind") == "uses" and not _text(e.get("demand")):
            errors.append(f"edge {a} -> {b}: a uses edge needs a demand")
        if e.get("kind") == "background" and kinds.get(a) != "blob":
            errors.append(f"edge {a} -> {b}: a background edge starts at a blob")
        if e.get("leaky"):
            warnings.append(f"edge {a} -> {b}: leaky")
    if not _acyclic(ids, [(e.get("from"), e.get("to")) for e in dag.get("edges", [])]):
        errors.append("the graph has a cycle")
    for t in dag.get("targets", []):
        if kinds.get(t) not in RESULTS:
            errors.append(f"target {t} is missing or not a result")
    return {"errors": errors, "warnings": warnings}


_MACRO_USE = re.compile(r"\\([A-Za-z]+)")
_ENV_USE = re.compile(r"\\begin\{([^}]*)\}")
# Commands that change layout, spacing or definitions: they shrink print without shortening a proof.
LAYOUT = set("newcommand renewcommand providecommand def edef gdef let DeclareMathOperator vspace hspace vskip hskip "
             "kern mkern mskip moveleft moveright raisebox lower raise small footnotesize scriptsize tiny normalsize "
             "looseness resizebox scalebox parbox minipage multicols columnbreak linebreak newline pagebreak newpage "
             "enlargethispage baselineskip baselinestretch setlength addtolength smash makebox framebox rlap llap "
             "mathrlap mathllap mathclap clap negthinspace negmedspace negthickspace includegraphics input include "
             "tabular tabularx multicolumn hfil hfill hss vfill strut displaystyle textstyle scriptstyle scriptscriptstyle "
             "fontsize selectfont mathchoice".split())


MATH_ENVS = set("equation equation* align align* aligned gather gather* gathered split multline multline* cases "
                "matrix pmatrix bmatrix vmatrix Vmatrix smallmatrix array itemize enumerate description".split())


def vocabulary(dag):
    """Macros and environments that occur anywhere in the protected DAG's text."""
    texts = []
    for n in dag["nodes"]:
        texts += [n.get("statement") or "", n.get("proof") or "", n.get("name") or ""]
    texts += [e.get("demand") or "" for e in dag["edges"]]
    blob = "\n".join(texts)
    return set(_MACRO_USE.findall(blob)), set(_ENV_USE.findall(blob))


def _printlines():
    """The printed-lines model (the source in _PRINTLINES below, with the paper fonts' glyph widths), as a module."""
    import types
    module = types.ModuleType("printlines")
    module.__dict__["WIDTHS_JSON"] = _WIDTHS_JSON
    exec(compile(_PRINTLINES, "printlines", "exec"), module.__dict__)
    return module


# Calibration, against XeLaTeX on the paper's own source: a result of the paper costs its measured typeset height
# (PAPER_HEIGHTS at the end of this file, in 12 pt lines, statement and proof with the space around them); any other result
# costs LINE_SLOPE * node_lines() + LINE_RESULT, fitted on 41 submitted results typeset in place (residual 1.1 lines).
# LINE_FIXED is the rest of the paper, so the paper as published scores PAPER_LINES.
LINE_SLOPE = 1.040
LINE_RESULT = 1.59
PAPER_LINES = 3572
# S10: only an improvement of more than 100 lines is accepted. RECORD_LINES is the record when this version opened
# (3525 lines, submission fd44f9ab on the previous track); a non-empty substitution must print at most
# RECORD_LINES - MIN_GAIN - 1 lines.
RECORD_LINES = 3525
MIN_GAIN = 100
MAX_LINES = RECORD_LINES - MIN_GAIN - 1


def _heights():
    return dict(PAPER_HEIGHTS)


_BASE = {}


def lines(dag, base=None):
    """Printed lines of the paper this DAG describes: the fixed text plus every result's statement and proof."""
    pl, h = _printlines(), _heights()
    paper = base or dag
    key = canonical_hash(paper)
    if key not in _BASE:
        _BASE[key] = {n["id"]: (n.get("statement"), n.get("proof")) for n in paper["nodes"]}
    orig = _BASE[key]
    by_node = {}
    for n in dag["nodes"]:
        if n.get("kind") not in RESULTS:
            continue
        same = n["id"] in h and orig.get(n["id"]) == (n.get("statement"), n.get("proof"))
        by_node[n["id"]] = h[n["id"]] if same else LINE_SLOPE * pl.node_lines(n) + LINE_RESULT
    fixed = PAPER_LINES - sum(h.values())
    return {"lines": int(round(fixed + sum(by_node.values()))), "by_node": {k: round(v, 1) for k, v in by_node.items()}}


def _plan(dag, sub):
    """Everything S1 to S7 needs, with the errors found on the way."""
    errors = []

    def err(check, message):
        errors.append({"check": check, "message": message})

    nodes = {n["id"]: n for n in dag["nodes"]}
    remove = sub.get("remove")
    add = sub.get("add")
    edges = sub.get("edges")
    discharge = sub.get("discharge")
    replaces = sub.get("replaces", {})
    for name, value, kind in (("remove", remove, list), ("add", add, list), ("edges", edges, list),
                              ("discharge", discharge, list), ("replaces", replaces, dict)):
        if not isinstance(value, kind):
            err("format", f"`{name}` is missing or not a {kind.__name__}")
    if sub.get("format") != SUB_FORMAT:
        err("format", "format is not " + SUB_FORMAT)
    if errors:
        return None, errors

    # S1
    held = canonical_hash(dag)
    if sub.get("base") != held:
        err("S1", f"base is not the hash of the DAG the verifier holds ({held})")

    # S2
    removed = set()
    for i in remove:
        if not isinstance(i, str) or i not in nodes:
            err("S2", f"remove lists {i!r}, which is not a node of the base")
        elif nodes[i].get("kind") == "blob":
            err("S2", f"remove lists the blob {i}; blobs are fixed")
        elif i in removed:
            err("S2", f"remove lists {i} twice")
        else:
            removed.add(i)
    added = {}
    for n in add:
        i = n.get("id") if isinstance(n, dict) else None
        if not _text(i) or " " in i:
            err("S2", f"an added node has no usable id: {i!r}")
        elif i in nodes:
            err("S2", f"added id {i} is already a node of the base")
        elif i in added:
            err("S2", f"added id {i} is used twice")
        elif n.get("kind") not in RESULTS + ("external",):
            err("S2", f"added node {i} has kind {n.get('kind')!r}; only results and externals can be added")
        else:
            added[i] = n
    kept = {i for i in nodes if i not in removed}

    # S3
    targets = list(dag.get("targets", []))
    new_targets = []
    for key, value in replaces.items():
        if key not in added or added[key].get("kind") not in RESULTS:
            err("S3", f"replaces maps {key!r}, which is not an added result")
        if value not in removed:
            err("S3", f"replaces names {value!r}, which is not a removed node")
    for t in targets:
        if t not in removed:
            new_targets.append(t)
            continue
        heirs = [k for k, v in replaces.items() if v == t and k in added and added[k].get("kind") in RESULTS]
        if len(heirs) != 1:
            err("S3", f"target {t} is removed and replaces maps {len(heirs)} added results to it, not exactly one")
        elif norm(added[heirs[0]].get("statement")) != norm(nodes[t].get("statement")):
            err("S3", f"the statement of {heirs[0]} is not identical to that of the target {t}")
        else:
            new_targets.append(heirs[0])

    # S4
    obligations = {(e["from"], e["to"]): e for e in dag["edges"] if e["from"] in removed and e["to"] in kept}
    met = {}
    for d in discharge:
        edge = d.get("edge") if isinstance(d, dict) else None
        key = tuple(edge) if isinstance(edge, list) and len(edge) == 2 and all(isinstance(x, str) for x in edge) else None
        if key is None or key not in obligations:
            err("S4", f"discharge names {edge!r}, which is not an obligation of this cut")
            continue
        if key in met:
            err("S4", f"edge {key[0]} -> {key[1]} is discharged more than once")
            continue
        by = d.get("by")
        if not isinstance(by, list) or not by or any(b not in added and b not in kept for b in by):
            err("S4", f"edge {key[0]} -> {key[1]}: `by` must be a non-empty list of added or kept nodes")
            continue
        if any(nodes.get(b, {}).get("kind") == "blob" for b in by):
            err("S4", f"edge {key[0]} -> {key[1]}: `by` names a blob; blobs give background, not results, "
                      "so an obligation is discharged only by results and externals")
            continue
        if not _text(d.get("argument")):
            err("S4", f"edge {key[0]} -> {key[1]}: empty argument")
            continue
        met[key] = d
    for key in obligations:
        if key not in met:
            err("S4", f"edge {key[0]} -> {key[1]} leaves the removed set and is not discharged")

    # S5
    good_edges = []
    for e in edges:
        a, b = (e.get("from"), e.get("to")) if isinstance(e, dict) else (None, None)
        if b not in added:
            err("S5", f"edge {a} -> {b} does not end at an added node")
        elif a not in added and a not in kept:
            err("S5", f"edge {a} -> {b} does not start at an added node, a kept node or a blob")
        elif e.get("kind") not in ("uses", "background"):
            err("S5", f"edge {a} -> {b}: kind must be uses or background")
        elif e.get("kind") == "uses" and nodes.get(a, {}).get("kind") == "blob":
            err("S5", f"edge {a} -> {b}: an edge from a blob is a background edge, never uses")
        elif e.get("kind") == "uses" and not _text(e.get("demand")):
            err("S5", f"edge {a} -> {b}: a uses edge carries a non-empty demand")
        else:
            good_edges.append(e)

    # S6
    deny = [d.lower() for d in dag.get("import_denylist", []) if isinstance(d, str) and d]
    for i, n in added.items():
        if n.get("kind") in RESULTS:
            if not _text(n.get("statement")) or not _text(n.get("proof")):
                err("S6", f"added result {i} needs a non-empty statement and proof")
            else:
                bad = deferral(n.get("proof"), [nodes[r] for r in (remove if isinstance(remove, list) else []) if isinstance(r, str) and r in nodes])
                if bad:
                    err("S6", f"added result {i}: the proof must be complete in its own words, and {bad!r} defers to "
                              "the paper, to a removed or original proof or to the reader, or announces a sketch")
        else:
            ref = n.get("ref") if isinstance(n.get("ref"), dict) else {}
            if not _text(n.get("statement")):
                err("S6", f"added external {i} needs a non-empty statement")
            if not all(_text(ref.get(k)) for k in ("citation", "locator", "quote")):
                err("S6", f"added external {i} needs ref.citation, ref.locator and ref.quote")
            for field in ("citation", "url", "quote"):
                value = ref.get(field)
                hit = [d for d in deny if isinstance(value, str) and d in value.lower()]
                if hit:
                    err("S6", f"added external {i}: ref.{field} names {hit[0]!r}, which is on the import_denylist")

    # S7
    new_ids = kept | set(added)
    new_edges = [(e["from"], e["to"]) for e in dag["edges"] if e["from"] in kept and e["to"] in kept]
    new_edges += [(e["from"], e["to"]) for e in good_edges]
    new_edges += [(b, key[1]) for key, d in met.items() for b in d["by"]]
    if not _acyclic(new_ids, new_edges):
        err("S7", "the resulting graph has a cycle")
    for t in new_targets:
        if t not in new_ids:
            err("S7", f"target {t} is not in the resulting graph")

    # S9: lines may only fall because less mathematics is printed: no layout, spacing or definition commands, and
    # only the environments the paper and ordinary mathematics use
    envs = vocabulary(dag)[1] | MATH_ENVS
    for i, n in enumerate(sub.get("add") or []):
        if not isinstance(n, dict):
            continue
        for field in ("statement", "proof", "name"):
            text = n.get(field) if isinstance(n.get(field), str) else ""
            for m in sorted(set(_MACRO_USE.findall(text)) & LAYOUT):
                err("S9", f"added node {i} ({n.get('id')!r}): \\{m} in its {field} is a layout, spacing or definition command")
            for e in sorted(set(_ENV_USE.findall(text)) - envs):
                err("S9", f"added node {i} ({n.get('id')!r}): environment {e!r} in its {field} is not one the paper or ordinary mathematics uses")
    return {"nodes": nodes, "removed": removed, "added": added, "kept": kept, "edges": good_edges,
            "met": met, "obligations": obligations, "targets": new_targets}, errors


def apply(dag, sub):
    plan, _ = _plan(dag, sub)
    if plan is None:
        raise ValueError("the substitution is not well formed")
    new = {k: v for k, v in dag.items() if k not in ("nodes", "edges", "targets")}
    new["targets"] = plan["targets"]
    new["nodes"] = [n for n in dag["nodes"] if n["id"] in plan["kept"]] + list(plan["added"].values())
    new["edges"] = [e for e in dag["edges"] if e["from"] in plan["kept"] and e["to"] in plan["kept"]]
    new["edges"] += plan["edges"]
    for (a, b), d in plan["met"].items():
        base = plan["obligations"][(a, b)]
        for by in d["by"]:
            new["edges"].append({"from": by, "to": b, "kind": "uses", "demand": base.get("demand", ""),
                                 "clause": "discharges " + a + " -> " + b, "where": base.get("where", "")})
    return new


def _obligations(dag, plan):
    nodes, added = plan["nodes"], plan["added"]

    def view(i):
        n = added.get(i) or nodes.get(i) or {}
        return {"id": i, "label": n.get("label", ""), "kind": n.get("kind", ""), "statement": n.get("statement", "")}

    out = []
    for (a, b), d in plan["met"].items():
        base = plan["obligations"][(a, b)]
        out.append({"id": f"O-discharge:{a}>{b}", "type": "discharge",
                    "question": "Given only the statements of the `by` nodes, does the demand follow as stated, "
                                "with the same constants, bounds and hypotheses?",
                    "given": {"demand": base.get("demand", ""), "clause": base.get("clause", ""),
                              "consumer": view(b), "by": [view(x) for x in d["by"]]},
                    "argument": d.get("argument", "")})
    for i, n in added.items():
        if n.get("kind") in RESULTS:
            incoming = [e for e in plan["edges"] if e["to"] == i]
            out.append({"id": f"O-proof:{i}", "type": "proof",
                        "question": "Is the proof complete and correct, using only the node's own incoming demands, "
                                    "the blobs it is linked to, and standard mathematics?",
                        "given": {"statement": n.get("statement", ""), "proof": n.get("proof", ""),
                                  "incoming": [{"from": view(e["from"]), "kind": e.get("kind"),
                                                "demand": e.get("demand", "")} for e in incoming]},
                        "argument": ""})
        else:
            out.append({"id": f"O-cite:{i}", "type": "cite",
                        "question": "Does the cited source state this, at this locator, as quoted, and is the node's "
                                    "statement a faithful reading of the quote?",
                        "given": {"statement": n.get("statement", ""), "ref": n.get("ref", {})},
                        "argument": ""})
    return out


def verify(dag, sub):
    base = score(dag)
    result = {"structural_ok": False, "errors": [], "warnings": [], "base_steps": base["steps"], "steps": None,
              "base_lines": lines(dag)["lines"], "lines": None, "lines_by_node": {},
              "saved": None, "by_node": {}, "obligations": []}
    if not isinstance(sub, dict):
        result["errors"] = [{"check": "format", "message": "the substitution is not a JSON object"}]
        return result
    plan, errors = _plan(dag, sub)
    result["errors"] = errors
    if plan is None or errors:
        return result
    new = apply(dag, sub)
    scored = score(new)  # S8
    printed = lines(new, dag)
    result.update(lines=printed["lines"], lines_by_node=printed["by_node"])
    if (sub.get("remove") or sub.get("add")) and printed["lines"] > MAX_LINES:
        result["errors"] = [{"check": "S10", "message": f"prints {printed['lines']} lines; only an improvement of more than "
                             f"{MIN_GAIN} lines on the record {RECORD_LINES} is accepted, so at most {MAX_LINES} lines"}]
        result["structural_ok"] = False
        return result
    result.update(structural_ok=True, steps=scored["steps"], saved=base["steps"] - scored["steps"],
                  by_node=scored["by_node"], obligations=_obligations(dag, plan))
    return result


def main(argv):
    try:
        command = argv[1]
        dag = load(argv[2])
        if command == "lint":
            out = lint(dag)
            print(json.dumps(out, indent=1, ensure_ascii=False))
            return 1 if out["errors"] else 0
        if command == "score":
            print(json.dumps({**score(dag), **{"lines": lines(dag)["lines"]}}, ensure_ascii=False))
            return 0
        if command == "hash":
            print(canonical_hash(dag))
            return 0
        if command == "verify":
            sub = load(argv[3])
            result = verify(dag, sub)
            if "--out" in argv:
                with open(argv[argv.index("--out") + 1], "w", encoding="utf-8") as handle:
                    json.dump(result, handle, indent=1, ensure_ascii=False)
            else:
                print(json.dumps(result, indent=1, ensure_ascii=False))
            if "--write-dag" in argv and result["structural_ok"]:
                with open(argv[argv.index("--write-dag") + 1], "w", encoding="utf-8") as handle:
                    json.dump(apply(dag, sub), handle, indent=1, ensure_ascii=False)
            return 0 if result["structural_ok"] else 1
    except (OSError, ValueError, IndexError, KeyError, TypeError) as exc:
        print("unreadable input: " + str(exc), file=sys.stderr)
        return 2
    print(__doc__, file=sys.stderr)
    return 2


# ---------------------------------------------------------------- printed-lines model data
# Measured typeset height of each result of the paper, in 12 pt lines (XeLaTeX on the arXiv source; a measurement
# disturbed by a float or by a proof set elsewhere is replaced by the paper-fitted model).
PAPER_HEIGHTS = {"cor:asymptotics": 16.24, "cor:ext-error": 12.64, "lem:charged": 36.87, "lem:classification": 46.93, "lem:degree": 14.63, "lem:extractor": 24.25, "lem:gp-rank": 12.79, "lem:half": 6.52, "lem:heavy": 13.0, "lem:honest": 18.51, "lem:init": 5.93, "lem:inverse": 50.18, "lem:lattice-facts": 17.02, "lem:ledger": 10.0, "lem:lift": 30.97, "lem:moore": 7.03, "lem:names": 11.96, "lem:prefix": 32.07, "lem:qap": 20.93, "lem:range": 16.26, "lem:rank-one": 7.89, "lem:reduction": 37.63, "lem:regularize": 29.62, "lem:sparse": 37.38, "lem:trim": 11.72, "lem:view": 60.71, "lem:we-hiding": 9.54, "prop:efficiency": 40.95, "prop:hs-dimension": 7.87, "prop:reduction-time": 38.75, "thm:correct": 15.03, "thm:extraction": 27.45}

# Glyph advance widths (per 1000 em) of the paper's fonts: NewCM10 Book, Book Italic, Bold, and NewCM Math.
_WIDTHS_JSON = r'''{"rm":{"32":333,"33":278,"34":374,"35":833,"36":500,"37":833,"38":778,"39":278,"40":389,"41":389,"42":500,"43":778,"44":278,"45":333,"46":278,"47":500,"48":500,"49":500,"50":500,"51":500,"52":500,"53":500,"54":500,"55":500,"56":500,"57":500,"58":278,"59":278,"60":778,"61":778,"62":778,"63":472,"64":778,"65":750,"66":708,"67":722,"68":764,"69":681,"70":653,"71":785,"72":750,"73":361,"74":514,"75":778,"76":625,"77":917,"78":750,"79":778,"80":681,"81":778,"82":736,"83":556,"84":722,"85":750,"86":750,"87":1028,"88":750,"89":750,"90":611,"91":278,"92":500,"93":278,"94":556,"95":750,"96":500,"97":500,"98":556,"99":444,"100":556,"101":444,"102":306,"103":500,"104":556,"105":278,"106":306,"107":528,"108":278,"109":833,"110":556,"111":500,"112":556,"113":528,"114":392,"115":394,"116":389,"117":556,"118":528,"119":722,"120":528,"121":528,"122":444,"123":500,"124":278,"125":500,"126":556,"160":500,"161":278,"162":444,"163":750,"164":778,"165":750,"166":278,"167":484,"168":500,"169":683,"170":449,"171":556,"172":778,"173":333,"174":683,"175":500,"176":375,"177":778,"178":359,"179":359,"180":500,"181":556,"182":611,"183":278,"184":444,"185":366,"186":419,"187":556,"188":825,"189":825,"190":825,"191":472,"192":750,"193":750,"194":750,"195":750,"196":750,"197":750,"198":903,"199":722,"200":681,"201":681,"202":681,"203":681,"204":361,"205":361,"206":361,"207":361,"208":764,"209":750,"210":778,"211":778,"212":778,"213":778,"214":778,"215":778,"216":778,"217":750,"218":750,"219":750,"220":750,"221":750,"222":625,"223":500,"224":500,"225":500,"226":500,"227":500,"228":500,"229":500,"230":722,"231":444,"232":444,"233":444,"234":444,"235":444,"236":278,"237":278,"238":278,"239":278,"240":500,"241":556,"242":500,"243":500,"244":500,"245":500,"246":500,"247":778,"248":500,"249":556,"250":556,"251":556,"252":556,"253":528,"254":556,"255":528,"256":750,"257":500,"258":750,"259":500,"260":750,"261":500,"262":722,"263":444,"264":722,"265":444,"266":722,"267":444,"268":722,"269":444,"270":764,"271":556,"272":764,"273":556,"274":681,"275":444,"276":681,"277":444,"278":681,"279":444,"280":681,"281":444,"282":681,"283":444,"284":785,"285":500,"286":785,"287":500,"288":785,"289":500,"290":785,"291":500,"292":750,"293":556,"294":750,"295":556,"296":361,"297":278,"298":361,"299":278,"300":361,"301":278,"302":361,"303":278,"304":361,"305":278,"306":839,"307":556,"308":514,"309":306,"310":778,"311":528,"312":531,"313":625,"314":278,"315":625,"316":278,"317":625,"318":278,"319":625,"320":456,"321":625,"322":336,"323":750,"324":556,"325":750,"326":556,"327":750,"328":556,"329":601,"330":750,"331":506,"332":778,"333":500,"334":778,"335":500,"336":778,"337":500,"338":1014,"339":778,"340":736,"341":392,"342":736,"343":392,"344":736,"345":392,"346":556,"347":394,"348":556,"349":394,"350":556,"351":394,"352":556,"353":394,"354":722,"355":389,"356":722,"357":389,"358":722,"359":388,"360":750,"361":556,"362":750,"363":556,"364":750,"365":556,"366":750,"367":556,"368":750,"369":556,"370":750,"371":556,"372":1028,"373":722,"374":750,"375":528,"376":750,"377":611,"378":444,"379":611,"380":444,"381":611,"382":444,"383":306,"880":560,"881":456,"882":722,"883":500,"884":194,"885":194,"886":750,"887":613,"890":111,"891":591,"892":591,"893":591,"894":278,"895":514,"900":167,"901":278,"902":750,"903":278,"904":874,"905":944,"906":559,"908":852,"910":930,"911":836,"912":250,"913":750,"914":708,"915":625,"916":833,"917":680,"918":611,"919":750,"920":778,"921":361,"922":778,"923":694,"924":916,"925":750,"926":667,"927":778,"928":750,"929":680,"931":722,"932":722,"933":778,"934":722,"935":750,"936":778,"937":722,"938":361,"939":778,"940":500,"941":430,"942":500,"943":250,"944":500,"945":500,"946":500,"947":555,"948":472,"949":430,"950":472,"951":500,"952":458,"953":250,"954":528,"955":500,"956":519,"957":472,"958":472,"959":528,"960":514,"961":472,"962":444,"963":569,"964":458,"965":500,"966":583,"967":555,"968":583,"969":667,"970":250,"971":500,"972":528,"973":500,"974":667,"975":764,"976":522,"977":569,"978":778,"979":778,"980":778,"981":578,"982":754,"983":528,"984":500,"985":500,"986":778,"987":500,"988":653,"989":500,"990":389,"991":389,"992":766,"993":722,"994":982,"995":789,"996":658,"997":535,"998":698,"999":555,"1000":510,"1001":484,"1002":750,"1003":528,"1004":500,"1005":500,"1006":716,"1007":458,"1008":528,"1009":472,"1010":444,"1011":266,"1012":778,"1013":430,"1014":430,"1015":625,"1016":472,"1017":722,"1018":916,"1019":583,"1020":472,"1021":722,"1022":722,"1023":722,"8192":1000,"8193":500,"8194":500,"8195":1000,"8196":333,"8197":250,"8198":167,"8199":500,"8200":278,"8201":200,"8202":28,"8203":0,"8208":333,"8209":333,"8210":500,"8211":500,"8212":1000,"8214":398,"8216":278,"8217":278,"8218":278,"8219":278,"8220":472,"8221":472,"8222":472,"8223":333,"8224":444,"8225":444,"8226":778,"8230":670,"8233":472,"8240":1166,"8241":1457,"8249":389,"8250":389,"8251":778,"8253":472,"8255":333,"8256":637,"8260":551,"8261":361,"8262":361,"8274":500,"8276":637},"it":{"32":358,"33":307,"34":401,"35":818,"36":500,"37":818,"38":767,"39":307,"40":409,"41":409,"42":511,"43":767,"44":307,"45":358,"46":307,"47":511,"48":511,"49":511,"50":511,"51":511,"52":511,"53":511,"54":511,"55":511,"56":511,"57":511,"58":307,"59":307,"60":778,"61":767,"62":778,"63":511,"64":767,"65":743,"66":704,"67":716,"68":755,"69":678,"70":653,"71":774,"72":743,"73":386,"74":525,"75":769,"76":627,"77":897,"78":743,"79":767,"80":678,"81":767,"82":729,"83":562,"84":716,"85":743,"86":743,"87":999,"88":743,"89":743,"90":613,"91":307,"92":500,"93":307,"94":556,"95":743,"96":511,"97":511,"98":460,"99":460,"100":511,"101":460,"102":307,"103":460,"104":511,"105":307,"106":307,"107":460,"108":256,"109":818,"110":562,"111":511,"112":511,"113":460,"114":422,"115":409,"116":332,"117":537,"118":460,"119":664,"120":464,"121":486,"122":409,"123":500,"124":278,"125":500,"126":556,"160":511,"161":307,"162":460,"163":769,"164":767,"165":743,"166":278,"167":490,"168":511,"169":683,"170":473,"171":562,"172":767,"173":358,"174":683,"175":511,"176":383,"177":767,"178":386,"179":359,"180":511,"181":511,"182":611,"183":278,"184":460,"185":375,"186":429,"187":562,"188":807,"189":807,"190":807,"191":511,"192":743,"193":743,"194":743,"195":743,"196":743,"197":743,"198":883,"199":716,"200":678,"201":678,"202":678,"203":678,"204":386,"205":386,"206":386,"207":386,"208":755,"209":743,"210":767,"211":767,"212":767,"213":767,"214":767,"215":767,"216":767,"217":743,"218":743,"219":743,"220":743,"221":743,"222":627,"223":537,"224":511,"225":511,"226":511,"227":511,"228":511,"229":511,"230":716,"231":460,"232":460,"233":460,"234":460,"235":460,"236":307,"237":307,"238":307,"239":307,"240":511,"241":562,"242":511,"243":511,"244":511,"245":511,"246":511,"247":767,"248":511,"249":537,"250":537,"251":537,"252":537,"253":486,"254":511,"255":486,"256":743,"257":511,"258":743,"259":511,"260":743,"261":511,"262":716,"263":460,"264":716,"265":460,"266":716,"267":460,"268":716,"269":460,"270":755,"271":511,"272":755,"273":511,"274":678,"275":460,"276":678,"277":460,"278":678,"279":460,"280":678,"281":460,"282":678,"283":460,"284":774,"285":460,"286":774,"287":460,"288":774,"289":460,"290":774,"291":460,"292":743,"293":511,"294":743,"295":511,"296":386,"297":307,"298":386,"299":307,"300":386,"301":307,"302":386,"303":307,"304":386,"305":307,"306":872,"307":583,"308":525,"309":307,"310":769,"311":460,"312":531,"313":627,"314":256,"315":627,"316":256,"317":627,"318":256,"319":627,"320":456,"321":627,"322":319,"323":743,"324":562,"325":743,"326":562,"327":743,"328":562,"329":819,"330":743,"331":498,"332":767,"333":511,"334":767,"335":511,"336":767,"337":511,"338":985,"339":716,"340":729,"341":422,"342":729,"343":422,"344":729,"345":422,"346":562,"347":409,"348":562,"349":409,"350":562,"351":409,"352":562,"353":409,"354":716,"355":332,"356":716,"357":332,"358":716,"359":332,"360":743,"361":537,"362":743,"363":537,"364":743,"365":537,"366":743,"367":537,"368":743,"369":537,"370":743,"371":537,"372":999,"373":664,"374":743,"375":486,"376":743,"377":613,"378":409,"379":613,"380":409,"381":613,"382":409,"383":307,"880":629,"881":562,"882":716,"883":572,"884":194,"885":194,"886":743,"887":743,"890":111,"891":591,"892":591,"893":591,"894":278,"895":525,"900":167,"901":278,"902":750,"903":278,"904":847,"905":917,"906":528,"908":861,"910":861,"911":805,"912":250,"913":743,"914":704,"915":627,"916":818,"917":678,"918":613,"919":743,"920":767,"921":386,"922":769,"923":692,"924":897,"925":743,"926":664,"927":767,"928":743,"929":678,"931":716,"932":716,"933":767,"934":716,"935":743,"936":767,"937":716,"938":361,"939":778,"940":500,"941":430,"942":555,"943":250,"944":500,"945":500,"946":500,"947":593,"948":472,"949":430,"950":472,"951":555,"952":458,"953":250,"954":528,"955":500,"956":650,"957":510,"958":472,"959":472,"960":500,"961":472,"962":444,"963":569,"964":458,"965":537,"966":583,"967":630,"968":583,"969":667,"970":250,"971":500,"972":472,"973":500,"974":667,"975":764,"976":474,"977":500,"978":778,"979":778,"980":778,"981":578,"982":754,"983":528,"984":500,"985":500,"986":778,"987":500,"988":653,"989":500,"990":389,"991":389,"992":766,"993":722,"994":982,"995":789,"996":658,"997":535,"998":698,"999":555,"1000":510,"1001":484,"1002":750,"1003":528,"1004":500,"1005":500,"1006":716,"1007":458,"1008":528,"1009":472,"1010":444,"1011":266,"1012":778,"1013":430,"1014":430,"1015":625,"1016":472,"1017":722,"1018":916,"1019":583,"1020":472,"1021":722,"1022":722,"1023":722,"8192":511,"8193":1022,"8194":511,"8195":1022,"8196":341,"8197":256,"8198":170,"8199":511,"8200":307,"8201":204,"8202":26,"8203":0,"8204":0,"8205":0,"8208":358,"8209":358,"8210":511,"8211":511,"8212":1022,"8214":398,"8216":307,"8217":307,"8218":307,"8219":307,"8220":490,"8221":490,"8222":490,"8223":361,"8224":444,"8225":444,"8226":767,"8230":684,"8233":485,"8240":1083,"8241":1379,"8249":358,"8250":358,"8251":767,"8253":511,"8255":358,"8256":691,"8260":603,"8261":383,"8262":383,"8274":511,"8276":691},"bf":{"32":383,"33":350,"34":481,"35":958,"36":575,"37":958,"38":894,"39":319,"40":447,"41":447,"42":575,"43":894,"44":319,"45":383,"46":319,"47":575,"48":575,"49":575,"50":575,"51":575,"52":575,"53":575,"54":575,"55":575,"56":575,"57":575,"58":319,"59":319,"60":894,"61":894,"62":894,"63":543,"64":894,"65":869,"66":818,"67":831,"68":882,"69":756,"70":724,"71":904,"72":900,"73":436,"74":594,"75":901,"76":692,"77":1092,"78":900,"79":864,"80":786,"81":864,"82":863,"83":639,"84":800,"85":885,"86":869,"87":1189,"88":869,"89":869,"90":703,"91":319,"92":575,"93":319,"94":556,"95":869,"96":575,"97":559,"98":639,"99":511,"100":639,"101":527,"102":351,"103":575,"104":639,"105":319,"106":351,"107":607,"108":319,"109":958,"110":639,"111":575,"112":639,"113":607,"114":474,"115":454,"116":447,"117":639,"118":607,"119":831,"120":607,"121":607,"122":511,"123":575,"124":319,"125":575,"126":556,"160":575,"161":350,"162":511,"163":869,"164":894,"165":869,"166":319,"167":695,"168":575,"169":686,"170":496,"171":639,"172":894,"173":383,"174":686,"175":575,"176":431,"177":894,"178":413,"179":413,"180":575,"181":639,"182":703,"183":278,"184":511,"185":417,"186":482,"187":639,"188":983,"189":983,"190":983,"191":543,"192":869,"193":869,"194":869,"195":869,"196":869,"197":869,"198":1042,"199":831,"200":756,"201":756,"202":756,"203":756,"204":436,"205":436,"206":436,"207":436,"208":882,"209":900,"210":864,"211":864,"212":864,"213":864,"214":864,"215":894,"216":894,"217":885,"218":885,"219":885,"220":885,"221":869,"222":724,"223":597,"224":559,"225":559,"226":559,"227":559,"228":559,"229":559,"230":831,"231":511,"232":527,"233":527,"234":527,"235":527,"236":319,"237":319,"238":319,"239":319,"240":575,"241":639,"242":575,"243":575,"244":575,"245":575,"246":575,"247":894,"248":575,"249":639,"250":639,"251":639,"252":639,"253":607,"254":639,"255":607,"256":869,"257":559,"258":869,"259":559,"260":869,"261":559,"262":831,"263":511,"264":831,"265":511,"266":831,"267":511,"268":831,"269":511,"270":882,"271":639,"272":882,"273":639,"274":756,"275":527,"276":756,"277":527,"278":756,"279":527,"280":756,"281":527,"282":756,"283":527,"284":904,"285":575,"286":904,"287":575,"288":904,"289":575,"290":904,"291":575,"292":900,"293":639,"294":900,"295":639,"296":436,"297":319,"298":436,"299":319,"300":436,"301":319,"302":436,"303":319,"304":436,"305":319,"306":987,"307":639,"308":594,"309":351,"310":901,"311":607,"312":607,"313":692,"314":319,"315":692,"316":319,"317":692,"318":319,"319":692,"320":436,"321":692,"322":387,"323":900,"324":639,"325":900,"326":639,"327":900,"328":639,"329":958,"330":900,"331":592,"332":864,"333":575,"334":864,"335":575,"336":864,"337":575,"338":1169,"339":894,"340":863,"341":474,"342":863,"343":474,"344":863,"345":474,"346":639,"347":454,"348":639,"349":454,"350":639,"351":454,"352":639,"353":454,"354":800,"355":447,"356":800,"357":447,"358":800,"359":447,"360":885,"361":639,"362":885,"363":639,"364":885,"365":639,"366":885,"367":639,"368":885,"369":639,"370":885,"371":639,"372":1189,"373":831,"374":869,"375":607,"376":869,"377":703,"378":511,"379":703,"380":511,"381":703,"382":511,"383":351,"880":654,"881":550,"882":800,"883":638,"884":261,"885":261,"886":900,"887":733,"890":161,"891":669,"892":669,"893":669,"894":361,"895":594,"900":228,"901":628,"902":933,"903":361,"904":1044,"905":1192,"906":703,"908":1044,"910":1189,"911":1008,"912":328,"913":869,"914":818,"915":692,"916":958,"917":756,"918":703,"919":900,"920":894,"921":436,"922":901,"923":806,"924":1092,"925":900,"926":767,"927":864,"928":900,"929":786,"931":831,"932":800,"933":894,"934":831,"935":869,"936":894,"937":831,"938":475,"939":961,"940":655,"941":544,"942":628,"943":328,"944":628,"945":655,"946":628,"947":722,"948":594,"949":572,"950":594,"951":628,"952":573,"953":355,"954":689,"955":628,"956":703,"957":622,"958":594,"959":661,"960":644,"961":622,"962":589,"963":711,"964":578,"965":655,"966":728,"967":694,"968":755,"969":828,"970":328,"971":628,"972":661,"973":628,"974":828,"975":901,"976":532,"977":739,"978":870,"979":1032,"980":778,"981":721,"982":754,"983":528,"984":628,"985":628,"986":961,"987":628,"988":783,"989":628,"990":389,"991":494,"992":948,"993":894,"994":982,"995":789,"996":738,"997":535,"998":731,"999":555,"1000":510,"1001":484,"1002":750,"1003":528,"1004":500,"1005":500,"1006":716,"1007":458,"1008":602,"1009":622,"1010":498,"1011":388,"1012":894,"1013":572,"1014":430,"1015":625,"1016":472,"1017":831,"1018":916,"1019":657,"1020":622,"1021":831,"1022":831,"1023":831,"8192":575,"8193":1150,"8194":575,"8195":1150,"8196":383,"8197":288,"8198":192,"8199":575,"8200":319,"8201":230,"8202":32,"8203":0,"8204":0,"8205":0,"8208":383,"8209":383,"8210":575,"8211":575,"8212":1150,"8214":499,"8216":319,"8217":319,"8218":319,"8219":319,"8220":571,"8221":571,"8222":571,"8223":411,"8224":511,"8225":511,"8226":894,"8230":838,"8233":543,"8240":1288,"8241":1667,"8249":445,"8250":445,"8251":894,"8253":543,"8255":732,"8256":732,"8260":648,"8261":415,"8262":415,"8274":575,"8276":732},"math":{"32":332,"33":278,"34":374,"35":833,"36":500,"37":833,"38":778,"39":278,"40":389,"41":389,"42":500,"43":778,"44":278,"45":333,"46":278,"47":500,"48":500,"49":500,"50":500,"51":500,"52":500,"53":500,"54":500,"55":500,"56":500,"57":500,"58":278,"59":278,"60":778,"61":778,"62":778,"63":472,"64":778,"65":750,"66":708,"67":722,"68":764,"69":681,"70":653,"71":785,"72":750,"73":361,"74":514,"75":778,"76":625,"77":917,"78":750,"79":778,"80":681,"81":778,"82":736,"83":556,"84":722,"85":750,"86":750,"87":1028,"88":750,"89":750,"90":611,"91":278,"92":500,"93":278,"94":556,"95":333,"96":500,"97":500,"98":556,"99":444,"100":556,"101":444,"102":306,"103":500,"104":556,"105":278,"106":306,"107":528,"108":278,"109":833,"110":556,"111":500,"112":556,"113":528,"114":392,"115":394,"116":389,"117":556,"118":528,"119":722,"120":528,"121":528,"122":444,"123":500,"124":278,"125":500,"126":556,"913":750,"914":708,"915":625,"916":833,"917":681,"918":611,"919":750,"920":778,"921":361,"922":778,"923":694,"924":917,"925":750,"926":667,"927":778,"928":750,"929":681,"931":722,"932":722,"933":778,"934":722,"935":750,"936":778,"937":722,"945":641,"946":558,"947":586,"948":474,"949":535,"950":530,"951":530,"952":488,"953":308,"954":530,"955":537,"956":530,"957":502,"958":530,"959":500,"960":586,"961":488,"962":474,"963":599,"964":530,"965":530,"966":641,"967":641,"968":641,"969":641,"977":530,"981":641,"982":836,"988":625,"989":500,"1008":624,"1009":488,"1012":778,"1013":414,"1014":414,"8448":1141,"8449":1109,"8450":722,"8451":1030,"8452":711,"8453":1141,"8454":1227,"8455":530,"8456":720,"8457":980,"8458":738,"8459":1065,"8460":720,"8461":777,"8462":576,"8463":576,"8464":620,"8465":554,"8466":770,"8467":417,"8468":978,"8469":722,"8470":916,"8471":683,"8472":636,"8473":611,"8474":777,"8475":818,"8476":828,"8477":722,"8478":736,"8479":736,"8480":883,"8481":1582,"8482":983,"8483":750,"8484":666,"8485":444,"8486":722,"8487":722,"8488":602,"8489":250,"8490":778,"8491":750,"8492":778,"8493":612,"8494":676,"8495":627,"8496":613,"8497":904,"8498":653,"8499":1149,"8500":697,"8501":611,"8502":604,"8503":528,"8504":574,"8505":319,"8506":985,"8507":1399,"8508":517,"8509":472,"8510":611,"8511":667,"8512":1056,"8513":667,"8514":542,"8515":542,"8516":667,"8517":694,"8518":500,"8519":472,"8520":279,"8521":379,"8522":632,"8523":778,"8524":806,"8525":1019,"8526":460,"8527":1258,"8592":1000,"8593":500,"8594":1000,"8595":500,"8596":1000,"8597":500,"8598":1000,"8599":1000,"8600":1000,"8601":1000,"8602":997,"8603":997,"8604":889,"8605":889,"8606":1017,"8607":572,"8608":1017,"8609":572,"8610":1192,"8611":1192,"8612":977,"8613":632,"8614":977,"8615":632,"8616":500,"8617":997,"8618":997,"8619":997,"8620":997,"8621":996,"8622":996,"8623":608,"8624":564,"8625":564,"8626":564,"8627":564,"8628":882,"8629":650,"8630":980,"8631":980,"8632":920,"8633":1018,"8634":771,"8635":771,"8636":1000,"8637":1012,"8638":441,"8639":441,"8640":1000,"8641":1012,"8642":441,"8643":441,"8644":1018,"8645":896,"8646":1018,"8647":997,"8648":992,"8649":997,"8650":992,"8651":1018,"8652":1018,"8653":991,"8654":1068,"8655":991,"8656":1000,"8657":611,"8658":1000,"8659":611,"8660":1000,"8661":611,"8662":1066,"8663":1066,"8664":1066,"8665":1066,"8666":1015,"8667":1015,"8668":997,"8669":997,"8670":997,"8671":997,"8672":1000,"8673":684,"8674":1000,"8675":684,"8676":1018,"8677":1018,"8678":1050,"8679":652,"8680":1050,"8681":652,"8682":652,"8683":652,"8684":652,"8685":652,"8686":652,"8687":652,"8688":1050,"8689":920,"8690":920,"8691":652,"8692":999,"8693":896,"8694":997,"8695":997,"8696":997,"8697":1000,"8698":997,"8699":997,"8700":1000,"8701":1000,"8702":1000,"8703":1000,"8704":666,"8705":556,"8706":586,"8707":556,"8708":556,"8709":778,"8710":833,"8711":833,"8712":667,"8713":667,"8714":547,"8715":667,"8716":667,"8717":547,"8718":666,"8719":944,"8720":944,"8721":1056,"8722":778,"8723":778,"8724":778,"8725":568,"8726":568,"8727":500,"8728":412,"8729":500,"8730":833,"8731":833,"8732":833,"8733":778,"8734":1000,"8735":778,"8736":778,"8737":778,"8738":778,"8739":278,"8740":388,"8741":500,"8742":556,"8743":667,"8744":667,"8745":667,"8746":667,"8747":665,"8748":1035,"8749":1405,"8750":665,"8751":1035,"8752":1405,"8753":695,"8754":682,"8755":682,"8756":516,"8757":516,"8758":278,"8759":516,"8760":778,"8761":906,"8762":778,"8763":773,"8764":773,"8765":773,"8766":901,"8767":778,"8768":280,"8769":773,"8770":778,"8771":778,"8772":778,"8773":778,"8774":778,"8775":778,"8776":773,"8777":773,"8778":778,"8779":773,"8780":778,"8781":778,"8782":778,"8783":778,"8784":778,"8785":778,"8786":778,"8787":778,"8788":906,"8789":906,"8790":778,"8791":778,"8792":778,"8793":778,"8794":778,"8795":778,"8796":778,"8797":778,"8798":778,"8799":778,"8800":778,"8801":778,"8802":778,"8803":778,"8804":778,"8805":778,"8806":778,"8807":778,"8808":778,"8809":778,"8810":1000,"8811":1000,"8812":434,"8813":778,"8814":778,"8815":778,"8816":778,"8817":778,"8818":776,"8819":776,"8820":776,"8821":776,"8822":778,"8823":778,"8824":778,"8825":778,"8826":778,"8827":778,"8828":738,"8829":738,"8830":773,"8831":773,"8832":778,"8833":778,"8834":778,"8835":778,"8836":778,"8837":778,"8838":778,"8839":778,"8840":778,"8841":778,"8842":778,"8843":778,"8844":667,"8845":667,"8846":667,"8847":778,"8848":778,"8849":778,"8850":778,"8851":667,"8852":667,"8853":782,"8854":782,"8855":782,"8856":782,"8857":782,"8858":782,"8859":782,"8860":782,"8861":782,"8862":778,"8863":778,"8864":778,"8865":778,"8866":611,"8867":611,"8868":778,"8869":778,"8870":445,"8871":445,"8872":612,"8873":673,"8874":841,"8875":653,"8876":565,"8877":732,"8878":793,"8879":773,"8880":778,"8881":778,"8882":738,"8883":738,"8884":738,"8885":738,"8886":1078,"8887":1078,"8888":948,"8889":818,"8890":778,"8891":642,"8892":642,"8893":642,"8894":900,"8895":778,"8896":833,"8897":833,"8898":833,"8899":833,"8900":500,"8901":278,"8902":500,"8903":802,"8904":623,"8905":623,"8906":623,"8907":623,"8908":623,"8909":778,"8910":733,"8911":733,"8912":698,"8913":698,"8914":658,"8915":658,"8916":839,"8917":778,"8918":778,"8919":778,"8920":1285,"8921":1285,"8922":778,"8923":778,"8924":778,"8925":778,"8926":738,"8927":738,"8928":738,"8929":738,"8930":778,"8931":778,"8932":778,"8933":778,"8934":776,"8935":776,"8936":773,"8937":773,"8938":738,"8939":738,"8940":738,"8941":738,"8942":218,"8943":776,"8944":613,"8945":613,"8946":839,"8947":667,"8948":547,"8949":667,"8950":667,"8951":547,"8952":667,"8953":667,"8954":839,"8955":667,"8956":547,"8957":667,"8958":547,"8959":556,"8960":778,"8961":902,"8962":652,"8963":778,"8964":778,"8965":778,"8966":778,"8967":280,"8968":444,"8969":444,"8970":444,"8971":444,"8972":818,"8973":818,"8974":818,"8975":818,"8976":667,"8977":572,"8978":778,"8979":667,"8980":778,"8981":587,"8982":986,"8983":778,"8984":738,"8985":667,"8986":778,"8987":658,"8988":392,"8989":392,"8990":392,"8991":392,"8992":1185,"8993":1185,"8994":1000,"8995":1000,"8996":778,"8997":759,"8998":984,"8999":726,"9000":1046,"9001":389,"9002":389,"9003":984,"9004":930,"9005":810,"9006":655,"9007":680,"9008":1137,"9009":1150,"9010":738,"9011":738,"9012":500,"9013":529,"9014":578,"9015":386,"9016":618,"9017":618,"9018":618,"9019":618,"9020":618,"9021":778,"9022":796,"9023":568,"9024":568,"9025":618,"9026":618,"9027":618,"9028":618,"9029":720,"9030":720,"9031":618,"9032":618,"9033":778,"9034":778,"9035":778,"9036":618,"9037":618,"9038":778,"9039":720,"9040":618,"9041":778,"9042":778,"9043":618,"9044":618,"9045":778,"9046":720,"9047":618,"9048":278,"9049":618,"9050":568,"9051":588,"9052":551,"9053":667,"9054":618,"9055":500,"9056":618,"9057":778,"9058":1000,"9059":827,"9060":618,"9061":500,"9062":667,"9063":778,"9064":556,"9065":778,"9066":278,"9067":1000,"9068":600,"9069":600,"9070":330,"9071":618,"9072":618,"9073":642,"9074":642,"9075":308,"9076":488,"9077":641,"9078":641,"9079":471,"9080":331,"9081":641,"9082":641,"9083":833,"9084":957,"9085":520,"9086":667,"9087":278,"9088":623,"9089":965,"9090":1076,"9091":1310,"9092":786,"9093":566,"9094":756,"9095":767,"9096":788,"9097":500,"9098":500,"9099":500,"9100":1028,"9101":613,"9102":589,"9103":756,"9104":756,"9105":756,"9106":756,"9107":778,"9108":930,"9109":618,"9110":738,"9111":748,"9112":748,"9113":777,"9114":777,"9115":875,"9116":875,"9117":875,"9118":875,"9119":875,"9120":875,"9121":667,"9122":667,"9123":667,"9124":667,"9125":667,"9126":667,"9127":902,"9128":902,"9129":902,"9130":902,"9131":902,"9132":902,"9133":902,"9134":1185,"9135":396,"9136":752,"9137":752,"9138":1576,"9139":1576,"9140":360,"9141":360,"9142":1066,"9143":1056,"9144":659,"9145":659,"9146":396,"9147":396,"9148":396,"9149":396,"9150":444,"9151":444,"9152":551,"9153":551,"9154":551,"9155":734,"9156":734,"9157":734,"9158":600,"9159":650,"9160":650,"9161":734,"9162":734,"9163":444,"9164":444,"9165":566,"9166":1050,"9167":668,"9168":333,"9169":500,"9170":500,"9171":500,"9172":848,"9173":848,"9174":848,"9175":636,"9176":636,"9177":636,"9178":734,"9179":967,"9180":504,"9181":504,"9182":492,"9183":492,"9184":546,"9185":546,"9186":1184,"9187":930,"9188":856,"9189":1070,"9190":1000,"9191":948,"9192":746,"9193":591,"9194":591,"9195":591,"9196":591,"9197":499,"9198":645,"9199":645,"9200":778,"9201":778,"9202":778,"9203":658,"9204":356,"9205":356,"9206":356,"9207":356,"9208":239,"9209":428,"9210":428,"9211":500,"9212":500,"9213":500,"9214":667,"9215":778,"9250":556,"9251":500,"9312":1124,"9313":1124,"9314":1124,"9315":1124,"9316":1124,"9317":1124,"9318":1124,"9319":1124,"9320":1124,"9321":1124,"9322":1124,"9323":1124,"9324":1124,"9325":1124,"9326":1124,"9327":1124,"9328":1124,"9329":1124,"9330":1124,"9331":1124,"9332":1159,"9333":1159,"9334":1159,"9335":1159,"9336":1159,"9337":1159,"9338":1159,"9339":1159,"9340":1159,"9341":1659,"9342":1659,"9343":1659,"9344":1659,"9345":1659,"9346":1659,"9347":1659,"9348":1659,"9349":1659,"9350":1659,"9351":1659,"9352":683,"9353":722,"9354":730,"9355":744,"9356":722,"9357":730,"9358":717,"9359":730,"9360":730,"9361":1183,"9362":1183,"9363":1183,"9364":1183,"9365":1183,"9366":1183,"9367":1183,"9368":1183,"9369":1183,"9370":1183,"9371":1222,"9372":1159,"9373":1215,"9374":1103,"9375":1215,"9376":1103,"9377":965,"9378":1159,"9379":1215,"9380":937,"9381":965,"9382":1187,"9383":937,"9384":1492,"9385":1215,"9386":1159,"9387":1215,"9388":1187,"9389":1051,"9390":1053,"9391":1048,"9392":1215,"9393":1187,"9394":1381,"9395":1187,"9396":1187,"9397":1103,"9398":1124,"9399":1124,"9400":1124,"9401":1124,"9402":1124,"9403":1124,"9404":1124,"9405":1124,"9406":1124,"9407":1124,"9408":1124,"9409":1124,"9410":1124,"9411":1124,"9412":1124,"9413":1124,"9414":1124,"9415":1124,"9416":1124,"9417":1124,"9418":1124,"9419":1124,"9420":1124,"9421":1124,"9422":1124,"9423":1124,"9424":1124,"9425":1124,"9426":1124,"9427":1124,"9428":1124,"9429":1124,"9430":1124,"9431":1124,"9432":1124,"9433":1124,"9434":1124,"9435":1124,"9436":1124,"9437":1124,"9438":1124,"9439":1124,"9440":1124,"9441":1124,"9442":1124,"9443":1124,"9444":1124,"9445":1124,"9446":1124,"9447":1124,"9448":1124,"9449":1124,"9450":1124,"9451":1124,"9452":1124,"9453":1124,"9454":1124,"9455":1124,"9456":1124,"9457":1124,"9458":1124,"9459":1124,"9460":1124,"9461":1378,"9462":1378,"9463":1378,"9464":1378,"9465":1378,"9466":1378,"9467":1378,"9468":1378,"9469":1378,"9470":1378,"9471":1124,"9472":666,"9473":666,"9474":666,"9475":666,"9476":666,"9477":666,"9478":666,"9479":666,"9480":666,"9481":666,"9482":666,"9483":666,"9484":666,"9485":666,"9486":666,"9487":666,"9488":666,"9489":666,"9490":666,"9491":666,"9492":666,"9493":666,"9494":666,"9495":666,"9496":666,"9497":666,"9498":666,"9499":666,"9500":502,"9501":502,"9502":502,"9503":502,"9504":502,"9505":502,"9506":502,"9507":502,"9508":502,"9509":502,"9510":502,"9511":502,"9512":502,"9513":502,"9514":502,"9515":502,"9516":666,"9517":666,"9518":666,"9519":666,"9520":666,"9521":666,"9522":666,"9523":666,"9524":666,"9525":666,"9526":666,"9527":666,"9528":666,"9529":666,"9530":666,"9531":666,"9532":666,"9533":666,"9534":666,"9535":666,"9536":666,"9537":666,"9538":666,"9539":666,"9540":666,"9541":666,"9542":666,"9543":666,"9544":666,"9545":666,"9546":666,"9547":666,"9548":666,"9549":666,"9550":666,"9551":666,"9552":666,"9553":666,"9554":666,"9555":666,"9556":666,"9557":666,"9558":666,"9559":666,"9560":666,"9561":666,"9562":666,"9563":666,"9564":666,"9565":666,"9566":502,"9567":502,"9568":502,"9569":502,"9570":502,"9571":502,"9572":666,"9573":666,"9574":666,"9575":666,"9576":666,"9577":666,"9578":502,"9579":666,"9580":666,"9581":666,"9582":666,"9583":666,"9584":666,"9585":500,"9586":500,"9587":500,"9588":666,"9589":666,"9590":666,"9591":666,"9592":666,"9593":666,"9594":666,"9595":666,"9596":666,"9597":666,"9598":666,"9599":666,"9600":778,"9601":664,"9602":664,"9603":664,"9604":664,"9605":664,"9606":664,"9607":664,"9608":664,"9609":664,"9610":664,"9611":664,"9612":778,"9613":664,"9614":664,"9615":664,"9616":778,"9617":664,"9618":664,"9619":664,"9620":664,"9621":664,"9622":664,"9623":664,"9624":664,"9625":664,"9626":664,"9627":664,"9628":664,"9629":664,"9630":664,"9631":664,"9632":778,"9633":778,"9634":778,"9635":778,"9636":778,"9637":778,"9638":778,"9639":778,"9640":778,"9641":778,"9642":328,"9643":328,"9644":778,"9645":778,"9646":466,"9647":466,"9648":1170,"9649":1170,"9650":968,"9651":968,"9652":626,"9653":626,"9654":858,"9655":858,"9656":626,"9657":626,"9658":866,"9659":866,"9660":968,"9661":968,"9662":626,"9663":626,"9664":858,"9665":858,"9666":626,"9667":626,"9668":866,"9669":866,"9670":1025,"9671":1025,"9672":778,"9673":1013,"9674":572,"9675":796,"9676":796,"9677":796,"9678":796,"9679":796,"9680":796,"9681":796,"9682":796,"9683":796,"9684":796,"9685":796,"9686":442,"9687":442,"9688":792,"9689":1024,"9690":1024,"9691":1024,"9692":600,"9693":600,"9694":600,"9695":600,"9696":1000,"9697":1000,"9698":778,"9699":778,"9700":778,"9701":778,"9702":500,"9703":778,"9704":778,"9705":778,"9706":778,"9707":778,"9708":613,"9709":973,"9710":973,"9711":1013,"9712":778,"9713":778,"9714":778,"9715":778,"9716":848,"9717":848,"9718":848,"9719":848,"9720":778,"9721":778,"9722":778,"9723":706,"9724":706,"9725":566,"9726":566,"9727":778,"9728":846,"9733":827,"9734":827,"9737":778,"9761":778,"9785":1013,"9786":1013,"9787":1013,"9788":846,"9789":667,"9790":667,"9792":500,"9794":655,"9824":778,"9825":778,"9826":778,"9827":778,"9828":778,"9829":778,"9830":778,"9831":778,"9833":442,"9834":611,"9835":898,"9837":388,"9838":388,"9839":388,"9854":1013,"9856":706,"9857":706,"9858":706,"9859":706,"9860":706,"9861":706,"9862":796,"9863":796,"9864":796,"9865":796,"9893":654,"9898":796,"9899":796,"9900":500,"9901":500,"9902":500,"9906":664,"10003":833,"10016":796,"10026":1013,"10038":800,"10045":575,"10074":525,"10098":278,"10099":278,"10139":1000,"10145":977,"10176":778,"10177":968,"10178":778,"10179":778,"10180":778,"10181":466,"10182":466,"10183":667,"10184":1168,"10185":1168,"10186":552,"10187":623,"10188":450,"10189":623,"10190":778,"10191":778,"10192":500,"10193":667,"10194":667,"10195":578,"10196":578,"10197":758,"10198":758,"10199":892,"10200":946,"10201":986,"10202":1026,"10203":1026,"10204":948,"10205":946,"10206":946,"10207":400,"10208":572,"10209":614,"10210":730,"10211":730,"10212":991,"10213":991,"10214":410,"10215":410,"10216":389,"10217":389,"10218":570,"10219":570,"10220":389,"10221":389,"10222":287,"10223":287,"10224":1015,"10225":1015,"10226":941,"10227":941,"10228":1121,"10229":1463,"10230":1463,"10231":1442,"10232":1457,"10233":1457,"10234":1534,"10235":1443,"10236":1443,"10237":1437,"10238":1437,"10239":1463,"10496":1017,"10497":1017,"10498":1000,"10499":1000,"10500":1000,"10501":1017,"10502":991,"10503":991,"10504":500,"10505":500,"10506":846,"10507":846,"10508":1000,"10509":1000,"10510":1000,"10511":1000,"10512":1375,"10513":1000,"10514":500,"10515":500,"10516":1214,"10517":1214,"10518":1230,"10519":1230,"10520":1230,"10521":1120,"10522":1120,"10523":1120,"10524":1120,"10525":1332,"10526":1332,"10527":1332,"10528":1332,"10529":837,"10530":837,"10531":716,"10532":716,"10533":716,"10534":716,"10535":1000,"10536":1000,"10537":1000,"10538":1000,"10539":830,"10540":830,"10541":1000,"10542":1000,"10543":830,"10544":830,"10545":1000,"10546":1000,"10547":1077,"10548":1118,"10549":1118,"10550":854,"10551":854,"10552":445,"10553":445,"10554":980,"10555":980,"10556":980,"10557":980,"10558":771,"10559":771,"10560":728,"10561":728,"10562":1018,"10563":1018,"10564":1018,"10565":1018,"10566":1018,"10567":1000,"10568":1000,"10569":1017,"10570":1012,"10571":1012,"10572":606,"10573":606,"10574":1000,"10575":373,"10576":1000,"10577":373,"10578":1088,"10579":1088,"10580":621,"10581":621,"10582":1088,"10583":1088,"10584":620,"10585":620,"10586":1000,"10587":1000,"10588":620,"10589":620,"10590":1000,"10591":1000,"10592":620,"10593":620,"10594":1018,"10595":800,"10596":1018,"10597":800,"10598":1018,"10599":1018,"10600":1018,"10601":1018,"10602":1018,"10603":1018,"10604":1018,"10605":1018,"10606":800,"10607":800,"10608":1046,"10609":1000,"10610":1085,"10611":1065,"10612":1065,"10613":1039,"10614":1000,"10615":1123,"10616":1000,"10617":1000,"10618":1073,"10619":1000,"10620":778,"10621":778,"10622":726,"10623":726,"10624":694,"10625":291,"10626":291,"10627":500,"10628":500,"10629":389,"10630":389,"10631":542,"10632":542,"10633":470,"10634":470,"10635":278,"10636":278,"10637":278,"10638":278,"10639":278,"10640":278,"10641":389,"10642":389,"10643":778,"10644":778,"10645":778,"10646":778,"10647":278,"10648":278,"10649":192,"10650":620,"10651":778,"10652":778,"10653":778,"10654":778,"10655":778,"10656":778,"10657":724,"10658":778,"10659":778,"10660":778,"10661":778,"10662":564,"10663":564,"10664":778,"10665":778,"10666":778,"10667":778,"10668":778,"10669":778,"10670":778,"10671":778,"10672":778,"10673":778,"10674":778,"10675":778,"10676":778,"10677":1047,"10678":712,"10679":712,"10680":712,"10681":712,"10682":712,"10683":778,"10684":712,"10685":712,"10686":712,"10687":712,"10688":712,"10689":712,"10690":954,"10691":984,"10692":712,"10693":712,"10694":712,"10695":712,"10696":712,"10697":712,"10698":968,"10699":968,"10700":968,"10701":1236,"10702":738,"10703":886,"10704":886,"10705":623,"10706":623,"10707":623,"10708":623,"10709":623,"10710":623,"10711":623,"10712":460,"10713":460,"10714":850,"10715":850,"10716":1000,"10717":1000,"10718":1000,"10719":1150,"10720":712,"10721":778,"10722":784,"10723":797,"10724":797,"10725":797,"10726":778,"10727":844,"10728":973,"10729":973,"10730":778,"10731":778,"10732":712,"10733":712,"10734":566,"10735":566,"10736":742,"10737":742,"10738":648,"10739":648,"10740":1140,"10741":556,"10742":556,"10743":556,"10744":500,"10745":500,"10746":964,"10747":1140,"10748":389,"10749":389,"10750":778,"10751":778,"10752":1111,"10753":1111,"10754":1111,"10755":833,"10756":833,"10757":833,"10758":833,"10759":1082,"10760":1082,"10761":1092,"10762":1056,"10763":707,"10764":1775,"10765":665,"10766":665,"10767":665,"10768":665,"10769":695,"10770":665,"10771":665,"10772":665,"10773":665,"10774":665,"10775":794,"10776":665,"10777":665,"10778":665,"10779":665,"10780":665,"10781":929,"10782":738,"10783":280,"10784":1118,"10785":441,"10786":778,"10787":778,"10788":778,"10789":778,"10790":778,"10791":827,"10792":778,"10793":778,"10794":778,"10795":778,"10796":778,"10797":669,"10798":669,"10799":778,"10800":778,"10801":778,"10802":778,"10803":778,"10804":606,"10805":606,"10806":778,"10807":778,"10808":778,"10809":968,"10810":968,"10811":968,"10812":667,"10813":667,"10814":240,"10815":750,"10816":667,"10817":667,"10818":667,"10819":667,"10820":667,"10821":667,"10822":607,"10823":607,"10824":607,"10825":607,"10826":1057,"10827":1057,"10828":846,"10829":846,"10830":667,"10831":667,"10832":846,"10833":667,"10834":667,"10835":667,"10836":667,"10837":805,"10838":805,"10839":778,"10840":778,"10841":667,"10842":667,"10843":667,"10844":771,"10845":771,"10846":667,"10847":667,"10848":667,"10849":642,"10850":667,"10851":667,"10852":838,"10853":838,"10854":778,"10855":778,"10856":778,"10857":778,"10858":773,"10859":773,"10860":778,"10861":778,"10862":778,"10863":773,"10864":778,"10865":778,"10866":778,"10867":778,"10868":842,"10869":992,"10870":1312,"10871":778,"10872":778,"10873":778,"10874":778,"10875":778,"10876":778,"10877":778,"10878":778,"10879":778,"10880":778,"10881":778,"10882":778,"10883":778,"10884":778,"10885":776,"10886":776,"10887":778,"10888":778,"10889":776,"10890":776,"10891":778,"10892":778,"10893":776,"10894":776,"10895":776,"10896":776,"10897":778,"10898":778,"10899":778,"10900":778,"10901":778,"10902":778,"10903":778,"10904":778,"10905":778,"10906":778,"10907":778,"10908":778,"10909":776,"10910":776,"10911":778,"10912":778,"10913":770,"10914":770,"10915":1011,"10916":876,"10917":1526,"10918":864,"10919":864,"10920":860,"10921":860,"10922":778,"10923":778,"10924":778,"10925":778,"10926":778,"10927":778,"10928":778,"10929":778,"10930":778,"10931":778,"10932":778,"10933":778,"10934":778,"10935":776,"10936":776,"10937":776,"10938":776,"10939":1248,"10940":1248,"10941":778,"10942":778,"10943":718,"10944":718,"10945":778,"10946":778,"10947":718,"10948":718,"10949":698,"10950":698,"10951":718,"10952":718,"10953":720,"10954":720,"10955":698,"10956":698,"10957":1384,"10958":1384,"10959":778,"10960":778,"10961":718,"10962":718,"10963":718,"10964":718,"10965":718,"10966":718,"10967":1348,"10968":1348,"10969":667,"10970":839,"10971":839,"10972":667,"10973":667,"10974":381,"10975":778,"10976":778,"10977":778,"10978":612,"10979":673,"10980":612,"10981":653,"10982":673,"10983":784,"10984":784,"10985":778,"10986":784,"10987":784,"10988":667,"10989":667,"10990":388,"10991":400,"10992":400,"10993":400,"10994":620,"10995":773,"10996":694,"10997":694,"10998":278,"10999":1013,"11000":1013,"11001":778,"11002":778,"11003":779,"11004":694,"11005":634,"11006":398,"11007":398,"11008":823,"11009":823,"11010":823,"11011":823,"11012":1062,"11013":977,"11014":612,"11015":612,"11016":612,"11017":612,"11018":612,"11019":612,"11020":1022,"11021":549,"11022":882,"11023":882,"11024":882,"11025":882,"11026":778,"11027":778,"11028":778,"11029":778,"11030":778,"11031":778,"11032":778,"11033":778,"11034":960,"11035":1024,"11036":1024,"11037":316,"11038":316,"11039":827,"11040":794,"11041":800,"11042":800,"11043":857,"11044":1013,"11045":1025,"11046":1025,"11047":572,"11048":572,"11049":1025,"11050":572,"11051":572,"11052":1186,"11053":1186,"11054":764,"11055":764,"11056":999,"11057":997,"11058":1121,"11059":1463,"11060":1017,"11061":1017,"11062":1017,"11063":1375,"11064":1000,"11065":1214,"11066":1214,"11067":1230,"11068":1230,"11069":1230,"11070":1000,"11071":1077,"11072":1000,"11073":1000,"11074":1039,"11075":1123,"11076":1073,"11077":1015,"11078":1015,"11079":1085,"11080":1039,"11081":1083,"11082":1039,"11083":1065,"11084":1065,"11085":535,"11086":571,"11087":571,"11088":827,"11089":486,"11090":486,"11091":827,"11092":794,"11093":1013,"11094":778,"11095":778,"11096":778,"11097":778,"11098":972,"11099":901,"11100":918,"11101":918,"11102":674,"11103":674,"11104":1000,"11105":390,"11106":1000,"11107":390,"11108":1170,"11109":410,"11110":1000,"11111":390,"11112":1000,"11113":390,"11114":1000,"11115":388,"11116":1000,"11117":388,"11118":851,"11119":851,"11120":1132,"11121":676,"11122":1132,"11123":676,"11126":814,"11127":814,"11128":814,"11129":814,"11130":998,"11131":704,"11132":998,"11133":704,"11134":1132,"11135":1008,"11136":1022,"11137":1022,"11138":1022,"11139":1022,"11140":1022,"11141":1022,"11142":1022,"11143":1022,"11144":635,"11145":635,"11146":635,"11147":635,"11148":1102,"11149":882,"11150":1102,"11151":882,"11152":1096,"11153":1096,"11154":1096,"11155":1096,"11156":976,"11157":760,"11159":766,"11160":649,"11161":683,"11162":649,"11163":683,"11164":649,"11165":683,"11166":649,"11167":683,"11168":918,"11169":918,"11170":918,"11171":918,"11172":646,"11173":646,"11174":646,"11175":646,"11176":977,"11177":977,"11178":977,"11179":977,"11180":667,"11181":667,"11182":667,"11183":667,"11184":1050,"11185":1050,"11186":1050,"11187":1050,"11188":926,"11189":926,"11190":926,"11191":926,"11192":652,"11193":978,"11194":712,"11195":712,"11196":712,"11197":566,"11198":778,"11199":778,"11200":410,"11201":510,"11202":414,"11203":510,"11204":510,"11205":626,"11206":626,"11207":626,"11208":626,"11209":778,"11210":656,"11211":656,"11212":510,"11213":510,"11214":510,"11215":510,"11216":778,"11217":778,"11218":744,"11219":778,"11220":674,"11221":712,"11222":712,"11223":485,"11224":614,"11225":558,"11226":346,"11227":626,"11228":570,"11229":712,"11230":600,"11231":712,"11232":801,"11233":553,"11234":841,"11235":717,"11236":801,"11237":485,"11238":893,"11239":717,"11240":826,"11241":826,"11242":827,"11243":827,"11244":1000,"11245":390,"11246":1000,"11247":390,"11248":585,"11249":485,"11250":713,"11251":778,"11252":496,"11253":504,"11254":778,"11255":325,"11256":456,"11257":1000,"11258":952,"11259":1212,"11260":486,"11261":485,"11262":778,"11263":377,"119808":869,"119809":818,"119810":831,"119811":882,"119812":756,"119813":724,"119814":904,"119815":900,"119816":436,"119817":594,"119818":901,"119819":692,"119820":1092,"119821":900,"119822":864,"119823":786,"119824":864,"119825":863,"119826":639,"119827":800,"119828":885,"119829":869,"119830":1189,"119831":869,"119832":869,"119833":703,"119834":559,"119835":639,"119836":511,"119837":639,"119838":527,"119839":351,"119840":575,"119841":639,"119842":319,"119843":351,"119844":607,"119845":319,"119846":958,"119847":639,"119848":575,"119849":639,"119850":607,"119851":474,"119852":454,"119853":447,"119854":639,"119855":607,"119856":831,"119857":607,"119858":607,"119859":511,"119860":750,"119861":759,"119862":715,"119863":828,"119864":738,"119865":643,"119866":786,"119867":831,"119868":440,"119869":555,"119870":849,"119871":681,"119872":970,"119873":803,"119874":763,"119875":642,"119876":791,"119877":759,"119878":613,"119879":584,"119880":683,"119881":583,"119882":944,"119883":828,"119884":581,"119885":683,"119886":529,"119887":429,"119888":433,"119889":520,"119890":466,"119891":490,"119892":477,"119894":345,"119895":412,"119896":521,"119897":298,"119898":878,"119899":600,"119900":485,"119901":503,"119902":446,"119903":451,"119904":469,"119905":361,"119906":572,"119907":485,"119908":716,"119909":572,"119910":490,"119911":465,"119912":869,"119913":866,"119914":817,"119915":938,"119916":810,"119917":689,"119918":887,"119919":982,"119920":511,"119921":631,"119922":971,"119923":756,"119924":1142,"119925":950,"119926":837,"119927":723,"119928":869,"119929":872,"119930":693,"119931":637,"119932":800,"119933":678,"119934":1093,"119935":947,"119936":675,"119937":773,"119938":633,"119939":521,"119940":513,"119941":610,"119942":554,"119943":568,"119944":545,"119945":668,"119946":405,"119947":471,"119948":604,"119949":348,"119950":1032,"119951":713,"119952":585,"119953":601,"119954":542,"119955":529,"119956":531,"119957":415,"119958":681,"119959":567,"119960":831,"119961":659,"119962":590,"119963":555,"119964":857,"119966":654,"119967":871,"119970":685,"119973":698,"119974":989,"119977":1007,"119978":699,"119979":763,"119980":716,"119982":625,"119983":776,"119984":744,"119985":710,"119986":1028,"119987":870,"119988":628,"119989":726,"119990":819,"119991":580,"119992":662,"119993":845,"119995":685,"119997":753,"119998":496,"119999":730,"120000":726,"120001":579,"120002":1038,"120003":761,"120005":773,"120006":780,"120007":580,"120008":515,"120009":551,"120010":753,"120011":618,"120012":888,"120013":752,"120014":658,"120015":691,"120016":969,"120017":916,"120018":745,"120019":1007,"120020":705,"120021":1005,"120022":790,"120023":1191,"120024":715,"120025":771,"120026":1099,"120027":861,"120028":1284,"120029":1095,"120030":822,"120031":880,"120032":839,"120033":923,"120034":722,"120035":910,"120036":853,"120037":784,"120038":1150,"120039":970,"120040":738,"120041":800,"120042":942,"120043":646,"120044":764,"120045":949,"120046":726,"120047":768,"120048":819,"120049":838,"120050":558,"120051":840,"120052":810,"120053":650,"120054":1137,"120055":851,"120056":848,"120057":885,"120058":913,"120059":677,"120060":562,"120061":618,"120062":842,"120063":732,"120064":1012,"120065":820,"120066":784,"120067":782,"120068":717,"120069":904,"120071":831,"120072":662,"120073":611,"120074":785,"120077":552,"120078":668,"120079":666,"120080":1049,"120081":832,"120082":828,"120083":823,"120084":828,"120086":828,"120087":669,"120088":645,"120089":831,"120090":1046,"120091":719,"120092":834,"120094":500,"120095":513,"120096":389,"120097":498,"120098":400,"120099":329,"120100":503,"120101":521,"120102":279,"120103":280,"120104":389,"120105":279,"120106":766,"120107":526,"120108":488,"120109":500,"120110":489,"120111":389,"120112":442,"120113":333,"120114":517,"120115":511,"120116":773,"120117":388,"120118":498,"120119":390,"120120":722,"120121":666,"120123":722,"120124":666,"120125":611,"120126":777,"120128":388,"120129":500,"120130":777,"120131":666,"120132":944,"120134":777,"120138":555,"120139":666,"120140":722,"120141":722,"120142":1000,"120143":722,"120144":722,"120146":500,"120147":628,"120148":472,"120149":500,"120150":472,"120151":389,"120152":500,"120153":572,"120154":279,"120155":389,"120156":544,"120157":279,"120158":722,"120159":572,"120160":472,"120161":628,"120162":500,"120163":544,"120164":389,"120165":417,"120166":528,"120167":472,"120168":667,"120169":472,"120170":472,"120171":472,"120172":847,"120173":1043,"120174":723,"120175":981,"120176":782,"120177":721,"120178":927,"120179":850,"120180":654,"120181":652,"120182":789,"120183":786,"120184":1239,"120185":982,"120186":976,"120187":977,"120188":976,"120189":977,"120190":978,"120191":789,"120192":850,"120193":981,"120194":1235,"120195":849,"120196":983,"120197":726,"120198":602,"120199":589,"120200":463,"120201":588,"120202":471,"120203":387,"120204":594,"120205":615,"120206":331,"120207":331,"120208":464,"120209":336,"120210":921,"120211":653,"120212":609,"120213":603,"120214":595,"120215":459,"120216":522,"120217":393,"120218":588,"120219":604,"120220":917,"120221":458,"120222":589,"120223":461,"120224":667,"120225":667,"120226":639,"120227":722,"120228":597,"120229":569,"120230":667,"120231":708,"120232":278,"120233":472,"120234":694,"120235":542,"120236":875,"120237":708,"120238":736,"120239":639,"120240":736,"120241":646,"120242":556,"120243":681,"120244":688,"120245":667,"120246":944,"120247":667,"120248":667,"120249":611,"120250":481,"120251":517,"120252":444,"120253":517,"120254":444,"120255":306,"120256":500,"120257":517,"120258":239,"120259":267,"120260":489,"120261":239,"120262":794,"120263":517,"120264":500,"120265":517,"120266":517,"120267":342,"120268":383,"120269":361,"120270":517,"120271":461,"120272":683,"120273":461,"120274":461,"120275":435,"120276":733,"120277":733,"120278":703,"120279":794,"120280":642,"120281":611,"120282":733,"120283":794,"120284":331,"120285":519,"120286":764,"120287":581,"120288":978,"120289":794,"120290":794,"120291":703,"120292":794,"120293":703,"120294":611,"120295":733,"120296":764,"120297":733,"120298":1039,"120299":733,"120300":733,"120301":672,"120302":525,"120303":561,"120304":489,"120305":561,"120306":511,"120307":336,"120308":561,"120309":561,"120310":256,"120311":286,"120312":531,"120313":256,"120314":867,"120315":561,"120316":550,"120317":561,"120318":561,"120319":372,"120320":422,"120321":404,"120322":561,"120323":500,"120324":744,"120325":500,"120326":500,"120327":476,"120328":667,"120329":667,"120330":639,"120331":722,"120332":597,"120333":569,"120334":667,"120335":708,"120336":278,"120337":472,"120338":694,"120339":542,"120340":875,"120341":708,"120342":736,"120343":639,"120344":736,"120345":646,"120346":556,"120347":681,"120348":688,"120349":667,"120350":944,"120351":667,"120352":667,"120353":611,"120354":481,"120355":517,"120356":444,"120357":517,"120358":444,"120359":306,"120360":500,"120361":517,"120362":239,"120363":267,"120364":489,"120365":239,"120366":794,"120367":517,"120368":500,"120369":517,"120370":517,"120371":342,"120372":383,"120373":361,"120374":517,"120375":461,"120376":683,"120377":461,"120378":461,"120379":435,"120380":733,"120381":733,"120382":703,"120383":794,"120384":642,"120385":611,"120386":733,"120387":794,"120388":331,"120389":519,"120390":764,"120391":581,"120392":978,"120393":794,"120394":794,"120395":703,"120396":794,"120397":703,"120398":611,"120399":733,"120400":764,"120401":733,"120402":1039,"120403":733,"120404":733,"120405":672,"120406":525,"120407":561,"120408":489,"120409":561,"120410":511,"120411":336,"120412":561,"120413":561,"120414":256,"120415":286,"120416":531,"120417":256,"120418":867,"120419":561,"120420":550,"120421":561,"120422":561,"120423":372,"120424":422,"120425":404,"120426":561,"120427":500,"120428":744,"120429":500,"120430":500,"120431":476,"120432":525,"120433":525,"120434":525,"120435":525,"120436":525,"120437":525,"120438":525,"120439":525,"120440":525,"120441":525,"120442":525,"120443":525,"120444":525,"120445":525,"120446":525,"120447":525,"120448":525,"120449":525,"120450":525,"120451":525,"120452":525,"120453":525,"120454":525,"120455":525,"120456":525,"120457":525,"120458":525,"120459":525,"120460":525,"120461":525,"120462":525,"120463":525,"120464":525,"120465":525,"120466":525,"120467":525,"120468":525,"120469":525,"120470":525,"120471":525,"120472":525,"120473":525,"120474":525,"120475":525,"120476":525,"120477":525,"120478":525,"120479":525,"120480":525,"120481":525,"120482":525,"120483":525,"120484":322,"120485":384,"120488":869,"120489":818,"120490":692,"120491":958,"120492":756,"120493":703,"120494":900,"120495":894,"120496":436,"120497":901,"120498":806,"120499":1092,"120500":900,"120501":767,"120502":864,"120503":900,"120504":786,"120505":894,"120506":831,"120507":800,"120508":894,"120509":831,"120510":869,"120511":894,"120512":831,"120513":958,"120514":743,"120515":647,"120516":679,"120517":551,"120518":597,"120519":615,"120520":615,"120521":567,"120522":359,"120523":615,"120524":618,"120525":615,"120526":583,"120527":615,"120528":575,"120529":679,"120530":567,"120531":551,"120532":695,"120533":615,"120534":615,"120535":743,"120536":743,"120537":743,"120538":743,"120539":679,"120540":506,"120541":615,"120542":724,"120543":743,"120544":567,"120545":966,"120546":750,"120547":759,"120548":615,"120549":833,"120550":738,"120551":683,"120552":831,"120553":763,"120554":440,"120555":849,"120556":694,"120557":970,"120558":803,"120559":742,"120560":763,"120561":831,"120562":642,"120563":763,"120564":780,"120565":584,"120566":583,"120567":667,"120568":828,"120569":612,"120570":772,"120571":833,"120572":640,"120573":566,"120574":518,"120575":444,"120576":466,"120577":438,"120578":497,"120579":469,"120580":354,"120581":576,"120582":583,"120583":603,"120584":494,"120585":438,"120586":485,"120587":570,"120588":517,"120589":363,"120590":571,"120591":437,"120592":540,"120593":654,"120594":626,"120595":651,"120596":622,"120597":531,"120598":406,"120599":591,"120600":624,"120601":596,"120602":517,"120603":828,"120604":869,"120605":866,"120606":657,"120607":958,"120608":810,"120609":773,"120610":982,"120611":867,"120612":511,"120613":971,"120614":806,"120615":1142,"120616":950,"120617":841,"120618":837,"120619":982,"120620":723,"120621":867,"120622":885,"120623":637,"120624":671,"120625":767,"120626":947,"120627":714,"120628":879,"120629":958,"120630":761,"120631":660,"120632":590,"120633":522,"120634":529,"120635":508,"120636":600,"120637":562,"120638":412,"120639":668,"120640":671,"120641":708,"120642":577,"120643":508,"120644":585,"120645":682,"120646":612,"120647":424,"120648":686,"120649":521,"120650":631,"120651":747,"120652":718,"120653":758,"120654":718,"120655":628,"120656":483,"120657":692,"120658":724,"120659":713,"120660":612,"120661":975,"120662":733,"120663":733,"120664":580,"120665":916,"120666":642,"120667":672,"120668":794,"120669":855,"120670":331,"120671":764,"120672":672,"120673":978,"120674":794,"120675":733,"120676":794,"120677":794,"120678":703,"120679":856,"120680":794,"120681":733,"120682":855,"120683":794,"120684":733,"120685":855,"120686":794,"120687":916,"120688":633,"120689":500,"120690":555,"120691":472,"120692":430,"120693":472,"120694":514,"120695":500,"120696":278,"120697":483,"120698":500,"120699":555,"120700":472,"120701":472,"120702":528,"120703":583,"120704":472,"120705":444,"120706":569,"120707":458,"120708":500,"120709":583,"120710":555,"120711":583,"120712":667,"120713":569,"120714":430,"120715":811,"120716":609,"120717":611,"120718":567,"120719":1035,"120720":733,"120721":733,"120722":580,"120723":916,"120724":642,"120725":672,"120726":794,"120727":855,"120728":331,"120729":764,"120730":672,"120731":978,"120732":794,"120733":733,"120734":794,"120735":794,"120736":703,"120737":856,"120738":794,"120739":733,"120740":855,"120741":794,"120742":733,"120743":855,"120744":794,"120745":916,"120746":633,"120747":500,"120748":555,"120749":472,"120750":430,"120751":472,"120752":514,"120753":500,"120754":278,"120755":483,"120756":500,"120757":555,"120758":472,"120759":472,"120760":528,"120761":583,"120762":472,"120763":444,"120764":569,"120765":458,"120766":500,"120767":583,"120768":555,"120769":583,"120770":667,"120771":569,"120772":430,"120773":811,"120774":609,"120775":611,"120776":567,"120777":1035,"120778":783,"120779":628,"120782":575,"120783":575,"120784":575,"120785":575,"120786":575,"120787":575,"120788":575,"120789":575,"120790":575,"120791":575,"120792":556,"120793":556,"120794":556,"120795":556,"120796":556,"120797":556,"120798":556,"120799":556,"120800":556,"120801":556,"120802":500,"120803":500,"120804":500,"120805":500,"120806":500,"120807":500,"120808":500,"120809":500,"120810":500,"120811":500,"120812":550,"120813":550,"120814":550,"120815":550,"120816":550,"120817":550,"120818":550,"120819":550,"120820":550,"120821":550,"120822":525,"120823":525,"120824":525,"120825":525,"120826":525,"120827":525,"120828":525,"120829":525,"120830":525,"120831":525}}'''

_PRINTLINES = r'''"""Printed lines of a result's statement and proof, as typeset in the Praxis paper (llncs, 10 pt New Computer
Modern, 6.5 in text width): a standard-library model of TeX's paragraph filling, from the fonts' own glyph
widths (widths.json). Markup costs nothing; what prints costs its width."""
import json, math, os, re

W = json.loads(WIDTHS_JSON)
W = {f: {int(k): v for k, v in t.items()} for f, t in W.items()}
PT = 10.0 / 1000                    # font units (per 1000 em) to points at 10 pt
TEXTWIDTH = 468.0                   # 6.5 in
PARINDENT = 15.0
SPACE, SHRINK = 3.33, 1.11
REL = {"=", "<", ">", "\\le", "\\leq", "\\ge", "\\geq", "\\ne", "\\neq", "\\in", "\\notin", "\\subseteq", "\\subset",
       "\\supseteq", "\\to", "\\mapsto", "\\equiv", "\\approx", "\\sim", "\\coloneqq", "\\defeq", ":=", "\\iff",
       "\\implies", "\\Rightarrow", "\\leftarrow", "\\gets", "\\mid", "\\perp", "\\cong", "\\simeq", "\\propto", "\\ll", "\\gg"}
BIN = {"+", "-", "\\cdot", "\\times", "\\oplus", "\\otimes", "\\cup", "\\cap", "\\pm", "\\setminus", "\\wedge", "\\vee", "\\circ", "\\star", "*"}
GREEK = "alpha beta gamma delta epsilon varepsilon zeta eta theta vartheta iota kappa lambda mu nu xi pi varpi rho varrho sigma varsigma tau upsilon phi varphi chi psi omega".split()
UGREEK = "Gamma Delta Theta Lambda Xi Pi Sigma Upsilon Phi Psi Omega".split()
ZERO = set("left right big Big bigg Bigg bigl bigr Bigl Bigr biggl biggr displaystyle textstyle scriptstyle limits nolimits label nonumber notag qedhere noindent par medskip smallskip bigskip allowbreak hfill centering phantom hphantom vphantom strut relax protect".split())
STYLE_TEXT = set("text textrm textup textnormal mathrm operatorname mathsf textsf mathtt texttt mbox hbox".split())
STYLE_IT = set("textit emph mathit".split())
STYLE_BF = set("textbf mathbf boldsymbol bm".split())
ACCENT = set("hat widehat bar overline tilde widetilde vec dot ddot underline check breve".split())
NAMED = {"log", "exp", "ln", "det", "dim", "deg", "gcd", "max", "min", "Pr", "ker", "rank", "lcm", "sup", "inf",
         "lim", "sin", "cos", "mod", "bmod", "arg", "tr", "Tr"}
WIDE = {"ldots": 1500, "cdots": 1500, "dots": 1500, "quad": 1000, "qquad": 2000, "sum": 1056, "prod": 944,
        "infty": 1000, "partial": 556, "forall": 556, "exists": 556, "emptyset": 500, "varnothing": 500,
        "langle": 389, "rangle": 389, "lfloor": 444, "rfloor": 444, "lceil": 444, "rceil": 444, "|": 500,
        "{": 500, "}": 500, "neg": 667, "top": 778, "bot": 778, "ell": 417, "nabla": 833, "prime": 275}


def gw(ch, font):
    t = W.get(font, W["rm"])
    return t.get(ord(ch), W["rm"].get(ord(ch), 500)) * PT


def textw(s, font="rm"):
    return sum(gw(c, font) for c in s)


def mathletter(c):
    if "a" <= c <= "z":
        return 0x210E if c == "h" else 0x1D44E + ord(c) - 97
    if "A" <= c <= "Z":
        return 0x1D434 + ord(c) - 65
    return ord(c)


def group(s, i):
    """The {...} group or single token at s[i]; returns (content, next index)."""
    while i < len(s) and s[i] == " ":
        i += 1
    if i < len(s) and s[i] == "{":
        d = 0
        for j in range(i, len(s)):
            d += (s[j] == "{") - (s[j] == "}")
            if d == 0:
                return s[i + 1:j], j + 1
        return s[i + 1:], len(s)
    if i < len(s) and s[i] == "\\":
        m = re.match(r"\\([A-Za-z]+|.)", s[i:], re.S)
        return (m.group(0), i + len(m.group(0))) if m else ("", len(s))
    return (s[i], i + 1) if i < len(s) else ("", i)


def mathw(s, scale=1.0):
    """Width of a math formula; returns a list of (width, breakable_after) chunks at the top level."""
    chunks, cur, i = [], 0.0, 0
    def put(w):
        nonlocal cur
        cur += w * scale
    def addabs(w):
        nonlocal cur
        cur += w
    def brk(w):
        nonlocal cur
        cur += w * scale
        chunks.append(cur)
        cur = 0.0
    while i < len(s):
        c = s[i]
        if c in " \n\t&":
            i += 1
            continue
        if c in "^_":
            arg, i = group(s, i + 1)
            addabs(sum(mathw(arg, scale * 0.7)))
            continue
        if c in "{}":
            i += 1
            continue
        if c == "\\":
            m = re.match(r"\\([A-Za-z]+|.)", s[i:], re.S)
            if not m:
                i += 1; continue
            name = m.group(1); i += len(m.group(0))
            if name in ZERO:
                if name == "label":
                    _, i = group(s, i)
                continue
            if name in (",", ";", ":", "!", " "):
                put({",": 1.67, ";": 2.78, ":": 2.22, "!": -1.67, " ": 3.33}[name]); continue
            if name in ("frac", "dfrac", "tfrac", "binom"):
                a, i = group(s, i); b, i = group(s, i)
                addabs(max(sum(mathw(a, scale * 0.7)), sum(mathw(b, scale * 0.7))) + 2.4 * scale); continue
            if name == "sqrt":
                if i < len(s) and s[i] == "[":
                    j = s.index("]", i); i = j + 1
                a, i = group(s, i); addabs(sum(mathw(a, scale)) + 8.3 * scale); continue
            if name in STYLE_TEXT or name in STYLE_BF or name in STYLE_IT:
                a, i = group(s, i)
                f = "bf" if name in STYLE_BF else ("it" if name in STYLE_IT else "rm")
                if name in ("mathbf", "boldsymbol", "bm") or name in STYLE_IT or name in ("mathrm", "mathsf", "mathtt", "operatorname"):
                    put(textw(re.sub(r"\\[A-Za-z]+|[{}]", "", a), f) * (1.0 if name != "mathsf" else 0.95) + (1.67 if name == "operatorname" else 0))
                else:
                    put(sum(w for w, _ in textline(a, f)))
                continue
            if name in ("mathbb", "mathcal", "mathfrak", "mathscr"):
                a, i = group(s, i); put(7.3 * max(1, len(re.sub(r"\\[A-Za-z]+|[{}\s]", "", a)))); continue
            if name in ACCENT:
                a, i = group(s, i); addabs(sum(mathw(a, scale))); continue
            if name in ("cref", "Cref", "ref", "eqref"):
                _, i = group(s, i); put(textw("Lemma B.12")); continue
            if name in GREEK:
                put(gw(chr(0x1D6FC + GREEK.index(name) % 25), "math") if False else 5.8); continue
            if name in UGREEK:
                put(7.2); continue
            if name in NAMED:
                put(textw(name) + 1.67); continue
            if name in WIDE:
                put(WIDE[name] * PT); continue
            if "\\" + name in REL:
                brk(7.78 + 5.56); continue
            if "\\" + name in BIN:
                brk(7.78 + 4.44); continue
            put(7.0)                                   # any other symbol or user macro: one glyph
            continue
        if c in "=<>":
            i += 1; brk(7.78 + 5.56); continue
        if c in "+-*":
            i += 1; brk(7.78 + 4.44); continue
        if c == ",":
            i += 1; brk(2.78 + 1.67); continue
        i += 1
        if c.isdigit() or c in "()[]|/.;:!'":
            put(gw(c, "rm"))
        else:
            put(W["math"].get(mathletter(c), 500) * PT)
    chunks.append(cur)
    return chunks


def textline(s, font):
    """Words of running text: list of (width, is_word_end) boxes; math is split at its break points."""
    boxes, i, word = [], 0, 0.0
    def end():
        nonlocal word
        if word:
            boxes.append((word, True)); word = 0.0
    while i < len(s):
        c = s[i]
        if c.isspace() or c == "~":
            if c == "~":
                word += SPACE; i += 1; continue
            end(); i += 1; continue
        if c == "$" or s.startswith("\\(", i):
            if s.startswith("\\(", i):
                j = s.find("\\)", i + 2); body = s[i + 2:j if j >= 0 else len(s)]; i = (j + 2) if j >= 0 else len(s)
            else:
                j = s.find("$", i + 1); body = s[i + 1:j if j >= 0 else len(s)]; i = (j + 1) if j >= 0 else len(s)
            ch = mathw(body)
            for k, w in enumerate(ch):
                word += w
                if k < len(ch) - 1:
                    boxes.append((word, True)); word = 0.0
            continue
        if c == "\\":
            m = re.match(r"\\([A-Za-z]+|.)", s[i:], re.S)
            if not m:
                i += 1; continue
            name = m.group(1); i += len(m.group(0))
            if name in ZERO:
                if name == "label":
                    _, i = group(s, i)
                continue
            if name in ("cref", "Cref", "ref", "eqref"):
                _, i = group(s, i); word += textw("Lemma B.12", font); continue
            if name in ("cite", "citep", "citet"):
                if i < len(s) and s[i] == "[":
                    j = s.index("]", i); word += textw(s[i + 1:j], font) + SPACE; i = j + 1
                _, i = group(s, i); word += textw("[AB12]", font); continue
            if name in STYLE_TEXT or name in STYLE_IT or name in STYLE_BF:
                a, i = group(s, i)
                f = "bf" if name in STYLE_BF else ("it" if name in STYLE_IT and font != "it" else font)
                for w, e in textline(a, f):
                    word += w
                    if e:
                        boxes.append((word, True)); word = 0.0
                continue
            if name in (",", " "):
                word += 1.67 if name == "," else SPACE; continue
            if name in ("ldots", "dots"):
                word += 15.0; continue
            if len(name) == 1:
                word += gw(name, font); continue
            word += 7.0
            continue
        if c in "{}":
            i += 1; continue
        word += gw(c, font); i += 1
    end()
    return boxes


def fill(boxes, first_indent=PARINDENT):
    """Greedy TeX-like filling (spaces may shrink); a too-long box hyphenates across lines."""
    if not boxes:
        return 0
    lines, cur, n = 1, first_indent, 0
    for w, _ in boxes:
        need = cur + (SPACE if n else 0) + w
        if need - SHRINK * n <= TEXTWIDTH or n == 0 and cur + w <= TEXTWIDTH:
            cur = need; n += 1
        else:
            rest = w
            # hyphenation: a long word starts on this line when at least a third fits
            if w > 40 and TEXTWIDTH - cur - SPACE > w / 3:
                rest = w - (TEXTWIDTH - cur - SPACE)
            lines += 1; cur, n = rest, 1
            while cur > TEXTWIDTH:
                lines += 1; cur -= TEXTWIDTH
    return lines


DISPLAY = re.compile(r"\\\[(.*?)\\\]|\$\$(.*?)\$\$|\\begin\{(equation\*?|align\*?|gather\*?|multline\*?|alignat\*?)\}(.*?)\\end\{\3\}", re.S)


def block_lines(text, font, head=None):
    """Lines of one statement or proof: paragraphs, list items, and display formulas."""
    text = text or ""
    total, pieces, last = 0.0, [], 0
    for m in DISPLAY.finditer(text):
        pieces.append(("t", text[last:m.start()]))
        body = m.group(1) or m.group(2) or m.group(4) or ""
        pieces.append(("d", body)); last = m.end()
    pieces.append(("t", text[last:]))
    first = True
    for kind, p in pieces:
        if kind == "d":
            rows = [r for r in re.split(r"\\\\", p) if r.strip()]
            for r in rows:
                w = sum(mathw(r))
                total += max(1, math.ceil(w / TEXTWIDTH)) + (1 if re.search(r"\\[dt]?frac", r) else 0)
            continue
        paras = re.split(r"\n\s*\n|\\item\b|\\begin\{(?:enumerate|itemize|description)\}(?:\[[^\]]*\])?|\\end\{(?:enumerate|itemize|description)\}", p)
        for k, para in enumerate(paras):
            if not para.strip():
                continue
            boxes = textline(para, font)
            if first and head:
                boxes = textline(head, "bf") + boxes
            total += fill(boxes, 0 if first else PARINDENT)
            first = False
    if first and head:
        total += 1
    return total


RESULTS = ("lemma", "proposition", "theorem", "corollary")


def node_lines(n, label=None):
    """Printed lines of a result: its header and statement (italic, as llncs sets lemmas) and its proof."""
    if n.get("kind") not in RESULTS:
        return 0.0
    head = (label or "Lemma B.12") + " (" + (n.get("name") or "") + ")."
    return block_lines(n.get("statement"), "it", head) + block_lines(n.get("proof"), "rm", "Proof.")
'''


if __name__ == "__main__":
    sys.exit(main(sys.argv))
