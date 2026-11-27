# Proof golf: Praxis

Participants shorten one paper, counted in the lines it prints. "Praxis: Practical Witness Encryption for NP" (D. Tse, N. Vanjani, P. Vesely; Cryptology ePrint Archive 2026/2971) has been converted to a DAG of results with labeled edges. A submission is a substitution: it removes a set of nodes, adds another set, and says how every obligation of the removed set is met. The score is the number of lines the paper prints with the substitution applied. Lower is better.

## Problem and model

### The DAG

The paper is one protected file, `checkers/dag.json`, in the format `paper-dag/1`. Its canonical hash is

```
c11e19f1da0f93daaf309da999a465e2ea3d1f7f24761e9b5776ef7108e435d4
```

It has 32 results, 17 externals, 26 blobs and 302 edges. Its targets are `thm:correct` (Theorem 5.6), `cor:asymptotics` (Corollary 5.8), `thm:extraction` (Theorem 5.9), `cor:ext-error` (Corollary 5.10).

| kind | what it is | counts toward the score |
|---|---|---|
| `theorem`, `lemma`, `proposition`, `corollary` | a result the paper proves, with its `statement` and `proof` | statement + proof |
| `external` | a theorem the paper cites and uses without proof, with its `ref` (`citation`, `locator`, `url`, `quote`) | statement |
| `blob` | background a reader needs: a definition, notation, a model, a construction, an algorithm, an assumption | no |

Blobs are fixed: a substitution cannot add, remove or change them.

**Blobs are verified background, not results.** Blobs cost nothing, so nothing a proof needs may hide in one. Every blob was read assertion by assertion and the result is protected in `blob-audit.md`. A proof may take from a blob it is linked to its definitions, notation, models, constructions, algorithms, assumptions and parameter conditions, standard mathematics, and facts the blob attributes to an earlier paper or a named theorem (blobs may refer to earlier work as a reference to build on). It may not take a claim of this paper's own that a blob asserts without proof: `blob-audit.md` lists every such claim, quoted, as U (unverified). An added proof that needs a U claim proves it in its own steps, or takes it by a `uses` edge from a result or external whose statement gives it. Code enforces the structural half: a discharge never names a blob (S4), and an edge from a blob is a background edge (S5).

An edge runs from a prerequisite to what depends on it. Its `kind` is `uses` (result or external to result: the proof of B uses A) or `background` (blob to anything: B is stated or proved in terms of A). A `uses` edge carries a `demand`: the weakest statement about A that the proof of B needs, written out as a self-contained sentence, constants and probability bounds included. This is the contract on the edge. The graph is acyclic.

`dag-contract.md` lists every statement, every blob and every edge demand of this DAG. It is the part of the DAG a reviewer needs, and it is protected. The proofs are in `checkers/dag.json`.

### The substitution

A substitution removes a set of nodes and adds another, and says how every obligation of the removed set is met.

```json
{
  "format": "paper-dag-substitution/1",
  "base": "<the canonical hash above>",
  "title": "one line",
  "remove": ["lem:inverse", "lem:trim"],
  "add": [ { a node: kind result or external, with id, kind, label, name, statement, explain, and proof or ref } ],
  "edges": [ { an edge whose `to` is an added node; `from` is an added node, a kept result, a kept external or a blob } ],
  "discharge": [
    {"edge": ["lem:inverse", "lem:heavy"], "by": ["new:inverse"], "argument": "why the statement(s) of `by` imply the demand on this edge, constants included"}
  ],
  "replaces": {"new:extraction": "thm:extraction"}
}
```

Canonical hash: `sha256(json.dumps(dag, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8"))`.

Structural checks (code decides, no judgment):

- S1 `base` equals the hash of the DAG the verifier holds.
- S2 `remove` lists existing result or external nodes, no blobs, no duplicates. Added ids are new and unique.
- S3 A target may be removed only if `replaces` maps exactly one added result to it and `norm(statement)` is identical. The added node then becomes the target.
- S4 Every edge of the base with `from` in `remove` and `to` kept (an obligation) appears exactly once in `discharge`, with `by` a non-empty list of added or kept results or externals (never a blob) and a non-empty `argument`. No discharge for a non-obligation.
- S5 Every edge in `edges` ends at an added node and starts at an added node, a kept node or a blob; an edge from a blob is `background`; `uses` edges carry a non-empty `demand`. Edges into removed nodes disappear with them.
- S6 Added results have non-empty `statement` and `proof`; added externals have `ref.citation`, `ref.locator` and `ref.quote`, and no entry of `import_denylist` occurs (case-insensitive substring) in `citation`, `url` or `quote`. Full proofs only: the `proof` of an added result must be complete in its own words. Code refuses a proof that names a removed node (by id or printed label), that defers to the paper, to the original or a removed proof or to the reader ("as in the paper", "the original proof", "same argument as", "unchanged", "details are omitted", "left to the reader"), or that announces a sketch, an outline or an idea. Passing this floor proves nothing; the reviewer still judges the proof.
- S7 The resulting graph (kept nodes and edges, added nodes and edges, plus, for each discharge, an edge from each `by` node to the consumer carrying the original demand) is acyclic, and every target is present.
- S8 The score of the resulting graph is computed. Unreferenced added nodes still count.
- S9 Added text uses no layout, spacing or definition command (`\\newcommand`, `\\def`, `\\vspace`, `\\small`, `\\looseness`, `\\resizebox`, `\\displaystyle` and the rest of the list `LAYOUT` in `checkers/paperdag.py`) and no environment beyond those the paper uses and ordinary mathematics needs (`MATH_ENVS`). New notation is judged in review.
- S10 Only an improvement of more than 100 lines is accepted: a non-empty substitution must print at most 3424 lines, more than 100 below the record of 3525 lines when this version opened (`MAX_LINES` in `checkers/paperdag.py`).

Semantic obligations (a reviewer decides). The verifier lists them, one per item:

- O-discharge, one per discharged edge: given only the statements of the `by` nodes, does the demand follow as stated, with the same constants, bounds and hypotheses? The submitter's `argument` is shown.
- O-proof, one per added result: is the proof complete and correct, using only the node's own incoming demands, the blobs it is linked to (their definitions and the facts `blob-audit.md` does not list as U), and standard mathematics? A proof that uses a removed node, a kept node it has no edge from, or a U claim of a blob it does not prove, fails.
- O-cite, one per added external: does the cited source state this, at this locator, as quoted, and is the node's statement a faithful reading of the quote?

A substitution is VALID when all structural checks pass and every obligation is accepted.

The import denylist of this DAG is: `2611.28552`, `2026/2971`, `praxis-lean`, `Praxis: Practical Witness Encryption`. An added external that cites the paper itself or its own Lean development is refused by S6.

## Score

The score is `lines`, an integer: the printed lines of the paper with the substitution applied, set as the paper is set (llncs, 10 pt New Computer Modern, 6.5 in text width). Lower is better. Every line saved is a line off the paper.

- **What prints counts, markup does not.** A result costs the lines of its header, its statement and its proof: running text is filled into lines from the fonts' own glyph widths, inline math is measured symbol by symbol (sub- and superscripts at 70%), each display row is a line, a reference prints as its label, and each statement and proof adds the space the paper puts around it. Statements count. Cited theorems and blobs print nothing in the results and cost nothing. The rest of the paper is fixed, so the paper as published scores 3572 lines, its 66 pages.
- **Calibrated against XeLaTeX.** A result of the paper costs its measured typeset height (`PAPER_HEIGHTS` in `checkers/paperdag.py`). An added result costs `1.040 * node_lines() + 1.59` lines, the model `node_lines()` (the `_PRINTLINES` source in the same file) fitted to 41 submitted results typeset in place in the paper (typical error 1.1 lines per result). `python3 checkers/paperdag.py score checkers/dag.json` prints the count.

The score of a submission is the score of the DAG that results from applying its substitution to the base. It is computed by the protected checker `paperdag_gate` on the declared substitution; the reviewer does not choose the number and does not recount it.

The starting submission is the empty substitution: it removes nothing and adds nothing, and scores 3572 lines, the paper as published.

**Only shorter mathematics scores.** Lines fall when less is printed, so the review closes the ways of printing less without proving less. (1) One inference per sentence: every sentence of an added proof is a single inference that can be checked on its own from what precedes it (one application of a definition, a lemma, a cited theorem, an incoming demand, or one algebraic or probabilistic manipulation); packing several into one sentence is rejected. (2) No new notation: an added node uses only notation of the blobs linked to it and of the statements it uses, plus names for objects its own proof constructs; a new abbreviation, symbol or shorthand for something the paper writes out is rejected, and so is a symbol used without definition. (3) No typographic shortening: the gate refuses layout and definition commands (S9), and the reviewer rejects text run together, dropped words a reader needs, or a formula written where the paper's sentence was needed to follow the argument.

A submission that is not VALID receives no score. It is not scored as the baseline and it is not repaired. A valid substitution may score more than the current record; it is then valid and not a record.

## What does not count

- Anything short of a full proof. An idea, a plan, a sketch, an outline, a list of steps without the steps, or a proof that points back to the paper's proof, to the proof it replaces, to a removed node, to another node's proof or to the reader is not a proof. Every step must be written out in the `proof` field so that a reader can check it from that text, the demands on the node's incoming edges and the blobs linked to it. A shorter proof must be a different complete proof, never the same proof with steps left out.
- A substitution over any DAG other than the protected one, or with a `base` other than the hash above.
- An added external that cites the paper itself (arXiv 2611.28552, ePrint 2026/2971, by title) or its own Lean development (`praxis-lean`), under any spelling. S6 refuses the listed spellings; the reviewer refuses the rest.
- An added external whose quote is not what the source says, whose locator does not lead to it, or whose statement says more than the quote. The reviewer cannot open sources; a citation it cannot recognise as stating the quoted result is rejected.
- A discharge whose `by` statements give a weaker constant, a looser bound, an extra hypothesis, a narrower range of parameters or a different probability space than the demand on the edge.
- A proof that uses a removed node, a kept node it has no edge from, a step from inside another node's proof, the original proof of the node it replaces, or anything outside the DAG that is not standard mathematics.
- A `uses` edge in `edges` whose `demand` does not follow from the statement of its `from` node.
- A blob used as a result: a discharge that names a blob (S4 refuses it), or a proof that takes a claim `blob-audit.md` lists as U (unverified) without proving it.
- An argument placed where it is not counted. A proof must be complete in the `proof` field of its node. Text in `explain`, `name`, `label`, `title`, a discharge `argument`, an edge's `demand` or `where`, or `notes.md` is never part of a proof.
- Text made shorter without making the mathematics shorter (see "Only shorter mathematics scores").
- A changed target statement, a changed blob, or a result offered in a different model, parameter range or security notion than the node it replaces.
- A prose argument for validity in `notes.md`, a claim of a machine check, a link, or a transcript. These are context, never evidence.

## Submission and review

Submit only files under `submission/`:

- `substitution.json`: the substitution, in the format above.
- `submission.json`: the manifest. It names the claim and declares the substitution to the protected checker `paperdag_gate`. Do not write it by hand: `python3 tools/pack.py` checks `substitution.json` with the protected verifier and DAG, prints what the hosted checker will answer, and writes it.
- `notes.md`, optional: what was cut and why it is sound, for a human reader.

No other file and no experiment: `experiments` is `[]`. Limits: 3 files, 262,144 bytes per file. The manifest carries the substitution to the checker as base64 text of one zlib stream, and the hosted evaluator accepts a declared input of at most 16,384 bytes; `tools/pack.py` reports the packed size and refuses a substitution that does not fit.

Review has three stages.

1. **The gate (code).** The protected checker `paperdag_gate` rebuilds the declared bytes, refuses anything that is not one strict JSON object (a repeated key is refused), and runs the reference verifier `checkers/paperdag.py` on the protected DAG. It passes only when S1 to S10 all hold, and then reports `lines`, the list of semantic obligations, and the SHA-256 of the bytes it checked. Without a pass there is no score.
2. **The review (model).** An LLM reviewer first confirms that the SHA-256 the gate reports is the SHA-256 of the submitted `substitution.json`, so that the scored bytes are the bytes it reads. It then judges every obligation the gate lists, reading `substitution.json` against `dag-contract.md`. The standard is strict: any gap, any step it cannot confirm, any changed constant, bound or hypothesis rejects the whole submission.
3. **Promotion (automatic).** An accepted submission that scores below the record becomes the record, with no wait for a person. A model reading a proof is not a proof check: a record can be reviewed by a person afterwards against `review-prompt.md`, and `python3 tools/pack.py --check` confirms the submitted files agree.

The hosted evaluator runs in a sandbox with no network. The reviewer cannot open a cited source, and a model reading a proof is not a proof check: its judgment is an assessment of the submitted text, not a certificate. Records are promoted automatically on that assessment; a person can review a record afterwards.
