#!/usr/bin/env python3
"""Flag Verus `proof fn`s whose conclusion follows trivially from their own
hypotheses.

A theorem is *vacuous* when its `ensures` restates its `requires`. Verus is
perfectly happy to discharge one — the proof obligation really is satisfied —
so nothing in the toolchain complains, the verified count goes up, and the
result looks like evidence while establishing nothing.

This is not a hypothetical failure mode. Two shipped on this branch before
being caught by hand:

    proof fn theorem_order_antisymmetric(a: Q, b: Q)
        requires Q::spec_le(a, b), Q::spec_le(b, a),
        ensures  Q::spec_eq(a, b),          // <- spec_eq is *defined* as
                                            //    spec_le(a,b) && spec_le(b,a)

The conclusion is the hypothesis wearing a different name. Catching that needs
one level of definitional unfolding, which is what this script does:

  1. Direct restatement    — an `ensures` clause appearing verbatim among the
                             `requires` clauses.
  2. Definitional vacuity  — an `ensures` clause whose `spec fn` body, unfolded
                             once, is a conjunction of things all present in the
                             `requires`.

Both are decided syntactically. That makes the check sound in the direction
that matters (everything it flags really is vacuous) and incomplete in the
other (a semantically trivial theorem dressed up in unfamiliar syntax slips
through). A cheap check that catches the mistake actually made beats an
expensive one that catches every conceivable mistake.

Exit status is 1 if anything is flagged, so this runs in CI.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

DEFAULT_SRC = Path(__file__).resolve().parent.parent / "src"


def strip_comments(text: str) -> str:
    """Remove line comments. Verus specs do not use block comments here."""
    return "\n".join(re.sub(r"//.*$", "", line) for line in text.split("\n"))


def split_top_level(text: str, sep: str = ",") -> list[str]:
    """Split on `sep`, ignoring separators nested inside brackets."""
    parts, depth, cur = [], 0, []
    for ch in text:
        if ch in "([{<":
            depth += 1
        elif ch in ")]}>":
            depth -= 1
        if ch == sep and depth == 0:
            parts.append("".join(cur))
            cur = []
        else:
            cur.append(ch)
    parts.append("".join(cur))
    return [p.strip() for p in parts if p.strip()]


def normalise(clause: str) -> str:
    """Collapse whitespace so formatting differences do not hide a match."""
    return re.sub(r"\s+", "", clause)


def find_body_start(text: str, from_idx: int) -> int:
    """Index of the `{` opening a function body, skipping the signature.

    Only `()` and `[]` are counted. `<` and `>` are deliberately *not* treated
    as brackets: in Rust they are ambiguous, and the return arrow `->` on every
    `spec fn` would otherwise drive the depth negative and hide the body. That
    is not a hypothetical — it silently disabled the definitional-unfolding
    half of this check, which was caught only by testing the linter against a
    known-vacuous fixture.
    """
    depth = 0
    for i in range(from_idx, len(text)):
        ch = text[i]
        if ch in "([":
            depth += 1
        elif ch in ")]":
            depth -= 1
        elif ch == "{" and depth == 0:
            return i
    return -1


def parse_spec_fns(text: str) -> dict[str, list[str]]:
    """Map a boolean `spec fn` name to the conjuncts of its body.

    Only simple conjunctive bodies are recorded — `&&&`-joined or `&&`-joined
    calls. Anything with a `match` or `if` is skipped, because unfolding it
    would need real evaluation rather than a syntactic split.
    """
    out: dict[str, list[str]] = {}
    for m in re.finditer(r"\bspec\s+fn\s+(\w+)\s*\(", text):
        name = m.group(1)
        brace = find_body_start(text, m.end() - 1)
        if brace < 0:
            continue
        depth, end = 0, -1
        for i in range(brace, len(text)):
            if text[i] == "{":
                depth += 1
            elif text[i] == "}":
                depth -= 1
                if depth == 0:
                    end = i
                    break
        if end < 0:
            continue
        body = text[brace + 1 : end].strip()
        if "match" in body or body.startswith("if"):
            continue
        if "&&&" in body:
            conj = [c.strip() for c in body.split("&&&") if c.strip()]
        elif "&&" in body:
            conj = split_top_level(body, "&") if False else [
                c.strip() for c in body.split("&&") if c.strip()
            ]
        else:
            continue
        out[name] = conj
    return out


def parse_proof_fns(text: str):
    """Yield (name, line, [requires], [ensures]) for every `proof fn`."""
    for m in re.finditer(r"\bproof\s+fn\s+(\w+)\s*\(", text):
        name = m.group(1)
        brace = find_body_start(text, m.end() - 1)
        if brace < 0:
            continue
        sig = text[m.end() : brace]
        line = text[: m.start()].count("\n") + 1

        def section(kw: str) -> list[str]:
            km = re.search(rf"\b{kw}\b", sig)
            if not km:
                return []
            rest = sig[km.end() :]
            nxt = re.search(r"\b(requires|ensures|decreases|opens_invariants)\b", rest)
            if nxt:
                rest = rest[: nxt.start()]
            return split_top_level(rest)

        yield name, line, section("requires"), section("ensures")


def self_test() -> int:
    """Check the linter against a fixture with known answers.

    Without this, a linter that has quietly stopped parsing anything is
    indistinguishable from one that finds nothing wrong — which is exactly what
    happened here once: treating `>` as a closing bracket made every `spec fn`
    body invisible, disabling the definitional-unfolding check while the script
    still reported success.
    """
    fixture = Path(__file__).resolve().parent / "fixtures" / "vacuous"
    text = strip_comments((fixture / "fixture.rs").read_text())
    spec_fns = parse_spec_fns(text)
    flagged = set()
    for name, _line, req, ens in parse_proof_fns(text):
        if _is_vacuous(text, spec_fns, req, ens):
            flagged.add(name)

    must_flag = {"vacuous_restatement", "vacuous_by_definition"}
    must_not = {"contentful_antisymmetry", "contentful_transitivity"}
    missed = must_flag - flagged
    false_pos = must_not & flagged
    if missed or false_pos:
        if missed:
            print(f"SELF-TEST FAILED: did not flag {sorted(missed)}")
        if false_pos:
            print(f"SELF-TEST FAILED: wrongly flagged {sorted(false_pos)}")
        return 1
    print("Self-test passed: both vacuous shapes caught, neither contentful one flagged.")
    return 0


def _is_vacuous(text, spec_fns, req, ens) -> bool:
    req_norm = {normalise(r) for r in req}
    if not req_norm or not ens:
        return False
    for clause in ens:
        if normalise(clause) in req_norm:
            return True
        call = re.match(r"^([\w:]+)\s*\((.*)\)$", clause.strip())
        if not call:
            continue
        fn = call.group(1).split("::")[-1]
        conj = spec_fns.get(fn)
        if not conj or len(conj) < 2:
            continue
        args = split_top_level(call.group(2))
        params = _param_names(text, fn)
        if params is None or len(params) != len(args):
            continue
        subst = dict(zip(params, args))
        if all(normalise(_substitute(c, subst)) in req_norm for c in conj):
            return True
    return False


def main(argv: list[str]) -> int:
    if len(argv) > 1 and argv[1] == "--self-test":
        return self_test()
    src = Path(argv[1]) if len(argv) > 1 else DEFAULT_SRC
    findings = []
    spec_fns: dict[str, list[str]] = {}
    sources = sorted(src.glob("*.rs"))

    # Spec-fn bodies are needed crate-wide before any file can be checked.
    for path in sources:
        spec_fns.update(parse_spec_fns(strip_comments(path.read_text())))

    for path in sources:
        text = strip_comments(path.read_text())
        for name, line, req, ens in parse_proof_fns(text):
            if not ens:
                continue
            req_norm = {normalise(r) for r in req}
            if not req_norm:
                continue
            for clause in ens:
                cn = normalise(clause)

                # (1) The conclusion is verbatim one of the hypotheses.
                if cn in req_norm:
                    findings.append(
                        (path.name, line, name, clause, "restates a `requires` clause verbatim")
                    )
                    continue

                # (2) The conclusion unfolds to a conjunction of hypotheses.
                call = re.match(r"^([\w:]+)\s*\((.*)\)$", clause.strip())
                if not call:
                    continue
                fn = call.group(1).split("::")[-1]
                conj = spec_fns.get(fn)
                if not conj or len(conj) < 2:
                    continue
                args = split_top_level(call.group(2))
                params = _param_names(text, fn)
                if params is None or len(params) != len(args):
                    continue
                subst = dict(zip(params, args))
                unfolded = [_substitute(c, subst) for c in conj]
                if all(normalise(u) in req_norm for u in unfolded):
                    findings.append(
                        (
                            path.name,
                            line,
                            name,
                            clause,
                            f"`{fn}` unfolds to a conjunction of the `requires` clauses",
                        )
                    )

    if findings:
        print("VACUOUS THEOREMS — the conclusion follows from the hypotheses alone:\n")
        for fname, line, name, clause, why in findings:
            print(f"  {fname}:{line}  {name}")
            print(f"      ensures: {clause}")
            print(f"      reason:  {why}\n")
        print(
            f"{len(findings)} finding(s). Either strengthen the conclusion into "
            "something with content, or delete the theorem."
        )
        return 1

    print("No vacuous theorems found.")
    return 0


def _param_names(text: str, fn: str) -> list[str] | None:
    m = re.search(rf"\bspec\s+fn\s+{re.escape(fn)}\s*\(([^)]*)\)", text)
    if not m:
        return None
    out = []
    for p in split_top_level(m.group(1)):
        p = p.strip()
        if not p:
            continue
        out.append(p.split(":")[0].strip())
    return out


def _substitute(body: str, subst: dict[str, str]) -> str:
    def repl(m: re.Match) -> str:
        return subst.get(m.group(0), m.group(0))

    return re.sub(r"\b\w+\b", repl, body)


if __name__ == "__main__":
    sys.exit(main(sys.argv))
