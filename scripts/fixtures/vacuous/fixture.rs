// Fixture for `check-vacuous-theorems.py --self-test`. Not compiled.
//
// Contains one theorem of each vacuous shape the linter must catch, plus two
// contentful theorems it must NOT flag. Guarding the guard: a linter that
// silently checks nothing looks exactly like one that passes.

verus! {

pub open spec fn spec_le(a: int, b: int) -> bool {
    a <= b
}

pub open spec fn spec_eq(a: int, b: int) -> bool {
    spec_le(a, b) && spec_le(b, a)
}

/// VACUOUS (1): the conclusion is verbatim one of the hypotheses.
pub proof fn vacuous_restatement(a: int, b: int)
    requires
        spec_le(a, b),
    ensures
        spec_le(a, b),
{
}

/// VACUOUS (2): `spec_eq` is *defined* as the conjunction of the hypotheses,
/// so unfolding it once yields exactly them. This is the shape that shipped.
pub proof fn vacuous_by_definition(a: int, b: int)
    requires
        spec_le(a, b),
        spec_le(b, a),
    ensures
        spec_eq(a, b),
{
}

/// CONTENTFUL: concludes structural equality, which is not among the
/// hypotheses and does not unfold to them. Must not be flagged.
pub proof fn contentful_antisymmetry(a: int, b: int)
    requires
        spec_le(a, b),
        spec_le(b, a),
    ensures
        a == b,
{
}

/// CONTENTFUL: a conclusion sharing vocabulary with the hypotheses but not
/// implied by restatement. Must not be flagged.
pub proof fn contentful_transitivity(a: int, b: int, c: int)
    requires
        spec_le(a, b),
        spec_le(b, c),
    ensures
        spec_le(a, c),
{
}

} // verus!
