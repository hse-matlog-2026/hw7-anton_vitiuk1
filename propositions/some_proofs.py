# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/some_proofs.py

"""Some proofs in Propositional Logic."""

from propositions.syntax import *
from propositions.proofs import *
from propositions.axiomatic_systems import *
from propositions.deduction import *

# Some inference rules that only use conjunction.

#: Conjunction introduction inference rule
A_RULE = InferenceRule([Formula.parse('x'), Formula.parse('y')],
                       Formula.parse('(x&y)'))
#: Conjunction elimination (right) inference rule
AE1_RULE = InferenceRule([Formula.parse('(x&y)')], Formula.parse('y'))
#: Conjunction elimination (left) inference rule
AE2_RULE = InferenceRule([Formula.parse('(x&y)')], Formula.parse('x'))


def prove_and_commutativity() -> Proof:
    """Proves ``'(q&p)'`` from ``'(p&q)'`` via `A_RULE`, `AE1_RULE`, and
    `AE2_RULE`.

    Returns:
        A valid proof of ``'(q&p)'`` from the single assumption ``'(p&q)'`` via
        the inference rules `A_RULE`, `AE1_RULE`, and `AE2_RULE`.
    """
    statement = InferenceRule([Formula.parse('(p&q)')], Formula.parse('(q&p)'))
    rules = {A_RULE, AE1_RULE, AE2_RULE}
    lines = [
        Proof.Line(Formula.parse('(p&q)')),
        Proof.Line(Formula.parse('q'), AE1_RULE, [0]),
        Proof.Line(Formula.parse('p'), AE2_RULE, [0]),
        Proof.Line(Formula.parse('(q&p)'), A_RULE, [1, 2])
    ]
    return Proof(statement, rules, lines)


def prove_I0() -> Proof:
    """Proves `~propositions.axiomatic_systems.I0` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I1`,
    and `~propositions.axiomatic_systems.D`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.I0` via the inference
        rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I1`, and
        `~propositions.axiomatic_systems.D`.
    """
    statement = I0
    rules = {MP, I1, D}

    lines = [
        Proof.Line(Formula.parse('((p->((p->p)->p))->((p->(p->p))->(p->p)))'), D, []),
        Proof.Line(Formula.parse('(p->((p->p)->p))'), I1, []),
        Proof.Line(Formula.parse('((p->(p->p))->(p->p))'), MP, [1, 0]),
        Proof.Line(Formula.parse('(p->(p->p))'), I1, []),
        Proof.Line(Formula.parse('(p->p)'), MP, [3, 2]),
    ]

    return Proof(statement, rules, lines)


#: Hypothetical syllogism
HS = InferenceRule([Formula.parse('(p->q)'), Formula.parse('(q->r)')],
                   Formula.parse('(p->r)'))


def prove_hypothetical_syllogism() -> Proof:
    """Proves `HS` via `~propositions.axiomatic_systems.MP`,
    `~propositions.axiomatic_systems.I0`, `~propositions.axiomatic_systems.I1`,
    and `~propositions.axiomatic_systems.D`.

    Returns:
        A valid proof of `HS` via the inference rules
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`, and
        `~propositions.axiomatic_systems.D`.
    """
    p = Formula.parse('p')
    q = Formula.parse('q')
    r = Formula.parse('r')

    p_implies_q = Formula.parse('(p->q)')
    q_implies_r = Formula.parse('(q->r)')

    statement = InferenceRule([p_implies_q, q_implies_r, p], r)
    rules = {MP}

    lines = [
        Proof.Line(p),
        Proof.Line(p_implies_q),
        Proof.Line(q, MP, (0, 1)),
        Proof.Line(q_implies_r),
        Proof.Line(r, MP, (2, 3))
    ]
    proof_r = Proof(statement, rules, lines)
    proof_p_implies_r = remove_assumption(proof_r)
    return proof_p_implies_r


def prove_I2() -> Proof:
    """Proves `~propositions.axiomatic_systems.I2` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    and `~propositions.axiomatic_systems.N`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.I2` via the inference
        rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    # Optional Task 6.7a

    not_p = Formula.parse('~p')
    not_q_implies_not_p = Formula.parse('(~q->~p)')
    p_implies_q = Formula.parse('(p->q)')

    i1_specialization = Formula.parse('(~p->(~q->~p))')
    n_specialization = Formula.parse('((~q->~p)->(p->q))')

    statement = InferenceRule([not_p], p_implies_q)
    rules = {MP, I1, N}
    lines = [
        Proof.Line(not_p),  # 0 : ~p
        Proof.Line(i1_specialization, I1, ()),  # 1  ~p -> (~q -> ~p)
        Proof.Line(not_q_implies_not_p, MP, (0, 1)),  # 2  (~q -> ~p)
        Proof.Line(n_specialization, N, ()),  # 3  ((~q->~p)->(p->q))
        Proof.Line(p_implies_q, MP, (2, 3))  # 4  (p -> q)
    ]
    proof_p_implies_q_from_not_p = Proof(statement, rules, lines)

    return remove_assumption(proof_p_implies_q_from_not_p)


#: Double-negation elimination
_NNE = InferenceRule([], Formula.parse('(~~p->p)'))


def _prove_NNE() -> Proof:
    """Proves `_NNE` via `~propositions.axiomatic_systems.MP`,
    `~propositions.axiomatic_systems.I0`, `~propositions.axiomatic_systems.I1`,
    `~propositions.axiomatic_systems.D`, and
    `~propositions.axiomatic_systems.N`.

    Returns:
        A valid proof of `_NNE` via the inference rules
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    # Optional Task 6.7b

    pp_contradiction = Formula.parse('~(p->p)')
    not_p = Formula.parse('~p')
    not_not_p = Formula.parse('~~p')

    proof_not_p = Proof(
        InferenceRule([not_not_p, not_p], not_p),
        set(),
        [Proof.Line(not_not_p), Proof.Line(not_p)]
    )

    proof_not_not_p = Proof(
        InferenceRule([not_not_p, not_p], not_not_p),
        set(),
        [Proof.Line(not_not_p), Proof.Line(not_p), Proof.Line(not_not_p)]
    )

    proof_contra = prove_from_opposites(proof_not_p, proof_not_not_p, pp_contradiction)
    proof_p_from_not_not_p = prove_by_way_of_contradiction(proof_contra)
    proof_p_from_not_not_p_no_i2 = inline_proof(proof_p_from_not_not_p, prove_I2())
    final_proof = remove_assumption(proof_p_from_not_not_p_no_i2)

    return final_proof


def prove_NN() -> Proof:
    """Proves `~propositions.axiomatic_systems.NN` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    and `~propositions.axiomatic_systems.N`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.NN` via the inference
        rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    # Optional Task 6.7c

    nne = _prove_NNE()
    specialized_nne_rule = InferenceRule([], Formula.parse('(~~~p->~p)'))
    proof_triple_not_p_implies_not_p = prove_specialization(nne, specialized_nne_rule)

    return prove_corollary(proof_triple_not_p_implies_not_p,
                           Formula.parse('(p->~~p)'), N)


#: Contraposition
_CP = InferenceRule([], Formula.parse('((p->q)->(~q->~p))'))


def _prove_CP() -> Proof:
    """Proves `_CP` via `~propositions.axiomatic_systems.MP`,
    `~propositions.axiomatic_systems.I0`, `~propositions.axiomatic_systems.I1`,
    `~propositions.axiomatic_systems.D`, and
    `~propositions.axiomatic_systems.N`.

    Returns:
        A valid proof of `_CP` via the inference rules
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    # Optional Task 6.7d
    pq = Formula.parse('(p->q)')
    nq = Formula.parse('~q')
    nnp = Formula.parse('~~p')
    p = Formula.parse('p')
    q = Formula.parse('q')
    bot = Formula.parse('~(p->p)')
    asm = [pq, nq, nnp]

    nne = _prove_NNE()
    Rn = nne.statement

    pr_p = Proof(InferenceRule(asm, p), {MP, Rn}, [
        Proof.Line(pq),
        Proof.Line(nq),
        Proof.Line(nnp),
        Proof.Line(Formula.parse('(~~p->p)'), Rn, ()),
        Proof.Line(p, MP, (2, 3))
    ])
    pr_p = inline_proof(pr_p, nne)

    ls = list(pr_p.lines)
    ls.append(Proof.Line(q, MP, (len(ls) - 1, 0)))
    pr_q = Proof(InferenceRule(asm, q), set(pr_p.rules) | {MP}, ls)

    pr_nq = Proof(InferenceRule(asm, nq), set(pr_q.rules), [
        Proof.Line(pq), Proof.Line(nq), Proof.Line(nnp), Proof.Line(nq)
    ])

    pr_bot = prove_from_opposites(pr_q, pr_nq, bot)
    pr_bot = inline_proof(pr_bot, prove_I2())

    pr_np = prove_by_way_of_contradiction(pr_bot)  # [pq, nq] ==> ~p
    pr = remove_assumption(pr_np)  # [pq] ==> (nq->~p)
    pr = remove_assumption(pr)  # [] ==> ((p->q)->(nq->~p))
    return pr


def prove_NI() -> Proof:
    """Proves `~propositions.axiomatic_systems.NI` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    and `~propositions.axiomatic_systems.N`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.NI` via the inference
        rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    # Optional Task 6.7e
    p = Formula.parse('p')
    nq = Formula.parse('~q')
    nnpq = Formula.parse('~~(p->q)')
    pq = Formula.parse('(p->q)')
    q = Formula.parse('q')
    bot = Formula.parse('~(p->p)')
    asm = [p, nq, nnpq]

    nne = _prove_NNE()
    spec = InferenceRule([], Formula.parse('(~~(p->q)->(p->q))'))
    spec_pf = prove_specialization(nne, spec)

    pr_pq = Proof(InferenceRule(asm, pq), {MP, spec}, [
        Proof.Line(p),
        Proof.Line(nq),
        Proof.Line(nnpq),
        Proof.Line(Formula.parse('(~~(p->q)->(p->q))'), spec, ()),
        Proof.Line(pq, MP, (2, 3))
    ])
    pr_pq = inline_proof(pr_pq, spec_pf)

    ls = list(pr_pq.lines)
    ls.append(Proof.Line(q, MP, (0, len(ls) - 1)))
    pr_q = Proof(InferenceRule(asm, q), set(pr_pq.rules) | {MP}, ls)

    pr_nq = Proof(InferenceRule(asm, nq), set(pr_q.rules), [
        Proof.Line(p), Proof.Line(nq), Proof.Line(nnpq), Proof.Line(nq)
    ])

    pr_bot = prove_from_opposites(pr_q, pr_nq, bot)
    pr_bot = inline_proof(pr_bot, prove_I2())

    pr_npq = prove_by_way_of_contradiction(pr_bot)
    pr = remove_assumption(pr_npq)
    pr = remove_assumption(pr)
    return pr


#: Consequentia mirabilis
_CM = InferenceRule([Formula.parse('(~p->p)')], Formula.parse('p'))


def _prove_CM() -> Proof:
    """Proves `_CM` via `~propositions.axiomatic_systems.MP`,
    `~propositions.axiomatic_systems.I0`, `~propositions.axiomatic_systems.I1`,
    `~propositions.axiomatic_systems.D`, and
    `~propositions.axiomatic_systems.N`.

    Returns:
        A valid proof of `_CM` via the inference rules
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    # Optional Task 6.7f

    a = Formula.parse('(~p->p)')
    np = Formula.parse('~p')
    p = Formula.parse('p')
    bot = Formula.parse('~(p->p)')

    asm = [a, np]

    pr_p = Proof(InferenceRule(asm, p), {MP}, [
        Proof.Line(a),  # 0
        Proof.Line(np),  # 1
        Proof.Line(p, MP, (1, 0))
    ])

    pr_np = Proof(InferenceRule(asm, np), {MP}, [
        Proof.Line(a),
        Proof.Line(np),
        Proof.Line(np)
    ])

    pr_bot = prove_from_opposites(pr_p, pr_np, bot)
    pr_bot = inline_proof(pr_bot, prove_I2())

    pr = prove_by_way_of_contradiction(pr_bot)  # [a] ==> p
    return pr


def prove_R() -> Proof:
    """Proves `~propositions.axiomatic_systems.R` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    and `~propositions.axiomatic_systems.N`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.R` via the inference
        rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    # Optional Task 6.7g

    qp = Formula.parse('(q->p)')
    nqp = Formula.parse('(~q->p)')
    npnq = Formula.parse('(~p->~q)')
    npp = Formula.parse('(~p->p)')
    p = Formula.parse('p')

    cp = _prove_CP()
    cp_rule = InferenceRule([], Formula.parse('((q->p)->(~p->~q))'))
    cp_pf = prove_specialization(cp, cp_rule)

    hs_pf = prove_hypothetical_syllogism()
    hs_rule = InferenceRule([npnq, nqp], npp)
    hs_pf = prove_specialization(hs_pf, hs_rule)

    cm_pf = _prove_CM()
    cm_rule = cm_pf.statement

    st = InferenceRule([qp, nqp], p)

    pr = Proof(st, {MP, cp_rule, hs_rule, cm_rule}, [
        Proof.Line(qp),
        Proof.Line(nqp),
        Proof.Line(cp_rule.conclusion, cp_rule, ()),
        Proof.Line(npnq, MP, (0, 2)),
        Proof.Line(npp, hs_rule, (3, 1)),
        Proof.Line(p, cm_rule, (4,))
    ])

    pr = inline_proof(pr, cp_pf)
    pr = inline_proof(pr, hs_pf)
    pr = inline_proof(pr, cm_pf)

    pr = remove_assumption(pr)
    pr = remove_assumption(pr)
    return pr


def prove_N() -> Proof:
    """Proves `~propositions.axiomatic_systems.N` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    and `~propositions.axiomatic_systems.N_ALTERNATIVE`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.N` via the inference
        rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N_ALTERNATIVE`.
    """
    # Optional Task 6.8

    a = Formula.parse('(~q->~p)')
    p = Formula.parse('p')
    q = Formula.parse('q')
    nq = Formula.parse('~q')

    nalt = Formula.parse('((~q->~p)->((~q->p)->q))')
    nalt2 = Formula.parse('((~q->p)->q)')
    i1 = Formula.parse('(p->(~q->p))')
    nqp = Formula.parse('(~q->p)')

    st = InferenceRule([a, p], q)
    pr = Proof(st, {MP, I1, N_ALTERNATIVE}, [
        Proof.Line(a),
        Proof.Line(nalt, N_ALTERNATIVE, ()),
        Proof.Line(nalt2, MP, (0, 1)),
        Proof.Line(p),
        Proof.Line(i1, I1, ()),
        Proof.Line(nqp, MP, (3, 4)),
        Proof.Line(q, MP, (5, 2))
    ])

    pr = remove_assumption(pr)
    pr = remove_assumption(pr)
    return pr


def prove_NA1() -> Proof:
    """Proves `~propositions.axiomatic_systems.NA1` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    `~propositions.axiomatic_systems.N`, and
    `~propositions.axiomatic_systems.AE1`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.NA1` via the inference
        rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.AE1`.
    """
    # Optional Task 6.9a


def prove_NA2() -> Proof:
    """Proves `~propositions.axiomatic_systems.NA2` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    `~propositions.axiomatic_systems.N`, and
    `~propositions.axiomatic_systems.AE2`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.NA2` via the inference
        rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.AE2`.
    """
    # Optional Task 6.9b


def prove_NO() -> Proof:
    """Proves `~propositions.axiomatic_systems.NO` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    `~propositions.axiomatic_systems.N`, and
    `~propositions.axiomatic_systems.OE`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.NO` via the inference
        rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.OE`.
    """
    # Optional Task 6.9c
