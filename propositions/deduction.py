# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2025
# File name: propositions/deduction.py

"""Useful proof manipulation maneuvers in Propositional Logic."""

from propositions.syntax import *
from propositions.proofs import *
from propositions.axiomatic_systems import *


def prove_corollary(antecedent_proof: Proof, consequent: Formula,
                    conditional: InferenceRule) -> Proof:
    """Converts the given proof of a formula `antecedent` to a proof of the
    given formula `consequent` by using the given assumptionless inference rule
    of which ``'(``\\ `antecedent`\\ ``->``\\ `consequent`\\ ``)'`` is a
    specialization.

    Parameters:
        antecedent_proof: valid proof of `antecedent`.
        consequent: formula to prove.
        conditional: assumptionless inference rule of which the assumptionless
            inference rule with conclusion
            ``'(``\\ `antecedent`\\ ``->``\\ `consequent`\\ ``)'`` is a
            specialization.

    Returns:
        A valid proof of `consequent` from the same assumptions as the given
        proof, via the same inference rules as the given proof and in addition
        `~propositions.axiomatic_systems.MP` and `conditional`.
    """
    assert antecedent_proof.is_valid()
    assert InferenceRule([],
                         Formula('->', antecedent_proof.statement.conclusion,
                                 consequent)).is_specialization_of(conditional)
    phi = antecedent_proof.statement.conclusion
    psi = consequent

    lines = list(antecedent_proof.lines)
    phi_implies_psi = Formula('->', phi, psi)
    lines.append(Proof.Line(phi_implies_psi, conditional, ()))
    idx_phi_implies_psi = len(lines) - 1
    idx_phi = len(antecedent_proof.lines) - 1
    lines.append(Proof.Line(psi, MP, (idx_phi, idx_phi_implies_psi)))
    statement = InferenceRule(antecedent_proof.statement.assumptions, psi)
    rules = set(antecedent_proof.rules) | {MP, conditional}
    proof = Proof(statement, rules, lines)
    return proof


def _append_proof(base_lines: List[Proof.Line], proof: Proof, shift_start: int) -> Tuple[List[Proof.Line], int]:
    """Appends lines of proof to base_lines, shifting assumption indices by shift_start.
    Returns the new lines list and the index of the last appended line."""
    new_lines = list(base_lines)
    for line in proof.lines:
        if line.is_assumption():
            new_lines.append(Proof.Line(line.formula))
        else:
            shifted = tuple(i + shift_start for i in line.assumptions)
            new_lines.append(Proof.Line(line.formula, line.rule, shifted))
    return new_lines, len(new_lines) - 1


def combine_proofs(antecedent1_proof: Proof, antecedent2_proof: Proof,
                   consequent: Formula, double_conditional: InferenceRule) -> \
        Proof:
    """Combines the given proofs of two formulas `antecedent1` and `antecedent2`
    into a proof of the given formula `consequent` by using the given
    assumptionless inference rule of which
    ``'(``\\ `antecedent1`\\ ``->(``\\ `antecedent2`\\ ``->``\\ `consequent`\\ ``))'``
    is a specialization.

    Parameters:
        antecedent1_proof: valid proof of `antecedent1`.
        antecedent2_proof: valid proof of `antecedent2` from the same
            assumptions and inference rules as `antecedent1_proof`.
        consequent: formula to prove.
        double_conditional: assumptionless inference rule of which the
            assumptionless inference rule with conclusion
            ``'(``\\ `antecedent1`\\ ``->(``\\ `antecedent2`\\ ``->``\\ `consequent`\\ ``))'``
            is a specialization.

    Returns:
        A valid proof of `consequent` from the same assumptions as the given
        proofs, via the same inference rules as the given proofs and in addition
        `~propositions.axiomatic_systems.MP` and `double_conditional`.
    """
    assert antecedent1_proof.is_valid()
    assert antecedent2_proof.is_valid()
    assert antecedent1_proof.statement.assumptions == \
           antecedent2_proof.statement.assumptions
    assert antecedent1_proof.rules == antecedent2_proof.rules
    assert InferenceRule(
        [], Formula('->', antecedent1_proof.statement.conclusion,
                    Formula('->', antecedent2_proof.statement.conclusion, consequent))
    ).is_specialization_of(double_conditional)
    phi1 = antecedent1_proof.statement.conclusion
    phi2 = antecedent2_proof.statement.conclusion
    psi = consequent
    assert InferenceRule([], Formula('->', phi1, Formula('->', phi2, psi))
                         ).is_specialization_of(double_conditional)

    lines = list(antecedent1_proof.lines)
    shift = len(lines)
    lines, last_idx2 = _append_proof(lines, antecedent2_proof, shift)

    idx_phi1 = shift - 1  # последняя строка первого доказательства
    idx_phi2 = last_idx2  # последняя строка второго доказательства

    phi2_implies_psi = Formula('->', phi2, psi)
    phi1_implies_phi2_implies_psi = Formula('->', phi1, phi2_implies_psi)
    lines.append(Proof.Line(phi1_implies_phi2_implies_psi, double_conditional, ()))
    idx_double = len(lines) - 1
    lines.append(Proof.Line(phi2_implies_psi, MP, (idx_phi1, idx_double)))
    idx_phi2_implies_psi = len(lines) - 1
    lines.append(Proof.Line(psi, MP, (idx_phi2, idx_phi2_implies_psi)))

    statement = InferenceRule(antecedent1_proof.statement.assumptions, psi)
    rules = set(antecedent1_proof.rules) | {MP, double_conditional}
    proof = Proof(statement, rules, lines)
    return proof


def remove_assumption(proof: Proof) -> Proof:
    """Converts the given proof of some `conclusion` formula, the last
    assumption of which is an assumption `assumption`, to a proof of
    ``'(``\\ `assumption`\\ ``->``\\ `conclusion`\\ ``)'`` from the same assumptions
    except `assumption`.

    Parameters:
        proof: valid proof to convert, with at least one assumption, via some
            set of inference rules all of which have no assumptions except
            perhaps `~propositions.axiomatic_systems.MP`.

    Returns:
        A valid proof of ``'(``\\ `assumption`\\ ``->``\\ `conclusion`\\ ``)'``
        from the same assumptions as the given proof except the last one, via
        the same inference rules as the given proof and in addition
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`, and
        `~propositions.axiomatic_systems.D`.
    """
    assert proof.is_valid()
    assert len(proof.statement.assumptions) > 0
    for rule in proof.rules:
        assert rule == MP or len(rule.assumptions) == 0

    assumptions = proof.statement.assumptions
    phi = assumptions[-1]
    new_assumptions = assumptions[:-1]
    conclusion = proof.statement.conclusion
    new_lines = []
    imp_line_index = {}
    new_rules = set(proof.rules) | {MP, I0, I1, D}

    for i, line in enumerate(proof.lines):
        xi = line.formula
        target = Formula('->', phi, xi)

        if line.is_assumption():
            if xi == phi:
                new_lines.append(Proof.Line(target, I0, ()))
                imp_line_index[i] = len(new_lines) - 1
            else:
                i1_spec = InferenceRule([], Formula('->', xi, target))
                new_lines.append(Proof.Line(xi))
                idx_xi = len(new_lines) - 1
                new_lines.append(Proof.Line(i1_spec.conclusion, I1, ()))
                idx_cond = len(new_lines) - 1
                new_lines.append(Proof.Line(target, MP, (idx_xi, idx_cond)))
                imp_line_index[i] = len(new_lines) - 1
        else:
            if line.rule == MP:
                j = line.assumptions[0]
                k = line.assumptions[1]
                xj = proof.lines[j].formula
                idx_phi_imp_xj = imp_line_index[j]
                idx_phi_imp_xj_imp_xi = imp_line_index[k]
                d_formula = Formula(
                    '->',
                    Formula('->', phi, Formula('->', xj, xi)),
                    Formula('->', Formula('->', phi, xj), Formula('->', phi, xi))
                )
                new_lines.append(Proof.Line(d_formula, D, ()))
                idx_d = len(new_lines) - 1
                new_lines.append(Proof.Line(d_formula.second, MP, (idx_phi_imp_xj_imp_xi, idx_d)))
                idx_mp1 = len(new_lines) - 1
                new_lines.append(Proof.Line(target, MP, (idx_phi_imp_xj, idx_mp1)))
                imp_line_index[i] = len(new_lines) - 1
            else:
                assert len(line.rule.assumptions) == 0
                new_lines.append(Proof.Line(xi, line.rule, ()))
                idx_xi = len(new_lines) - 1
                i1_spec_conc = Formula('->', xi, target)
                new_lines.append(Proof.Line(i1_spec_conc, I1, ()))
                idx_cond = len(new_lines) - 1
                new_lines.append(Proof.Line(target, MP, (idx_xi, idx_cond)))
                imp_line_index[i] = len(new_lines) - 1

    final_target = Formula('->', phi, conclusion)
    new_statement = InferenceRule(new_assumptions, final_target)
    result = Proof(new_statement, new_rules, new_lines)
    return result


def prove_from_opposites(proof_of_affirmation: Proof,
                         proof_of_negation: Proof, conclusion: Formula) -> \
        Proof:
    """Combines the given proofs of a formula `affirmation` and its negation
    ``'~``\\ `affirmation`\\ ``'`` into a proof of the given formula.

    Parameters:
        proof_of_affirmation: valid proof of `affirmation`.
        proof_of_negation: valid proof of ``'~``\\ `affirmation`\\ ``'`` from the
            same assumptions and inference rules of `proof_of_affirmation`.
        conclusion: formula to prove.

    Returns:
        A valid proof of `conclusion` from the same assumptions as the given
        proofs, via the same inference rules as the given proofs and in addition
        `~propositions.axiomatic_systems.MP` and
        `~propositions.axiomatic_systems.I2`.
    """
    assert proof_of_affirmation.is_valid()
    assert proof_of_negation.is_valid()
    assert proof_of_affirmation.statement.assumptions == \
           proof_of_negation.statement.assumptions
    assert Formula('~', proof_of_affirmation.statement.conclusion) == \
           proof_of_negation.statement.conclusion
    assert proof_of_affirmation.rules == proof_of_negation.rules

    phi = proof_of_affirmation.statement.conclusion
    psi = conclusion
    lines = list(proof_of_affirmation.lines)
    shift = len(lines)
    lines, last_idx_neg = _append_proof(lines, proof_of_negation, shift)
    idx_phi = shift - 1
    idx_not_phi = last_idx_neg
    phi_implies_psi = Formula('->', phi, psi)
    i2_instance = Formula('->', proof_of_negation.statement.conclusion, phi_implies_psi)
    lines.append(Proof.Line(i2_instance, I2, ()))
    idx_i2 = len(lines) - 1
    lines.append(Proof.Line(phi_implies_psi, MP, (idx_not_phi, idx_i2)))
    idx_phi_implies_psi = len(lines) - 1
    lines.append(Proof.Line(psi, MP, (idx_phi, idx_phi_implies_psi)))

    statement = InferenceRule(proof_of_affirmation.statement.assumptions, psi)
    rules = set(proof_of_affirmation.rules) | {MP, I2}
    result = Proof(statement, rules, lines)
    return result


def prove_by_way_of_contradiction(proof: Proof) -> Proof:
    """Converts the given proof of ``'~(p->p)'``, the last assumption of which
    is an assumption ``'~``\\ `formula`\\ ``'``, to a proof of `formula` from the
    same assumptions except ``'~``\\ `formula`\\ ``'``.

    Parameters:
        proof: valid proof of ``'~(p->p)'`` to convert, the last assumption of
            which is of the form ``'~``\\ `formula`\\ ``'``, via some set of
            inference rules all of which have no assumptions except perhaps
            `~propositions.axiomatic_systems.MP`.

    Returns:
        A valid proof of `formula` from the same assumptions as the given proof
        except the last one, via the same inference rules as the given proof and
        in addition `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    assert proof.is_valid()
    assert proof.statement.conclusion == Formula.parse('~(p->p)')
    assert len(proof.statement.assumptions) > 0
    assert proof.statement.assumptions[-1].root == '~'
    for rule in proof.rules:
        assert rule == MP or len(rule.assumptions) == 0
    not_formula = proof.statement.assumptions[-1]
    formula = not_formula.first
    deduced = remove_assumption(proof)
    imp1 = deduced.statement.conclusion
    p_to_p = Formula.parse('(p->p)')
    n_instance = Formula('->', imp1, Formula('->', p_to_p, formula))
    lines = list(deduced.lines)
    lines.append(Proof.Line(n_instance, N, ()))
    idx_n = len(lines) - 1
    idx_imp1 = len(deduced.lines) - 1
    lines.append(Proof.Line(Formula('->', p_to_p, formula), MP, (idx_imp1, idx_n)))
    idx_p_to_p_implies_formula = len(lines) - 1
    lines.append(Proof.Line(p_to_p, I0, ()))
    idx_p_to_p = len(lines) - 1
    lines.append(Proof.Line(formula, MP, (idx_p_to_p, idx_p_to_p_implies_formula)))
    new_statement = InferenceRule(proof.statement.assumptions[:-1], formula)
    new_rules = set(deduced.rules) | {N}
    result = Proof(new_statement, new_rules, lines)
    return result
