# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/proofs.py

"""Proofs by deduction in Propositional Logic."""

from __future__ import annotations
from typing import AbstractSet, FrozenSet, List, Mapping, Optional, Sequence, \
    Set, Tuple, Union

from logic_utils import frozen, memoized_parameterless_method

from propositions.syntax import *

#: A mapping from variable names to formulas.
SpecializationMap = Mapping[str, Formula]


@frozen
class InferenceRule:
    """An immutable inference rule in Propositional Logic, comprised of zero
    or more assumed propositional formulas, and a conclusion propositional
    formula.

    Attributes:
        assumptions (`~typing.Tuple`\\[`~propositions.syntax.Formula`, ...]):
            the assumptions of the rule.
        conclusion (`~propositions.syntax.Formula`): the conclusion of the rule.
    """
    assumptions: Tuple[Formula, ...]
    conclusion: Formula

    _specmap_cache = {}

    def __init__(self, assumptions: Sequence[Formula], conclusion: Formula):
        """Initializes an `InferenceRule` from its assumptions and conclusion.

        Parameters:
            assumptions: the assumptions for the rule.
            conclusion: the conclusion for the rule.
        """
        self.assumptions = tuple(assumptions)
        self.conclusion = conclusion

    @memoized_parameterless_method
    def __repr__(self) -> str:
        """Computes a string representation of the current inference rule.

        Returns:
            A string representation of the current inference rule.
        """
        return str([str(assumption) for assumption in self.assumptions]) + \
            ' ==> ' + "'" + str(self.conclusion) + "'"

    def __eq__(self, other: object) -> bool:
        """Compares the current inference rule with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is an `InferenceRule` object that
            equals the current inference rule, ``False`` otherwise.
        """
        return isinstance(other, InferenceRule) and \
            self.assumptions == other.assumptions and \
            self.conclusion == other.conclusion

    def __ne__(self, other: object) -> bool:
        """Compares the current inference rule with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not an `InferenceRule` object or
            does not does not equal the current inference rule, ``False``
            otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash((self.assumptions, self.conclusion))

    def variables(self) -> Set[str]:
        """Finds all variable names in the current inference rule.

        Returns:
            A set of all variable names used in the assumptions and in the
            conclusion of the current inference rule.
        """
        vars_ = set()
        for x in self.assumptions:
            vars_.update(x.variables())
        vars_.update(self.conclusion.variables())
        return vars_

    def specialize(self, specialization_map: SpecializationMap) -> \
            InferenceRule:
        """Specializes the current inference rule by simultaneously substituting
        each variable name `v` that is a key in `specialization_map` with the
        formula `specialization_map[v]`.

        Parameters:
            specialization_map: mapping defining the specialization to be
                performed.

        Returns:
            The resulting inference rule.
        """
        for variable in specialization_map:
            assert is_variable(variable)

        new = [
            x.substitute_variables(specialization_map)
            for x in self.assumptions
        ]
        new_conclusion = self.conclusion.substitute_variables(specialization_map)

        return InferenceRule(new, new_conclusion)

    @staticmethod
    def _merge_specialization_maps(
            specialization_map1: Union[SpecializationMap, None],
            specialization_map2: Union[SpecializationMap, None]) -> \
            Union[SpecializationMap, None]:
        """Merges the given specialization maps while checking their
        consistency.

        Parameters:
            specialization_map1: first mapping to merge, or ``None``.
            specialization_map2: second mapping to merge, or ``None``.

        Returns:
            A single mapping containing all (key, value) pairs that appear in
            either of the given maps, or ``None`` if one of the given maps is
            ``None`` or if some key appears in both given maps but with
            different values.
        """
        if specialization_map1 is not None:
            for variable in specialization_map1:
                assert is_variable(variable)
        if specialization_map2 is not None:
            for variable in specialization_map2:
                assert is_variable(variable)

        if specialization_map1 is None or specialization_map2 is None:
            return None

        merged = dict(specialization_map1)
        for v, f in specialization_map2.items():
            if v in merged and merged[v] != f:
                return None
            merged[v] = f
        return merged

    @staticmethod
    def _formula_specialization_map(general: Formula, specialization: Formula) \
            -> Union[SpecializationMap, None]:
        """Computes the minimal specialization map by which the given formula
        specializes to the given specialization.

        Parameters:
            general: non-specialized formula for which to compute the map.
            specialization: specialization for which to compute the map.

        Returns:
            The computed specialization map, or ``None`` if `specialization` is
            in fact not a specialization of `general`.
        """
        if is_variable(general.root):
            return {general.root: specialization}
        if is_constant(general.root):
            return {} if general == specialization else None
        if is_unary(general.root):
            if general.root != specialization.root:
                return None
            return InferenceRule._formula_specialization_map(general.first, specialization.first)
        assert is_binary(general.root)
        if general.root != specialization.root:
            return None

        left_map = InferenceRule._formula_specialization_map(general.first, specialization.first)
        right_map = InferenceRule._formula_specialization_map(general.second, specialization.second)
        return InferenceRule._merge_specialization_maps(left_map, right_map)

    def specialization_map(self, specialization: InferenceRule) -> \
            Union[SpecializationMap, None]:
        """Computes the minimal specialization map by which the current
        inference rule specializes to the given specialization.

        Parameters:
            specialization: specialization for which to compute the map.

        Returns:
            The computed specialization map, or ``None`` if `specialization` is
            in fact not a specialization of the current rule.
        """
        key = (self, specialization)
        if key in InferenceRule._specmap_cache:
            return InferenceRule._specmap_cache[key]

        if len(self.assumptions) != len(specialization.assumptions):
            InferenceRule._specmap_cache[key] = None
            return None

        current_map: Union[SpecializationMap, None] = {}
        for a_general, a_spec in zip(self.assumptions, specialization.assumptions):
            m = InferenceRule._formula_specialization_map(a_general, a_spec)
            current_map = InferenceRule._merge_specialization_maps(current_map, m)
            if current_map is None:
                InferenceRule._specmap_cache[key] = None
                return None

        m_conc = InferenceRule._formula_specialization_map(self.conclusion, specialization.conclusion)
        current_map = InferenceRule._merge_specialization_maps(current_map, m_conc)

        InferenceRule._specmap_cache[key] = current_map
        return current_map

    def is_specialization_of(self, general: InferenceRule) -> bool:
        """Checks if the current inference rule is a specialization of the given
        inference rule.

        Parameters:
            general: non-specialized inference rule to check.

        Returns:
            ``True`` if the current inference rule is a specialization of
            `general`, ``False`` otherwise.
        """
        return general.specialization_map(self) is not None


@frozen
class Proof:
    """An immutable deductive proof in Propositional Logic, comprised of a
    statement in the form of an inference rule, a set of inference rules that
    may be used in the proof, and a list of lines that prove the statement via
    these inference rules.

    Attributes:
        statement (`InferenceRule`): the statement proven by the proof.
        rules (`~typing.AbstractSet`\\[`InferenceRule`]): the allowed rules of
            the proof.
        lines (`~typing.Tuple`\\[`Line`]): the lines of the proof.
    """
    statement: InferenceRule
    rules: FrozenSet[InferenceRule]
    lines: Tuple[Proof.Line, ...]

    def __init__(self, statement: InferenceRule,
                 rules: AbstractSet[InferenceRule],
                 lines: Sequence[Proof.Line]):
        """Initializes a `Proof` from its statement, allowed inference rules,
        and lines.

        Parameters:
            statement: the statement to be proven by the proof.
            rules: the allowed rules for the proof.
            lines: the lines for the proof.
        """
        self.statement = statement
        self.rules = frozenset(rules)
        self.lines = tuple(lines)
        self._spec_cache = {}
        self._derived_rule_cache = {}

    @frozen
    class Line:
        """An immutable line in a deductive proof, comprised of a formula that
        is justified either as an assumption of the proof, or as the conclusion
        of a specialization of an allowed inference rule of the proof, the
        assumptions of which are justified by previous lines in the proof.

        Attributes:
            formula (`~propositions.syntax.Formula`): the formula justified by
                the line.
            rule (`~typing.Optional`\\[`InferenceRule`]): the inference rule,
                out of those allowed in the proof, that has a specialization
                that concludes the formula; or ``None`` if the formula is
                justified as an assumption of the proof.
            assumptions (`~typing.Optional`\\[`~typing.Tuple`\\[`int`]): tuple
                of zero or more numbers of previous lines in the proof whose
                formulas are the respective assumptions of the specialization of
                the rule that concludes the formula, if the formula is not
                justified as an assumption of the proof.
        """
        formula: Formula
        rule: Optional[InferenceRule]
        assumptions: Optional[Tuple[int, ...]]

        def __init__(self, formula: Formula,
                     rule: Optional[InferenceRule] = None,
                     assumptions: Optional[Sequence[int]] = None):
            """Initializes a `~Proof.Line` from its formula, and optionally its
            rule and numbers of justifying previous lines.

            Parameters:
                formula: the formula to be justified by the line.
                rule: the inference rule, out of those allowed in the proof,
                    that has a specialization that concludes the formula; or
                    ``None`` if the formula is to be justified as an assumption
                    of the proof.
                assumptions: numbers of previous lines in the proof whose
                    formulas are the respective assumptions of the
                    specialization of the rule that concludes the formula, or
                    ``None`` if the formula is to be justified as an assumption
                    of the proof.
            """
            assert (rule is None and assumptions is None) or \
                   (rule is not None and assumptions is not None)
            self.formula = formula
            self.rule = rule
            if assumptions is not None:
                self.assumptions = tuple(assumptions)

        def __repr__(self) -> str:
            """Computes a string representation of the current line.

            Returns:
                A string representation of the current line.
            """
            if self.rule is None:
                return str(self.formula)
            else:
                r = str(self.formula) + '    (Inference Rule ' + str(self.rule)
                if len(self.assumptions) == 1:
                    r += ' on line ' + str(self.assumptions[0])
                elif len(self.assumptions) > 1:
                    r += ' on lines ' + ','.join(map(str, self.assumptions))
                r += ')'
                return r

        def is_assumption(self) -> bool:
            """Checks if the current proof line is justified as an assumption of
            the proof.

            Returns:
                ``True`` if the current proof line is justified as an assumption
                of the proof, ``False`` otherwise.
            """
            return self.rule is None

    def __repr__(self) -> str:
        """Computes a string representation of the current proof.

        Returns:
            A string representation of the current proof.
        """
        r = 'Proof of ' + str(self.statement) + ' via inference rules:\n'
        for rule in self.rules:
            r += '  ' + str(rule) + '\n'
        r += 'Lines:\n'
        for i in range(len(self.lines)):
            r += ('%3d) ' % i) + str(self.lines[i]) + '\n'
        r += "QED\n"
        return r

    def rule_for_line(self, line_number: int) -> Union[InferenceRule, None]:
        """Computes the inference rule whose conclusion is the formula justified
        by the specified line, and whose assumptions are the formulas justified
        by the lines specified as the assumptions of that line.

        Parameters:
            line_number: number of the line according to which to compute the
                inference rule.

        Returns:
            The computed inference rule, with assumptions ordered in the order
            of their numbers in the specified line, or ``None`` if the specified
            line is justified as an assumption.
        """
        assert line_number < len(self.lines)
        line = self.lines[line_number]
        if line.is_assumption():
            return None
        assumptions_formulas = [self.lines[i].formula for i in line.assumptions]
        return InferenceRule(assumptions_formulas, line.formula)

    def is_line_valid(self, line_number: int) -> bool:
        """Checks if the specified line validly follows from its justifications.

        Parameters:
            line_number: number of the line to check.

        Returns:
            If the specified line is justified as an assumption, then ``True``
            if the formula justified by this line is an assumption of the
            current proof, ``False`` otherwise. Otherwise (i.e., if the
            specified line is justified as a conclusion of an inference rule),
            ``True`` if the rule specified for that line is one of the allowed
            inference rules in the current proof, and it has a specialization
            that satisfies all of the following:

            1. The conclusion of that specialization is the formula justified by
               that line.
            2. The assumptions of this specialization are the formulas justified
               by the lines that are specified as the assumptions of that line
               (in the order of their numbers in that line), all of which must
               be previous lines.
        """
        assert line_number < len(self.lines)
        line = self.lines[line_number]

        if line.is_assumption():
            return line.formula in self.statement.assumptions

        if line.rule not in self.rules:
            return False

        for i in line.assumptions:
            if i >= line_number:
                return False

        derived_rule = self.rule_for_line(line_number)
        if derived_rule is None:
            return False

        key = (line.rule, derived_rule)
        if key in self._spec_cache:
            return self._spec_cache[key]

        ans = derived_rule.is_specialization_of(line.rule)
        self._spec_cache[key] = ans
        return ans

    def is_valid(self) -> bool:
        """Checks if the current proof is a valid proof of its claimed statement
        via its inference rules.

        Returns:
            ``True`` if the current proof is a valid proof of its claimed
            statement via its inference rules, ``False`` otherwise.
        """
        if len(self.lines) == 0:
            return False

        for i in range(len(self.lines)):
            if not self.is_line_valid(i):
                return False

        return self.lines[-1].formula == self.statement.conclusion


def prove_specialization(proof: Proof, specialization: InferenceRule) -> Proof:
    """Converts the given proof of an inference rule to a proof of the given
    specialization of that inference rule.

    Parameters:
        proof: valid proof to convert.
        specialization: specialization of the rule proven by the given proof.

    Returns:
        A valid proof of the given specialization via the same inference rules
        as the given proof.
    """
    assert proof.is_valid()
    assert specialization.is_specialization_of(proof.statement)

    sigma = proof.statement.specialization_map(specialization)
    assert sigma is not None

    new_lines = []
    for line in proof.lines:
        new_formula = line.formula.substitute_variables(sigma)
        if line.is_assumption():
            new_lines.append(Proof.Line(new_formula))
        else:
            new_lines.append(Proof.Line(new_formula, line.rule, line.assumptions))

    new_proof = Proof(specialization, proof.rules, new_lines)
    assert new_proof.is_valid()
    return new_proof


def _inline_proof_once(main_proof: Proof, line_number: int,
                       lemma_proof: Proof) -> Proof:
    """Inlines the given proof of a "lemma" inference rule into the given proof
    that uses that "lemma" rule, eliminating the usage of (a specialization of)
    that "lemma" rule in the specified line in the latter proof.

    Parameters:
        main_proof: valid proof to inline into.
        line_number: number of the line in `main_proof` that should be replaced.
        lemma_proof: valid proof of the inference rule of the specified line (an
            allowed inference rule of `main_proof`).

    Returns:
        A valid proof obtained by replacing the specified line in `main_proof`
        with a full (specialized) list of lines proving the formula of the
        specified line from the lines specified as the assumptions of that line,
        and updating justification line numbers specified throughout the proof
        to maintain the validity of the proof. The set of allowed inference
        rules in the returned proof is the union of the rules allowed in the two
        given proofs, but the "lemma" rule that is used in the specified line in
        `main_proof` is no longer used in the corresponding lines in the
        returned proof (and thus, this "lemma" rule is used one less time in the
        returned proof than in `main_proof`).
    """
    assert main_proof.is_valid()
    assert line_number < len(main_proof.lines)
    assert main_proof.lines[line_number].rule == lemma_proof.statement
    assert lemma_proof.is_valid()

    line = main_proof.lines[line_number]
    assert not line.is_assumption()
    specialized_rule = main_proof.rule_for_line(line_number)
    assert specialized_rule is not None
    assert specialized_rule.is_specialization_of(lemma_proof.statement)

    specialized_lemma_proof = prove_specialization(lemma_proof, specialized_rule)
    assert specialized_lemma_proof.is_valid()
    lemma_lines_count = len(specialized_lemma_proof.lines)
    shift = lemma_lines_count - 1

    new_lines = []
    new_lines.extend(main_proof.lines[:line_number])
    assumption_line_numbers = list(line.assumptions)
    for lemma_line in specialized_lemma_proof.lines:
        if lemma_line.is_assumption():
            i = specialized_rule.assumptions.index(lemma_line.formula)
            src_line_num = assumption_line_numbers[i]
            src_line = main_proof.lines[src_line_num]

            if src_line.is_assumption():
                new_lines.append(Proof.Line(src_line.formula))
            else:
                new_lines.append(Proof.Line(src_line.formula, src_line.rule, src_line.assumptions))
        else:
            shifted_assumptions = tuple(a + line_number for a in lemma_line.assumptions)
            new_lines.append(Proof.Line(lemma_line.formula, lemma_line.rule, shifted_assumptions))

    for l in main_proof.lines[line_number + 1:]:
        if l.is_assumption():
            new_lines.append(l)
        else:
            new_assumptions = []
            for a in l.assumptions:
                if a >= line_number:
                    new_assumptions.append(a + shift)
                else:
                    new_assumptions.append(a)
            new_lines.append(Proof.Line(l.formula, l.rule, tuple(new_assumptions)))

    new_rules = set(main_proof.rules) | set(lemma_proof.rules)
    inlined = Proof(main_proof.statement, new_rules, new_lines)
    return inlined


def inline_proof(main_proof: Proof, lemma_proof: Proof) -> Proof:
    """Inlines the given proof of a "lemma" inference rule into the given proof
    that uses that "lemma" rule, eliminating all usages of (any specializations
    of) that "lemma" rule in the latter proof.

    Parameters:
        main_proof: valid proof to inline into.
        lemma_proof: valid proof of one of the allowed inference rules of
            `main_proof`.

    Returns:
        A valid proof obtained from `main_proof` by inlining (an appropriate
        specialization of) `lemma_proof` in lieu of each line that specifies the
        "lemma" inference rule proved by `lemma_proof` as its justification. The
        set of allowed inference rules in the returned proof is the union of the
        rules allowed in the two given proofs but without the "lemma" rule
        proved by `lemma_proof`.
    """
    assert main_proof.is_valid()
    assert lemma_proof.is_valid()

    current = main_proof
    while True:
        line_to_inline = None
        for i, line in enumerate(current.lines):
            if line.rule == lemma_proof.statement:
                line_to_inline = i
                break
        if line_to_inline is None:
            break
        current = _inline_proof_once(current, line_to_inline, lemma_proof)

    new_rules = set(current.rules)
    if lemma_proof.statement in new_rules:
        new_rules.remove(lemma_proof.statement)
    result = Proof(current.statement, new_rules, current.lines)
    return result
