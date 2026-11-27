# SPDX-License-Identifier: Apache-2.0
"""Tests for symbolic grade constraint inference and Rocq certificate replay."""

from tests.harness import Case, ensure, raises
from toolchain import graded_inference as gi


def _test_exact_and_linear_propagation() -> None:
    x = gi.GradeMeta("x", gi.InferenceDomain.NAT_EXACT, (1, 0, 1, 5))
    y = gi.GradeMeta("y", gi.InferenceDomain.NAT_EXACT, (1, 6, 1, 10))
    res = gi.solve_constraints(
        [
            gi.GradeConstraint(gi.GradeVar(x), "eq", gi.GradeLit(2), (1, 0), "x bound"),
            gi.GradeConstraint(
                gi.GradeAdd(gi.GradeVar(x), gi.GradeVar(y)),
                "eq",
                gi.GradeLit(5),
                (2, 0),
                "sum equals 5",
            ),
        ],
        gi.InferenceDomain.NAT_EXACT,
        metas=(x, y),
    )
    ensure(res.ok and res.assignments == {"x": 2, "y": 3}, f"unexpected exact solution: {res}")
    ensure(res.certificate is not None and gi.parse_rocq_assumptions_count(res.certificate.gallina) == 0,
           "exact certificate must declare zero axioms")

    # NatExact must NEVER weaken `le` into `<=`!
    le_mismatch = gi.solve_constraints(
        [gi.GradeConstraint(gi.GradeLit(1), "le", gi.GradeLit(2), (3, 0), "attempt weakening")],
        gi.InferenceDomain.NAT_EXACT,
    )
    ensure(not le_mismatch.ok and le_mismatch.status == "inconsistent" and le_mismatch.certificate is None,
           f"NatExact weakened 1 <= 2: {le_mismatch}")

    # Linear must also enforce exact equality and refuse weakening or dropping.
    lin_x = gi.GradeMeta("lx", gi.InferenceDomain.LINEAR, (4, 0))
    lin_ok = gi.solve_constraints(
        [gi.GradeConstraint(gi.GradeVar(lin_x), "le", gi.GradeLit(1), (4, 0), "linear use")],
        gi.InferenceDomain.LINEAR,
        metas=(lin_x,),
    )
    ensure(lin_ok.ok and lin_ok.assignments == {"lx": 1}, f"Linear failed exact 1: {lin_ok}")

    lin_bad = gi.solve_constraints(
        [gi.GradeConstraint(gi.GradeLit(0), "le", gi.GradeLit(1), (5, 0), "linear drop")],
        gi.InferenceDomain.LINEAR,
    )
    ensure(not lin_bad.ok and lin_bad.status == "inconsistent", f"Linear allowed weakening 0 <= 1: {lin_bad}")


def _test_bounded_presence_and_affine() -> None:
    b1 = gi.GradeMeta("b1", gi.InferenceDomain.NAT_BOUND, (1, 0))
    b2 = gi.GradeMeta("b2", gi.InferenceDomain.NAT_BOUND, (2, 0))
    bounded = gi.solve_constraints(
        [
            gi.GradeConstraint(gi.GradeLit(2), "le", gi.GradeVar(b1), (1, 0), "lower bound"),
            gi.GradeConstraint(gi.GradeVar(b1), "le", gi.GradeLit(5), (1, 5), "upper bound"),
            gi.GradeConstraint(gi.GradeVar(b2), "le", gi.GradeLit(3), (2, 0), "only upper bound"),
        ],
        gi.InferenceDomain.NAT_BOUND,
        metas=(b1, b2),
    )
    ensure(bounded.ok and bounded.assignments == {"b1": 2, "b2": 0}, f"wrong minimal NatBound: {bounded}")

    p1 = gi.GradeMeta("p1", gi.InferenceDomain.PRESENCE, (1, 0))
    p2 = gi.GradeMeta("p2", gi.InferenceDomain.PRESENCE, (2, 0))
    pres = gi.solve_constraints(
        [
            gi.GradeConstraint(
                gi.GradeAdd(gi.GradeVar(p1), gi.GradeVar(p2)),
                "eq",
                gi.GradeLit(0),
                (1, 0),
                "absent sum",
            ),
            gi.GradeConstraint(
                gi.GradeAdd(gi.GradeLit(1), gi.GradeLit(1)),
                "eq",
                gi.GradeLit(1),
                (2, 0),
                "idempotent presence add",
            ),
        ],
        gi.InferenceDomain.PRESENCE,
        metas=(p1, p2),
    )
    ensure(pres.ok and pres.assignments == {"p1": 0, "p2": 0}, f"wrong Presence result: {pres}")

    a1 = gi.GradeMeta("a1", gi.InferenceDomain.AFFINE, (1, 0))
    aff_ok = gi.solve_constraints(
        [gi.GradeConstraint(gi.GradeLit(0), "le", gi.GradeVar(a1), (1, 0), "affine drop")],
        gi.InferenceDomain.AFFINE,
        metas=(a1,),
    )
    ensure(aff_ok.ok and aff_ok.assignments == {"a1": 0}, f"wrong Affine minimal result: {aff_ok}")

    aff_over = gi.solve_constraints(
        [
            gi.GradeConstraint(
                gi.GradeAdd(gi.GradeLit(1), gi.GradeLit(1)),
                "le",
                gi.GradeLit(1),
                (2, 0),
                "affine double use",
            ),
        ],
        gi.InferenceDomain.AFFINE,
    )
    ensure(not aff_over.ok and aff_over.status == "inconsistent", f"Affine allowed 1 + 1 <= 1: {aff_over}")


def _test_symbolic_polynomials_and_joins() -> None:
    # Semiring distributivity (q + r) * s == q * s + r * s in NatExact without guessing q, r, s
    poly_eq = gi.solve_constraints(
        [
            gi.GradeConstraint(
                gi.GradeMul(gi.GradeAdd(gi.GradeVar("q"), gi.GradeVar("r")), gi.GradeVar("s")),
                "eq",
                gi.GradeAdd(
                    gi.GradeMul(gi.GradeVar("q"), gi.GradeVar("s")),
                    gi.GradeMul(gi.GradeVar("r"), gi.GradeVar("s")),
                ),
                (1, 0),
                "distributivity",
            ),
        ],
        gi.InferenceDomain.NAT_EXACT,
    )
    ensure(poly_eq.ok and poly_eq.certificate is not None, f"polynomial distributivity failed: {poly_eq}")

    # Monotonic inequality q <= q + r in NatBound
    poly_le = gi.solve_constraints(
        [
            gi.GradeConstraint(
                gi.GradeVar("q"),
                "le",
                gi.GradeAdd(gi.GradeVar("q"), gi.GradeVar("r")),
                (2, 0),
                "monotone add",
            ),
        ],
        gi.InferenceDomain.NAT_BOUND,
    )
    ensure(poly_le.ok and poly_le.certificate is not None, f"polynomial inequality failed: {poly_le}")

    # Branch join in NatBound vs NatExact
    j = gi.GradeMeta("j", gi.InferenceDomain.NAT_BOUND, (3, 0))
    join_bound = gi.solve_constraints(
        [
            gi.GradeConstraint(
                gi.GradeJoin(gi.GradeLit(2), gi.GradeLit(5)),
                "le",
                gi.GradeVar(j),
                (3, 0),
                "branch join",
            ),
        ],
        gi.InferenceDomain.NAT_BOUND,
        metas=(j,),
    )
    ensure(join_bound.ok and join_bound.assignments == {"j": 5}, f"join in NatBound failed: {join_bound}")

    join_exact_bad = gi.solve_constraints(
        [
            gi.GradeConstraint(
                gi.GradeJoin(gi.GradeLit(2), gi.GradeLit(5)),
                "eq",
                gi.GradeLit(5),
                (3, 0),
                "exact join mismatch",
            ),
        ],
        gi.InferenceDomain.NAT_EXACT,
    )
    ensure(not join_exact_bad.ok and join_exact_bad.status == "inconsistent",
           f"NatExact accepted unequal branch join: {join_exact_bad}")


def _test_residuals_and_negative_controls() -> None:
    # Ambiguous multi-variable sum: x + y = 3 in NatExact
    x = gi.GradeMeta("x", gi.InferenceDomain.NAT_EXACT, (1, 0))
    y = gi.GradeMeta("y", gi.InferenceDomain.NAT_EXACT, (1, 5))
    ambiguous = gi.solve_constraints(
        [gi.GradeConstraint(gi.GradeAdd(gi.GradeVar(x), gi.GradeVar(y)), "eq", gi.GradeLit(3))],
        gi.InferenceDomain.NAT_EXACT,
        metas=(x, y),
    )
    ensure(not ambiguous.ok and ambiguous.status == "residual" and ambiguous.certificate is None,
           f"ambiguous constraint should leave residual: {ambiguous}")
    ensure(ambiguous.residuals[0].kind == "ambiguous", f"wrong residual kind: {ambiguous.residuals}")

    # Non-linear constraint: x * y = 6
    nonlinear = gi.solve_constraints(
        [gi.GradeConstraint(gi.GradeMul(gi.GradeVar(x), gi.GradeVar(y)), "eq", gi.GradeLit(6))],
        gi.InferenceDomain.NAT_EXACT,
        metas=(x, y),
    )
    ensure(not nonlinear.ok and nonlinear.residuals[0].kind == "non_linear",
           f"non-linear constraint should leave residual: {nonlinear}")

    # Underconstrained meta
    z = gi.GradeMeta("z", gi.InferenceDomain.NAT_EXACT, (2, 0))
    under = gi.solve_constraints([], gi.InferenceDomain.NAT_EXACT, metas=(z,))
    ensure(not under.ok and under.residuals[0].kind == "underconstrained",
           f"unconstrained meta should leave residual: {under}")

    # Budget exhaustion
    exhausted = gi.solve_constraints(
        [gi.GradeConstraint(gi.GradeVar(x), "eq", gi.GradeLit(1))],
        gi.InferenceDomain.NAT_EXACT,
        metas=(x,),
        max_steps=1,
    )
    # Step 1 resolves x=1, then loop checks active (empty) unless multi-step chain:
    chain_a = gi.GradeMeta("a", gi.InferenceDomain.NAT_EXACT)
    chain_b = gi.GradeMeta("b", gi.InferenceDomain.NAT_EXACT)
    chain_c = gi.GradeMeta("c", gi.InferenceDomain.NAT_EXACT)
    budget_hit = gi.solve_constraints(
        [
            gi.GradeConstraint(gi.GradeVar(chain_a), "eq", gi.GradeLit(1)),
            gi.GradeConstraint(gi.GradeVar(chain_b), "eq", gi.GradeVar(chain_a)),
            gi.GradeConstraint(gi.GradeVar(chain_c), "eq", gi.GradeVar(chain_b)),
        ],
        gi.InferenceDomain.NAT_EXACT,
        metas=(chain_a, chain_b, chain_c),
        max_steps=1,
    )
    ensure(not budget_hit.ok and budget_hit.status == "budget_exhausted"
           and budget_hit.residuals[0].kind == "budget_exhausted"
           and budget_hit.certificate is None,
           f"expected budget_exhausted residual: {budget_hit}")
    _ = exhausted


def _test_rocq_certificate_replay_and_tamper_refusal() -> None:
    x = gi.GradeMeta("x", gi.InferenceDomain.NAT_EXACT, (1, 0))
    y = gi.GradeMeta("y", gi.InferenceDomain.NAT_EXACT, (1, 5))
    exact_res = gi.solve_constraints(
        [
            gi.GradeConstraint(gi.GradeVar(x), "eq", gi.GradeLit(2)),
            gi.GradeConstraint(gi.GradeAdd(gi.GradeVar(x), gi.GradeVar(y)), "eq", gi.GradeLit(5)),
            gi.GradeConstraint(
                gi.GradeMul(gi.GradeAdd(gi.GradeVar("q"), gi.GradeVar("r")), gi.GradeVar("s")),
                "eq",
                gi.GradeAdd(
                    gi.GradeMul(gi.GradeVar("q"), gi.GradeVar("s")),
                    gi.GradeMul(gi.GradeVar("r"), gi.GradeVar("s")),
                ),
            ),
        ],
        gi.InferenceDomain.NAT_EXACT,
        metas=(x, y),
        verify_rocq=True,
    )
    ensure(exact_res.ok and exact_res.certificate is not None, "exact Rocq replay failed")

    # Bounded + Presence + Affine + Linear Rocq replays with zero axioms
    b = gi.GradeMeta("b", gi.InferenceDomain.NAT_BOUND)
    bounded_res = gi.solve_constraints(
        [
            gi.GradeConstraint(gi.GradeLit(2), "le", gi.GradeVar(b)),
            gi.GradeConstraint(gi.GradeVar(b), "le", gi.GradeLit(4)),
            gi.GradeConstraint(gi.GradeVar("q"), "le", gi.GradeAdd(gi.GradeVar("q"), gi.GradeVar("r"))),
        ],
        gi.InferenceDomain.NAT_BOUND,
        metas=(b,),
        verify_rocq=True,
    )
    ensure(bounded_res.ok, "NatBound Rocq replay failed")

    p = gi.GradeMeta("p", gi.InferenceDomain.PRESENCE)
    pres_res = gi.solve_constraints(
        [gi.GradeConstraint(gi.GradeVar(p), "le", gi.GradeLit(1))],
        gi.InferenceDomain.PRESENCE,
        metas=(p,),
        verify_rocq=True,
    )
    ensure(pres_res.ok, "Presence Rocq replay failed")

    aff = gi.GradeMeta("aff", gi.InferenceDomain.AFFINE)
    aff_res = gi.solve_constraints(
        [gi.GradeConstraint(gi.GradeLit(0), "le", gi.GradeVar(aff))],
        gi.InferenceDomain.AFFINE,
        metas=(aff,),
        verify_rocq=True,
    )
    ensure(aff_res.ok, "Affine Rocq replay failed")

    lin = gi.GradeMeta("lin", gi.InferenceDomain.LINEAR)
    lin_res = gi.solve_constraints(
        [gi.GradeConstraint(gi.GradeVar(lin), "eq", gi.GradeLit(1))],
        gi.InferenceDomain.LINEAR,
        metas=(lin,),
        verify_rocq=True,
    )
    ensure(lin_res.ok, "Linear Rocq replay failed")

    # Tampered certificate witness MUST be rejected by Rocq!
    cert = exact_res.certificate
    if cert is None:
        raise AssertionError("expected exact certificate")
    tampered_gallina = cert.gallina.replace("=> 2", "=> 99", 1)
    ensure(tampered_gallina != cert.gallina, "tamper did not alter certificate")
    tampered = gi.GradeCertificate(
        domain=cert.domain,
        assignments=cert.assignments,
        constraints=cert.constraints,
        gallina=tampered_gallina,
        module_name=cert.module_name,
        theorem_names=cert.theorem_names,
        source_sha256=cert.source_sha256,
    )
    with raises(ValueError):
        gi.verify_certificate(tampered)

    # Tampered axiom in certificate MUST be rejected by solver_ledger.audit!
    axiom_gallina = cert.gallina.replace(
        "Proof.\n  cbn. vm_compute. reflexivity.\nQed.",
        "Axiom holdfast_solver_fake : False.\nProof.\n  exact (False_rect _ holdfast_solver_fake).\nQed.",
        1,
    )
    ensure("Axiom holdfast_solver_fake" in axiom_gallina, "failed to inject axiom")
    axiom_cert = gi.GradeCertificate(
        domain=cert.domain,
        assignments=cert.assignments,
        constraints=cert.constraints,
        gallina=axiom_gallina,
        module_name=cert.module_name,
        theorem_names=cert.theorem_names,
        source_sha256=cert.source_sha256,
    )
    with raises(ValueError):
        gi.verify_certificate(axiom_cert)


def cases() -> list[Case]:
    return [
        Case("exact and linear constraint propagation without weakening", _test_exact_and_linear_propagation),
        Case("bounded, presence, and affine minimal constraint solving", _test_bounded_presence_and_affine),
        Case("symbolic polynomial normal forms and branch joins", _test_symbolic_polynomials_and_joins),
        Case("explicit residual goals for ambiguous, non-linear, underconstrained, and budgeted cases",
             _test_residuals_and_negative_controls),
        Case("Rocq certificate kernel replay and tampered certificate refusal",
             _test_rocq_certificate_replay_and_tamper_refusal, lane="toolchain"),
    ]
