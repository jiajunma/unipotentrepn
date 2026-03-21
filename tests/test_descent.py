"""
test_descent.py - Test that descent_drc is the inverse of lifting for all types.

For each root system type, generate DRC diagrams via dpart2drc (dual partition),
then lift each DRC using the appropriate lift function, and verify that
descent_drc applied to the lifted DRC recovers the original source DRC.

Lift-descent pairs tested:
  Type C: lift_drc_D_C (D -> C), descent_drc(_, 'C') should recover D-drc
  Type D: lift_drc_C_D (C -> D), descent_drc(_, 'D') should recover C-drc
  Type M: lift_extdrc_B_M (B -> M), descent_drc(_, 'M') should recover B-ext-drc
  Type B: lift_drc_M_B (M -> B), descent_drc(_, 'B') should recover M-drc

Usage:
  python3 tests/test_descent.py
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from combunipotent import (
    dpart2drc, verify_drc, reg_drc, str_dgms,
    split_extdrc_B,
)
from combunipotent.drclift import (
    descent_drc,
    lift_drc_D_C, lift_drc_D_C_trivial, lift_drc_D_C_gd, lift_drc_D_C_det,
    lift_drc_C_D,
    lift_drc_M_B,
    lift_extdrc_B_M,
    ext_drc2drc,
    twist_sp2nsp, twist_nsp2sp,
)
from combunipotent.drc import gp_form_C, gp_form_D, gp_form_M


# ---- Test data: (dual_partition, rtype) ----
# These are dual partitions used to generate source DRCs.

# D->C lift: source is D-type DRC, target is C-type DRC
TEST_D_TO_C = [
    (1, 1), (3, 1), (3, 3), (5, 1), (5, 3), (5, 5),
    (3, 3, 1, 1), (5, 3, 1, 1), (5, 5, 1, 1),
    (7, 3), (7, 5), (7, 5, 3, 1), (7, 7, 3, 3),
    (5, 5, 3, 3), (9, 7, 5, 3),
]

# C->D lift: source is C-type DRC, target is D-type DRC
TEST_C_TO_D = [
    (1,), (3,), (5,), (3, 1, 1), (5, 1, 1),
    (5, 3, 1), (5, 3, 3), (5, 5, 1),
    (7, 3, 1), (7, 5, 1), (7, 5, 3), (7, 7, 1),
    (9, 5, 3),
]

# M->B lift: source is M-type DRC, target is B-type extended DRC
TEST_M_TO_B = [
    (2, 2), (4, 2), (4, 4), (6, 2), (6, 4), (6, 6),
    (4, 4, 2, 2), (6, 4, 2, 2), (8, 4), (8, 6),
    (8, 6, 4, 2), (8, 8, 4, 4), (6, 6, 4, 4),
    (10, 8, 6, 4),
]

# B->M lift: source is B-type extended DRC, target is M-type DRC
TEST_B_TO_M = [
    (2, 2), (4, 2), (4, 4), (6, 2), (6, 4), (6, 6),
    (4, 4, 2, 2), (6, 4, 2, 2), (8, 4), (8, 6),
    (8, 6, 4, 2),
]


def test_descent_D_to_C():
    """
    Test: lift D-type DRC to C via lift_drc_D_C_trivial,
    then descent_drc(_, 'C') should recover the D-type DRC.
    """
    n_tested = 0
    failures = []

    for dpart in TEST_D_TO_C:
        d_drcs = dpart2drc(dpart, rtype='D', report=False)
        for drc in d_drcs:
            drc = reg_drc(drc)
            # Trivial lift: D -> C
            ndrc = lift_drc_D_C_trivial(drc)
            if ndrc is None:
                continue
            ndrc = reg_drc(ndrc)
            # Descent: C -> D
            ddrc = descent_drc(ndrc, 'C')
            ddrc = reg_drc(ddrc)
            n_tested += 1
            if ddrc != drc:
                failures.append((dpart, drc, ndrc, ddrc, 'trivial'))

            # Det lift: D -> C (non-special shape)
            nddrc = lift_drc_D_C_det(drc)
            if nddrc is not None:
                nddrc = reg_drc(nddrc)
                dddrc = descent_drc(nddrc, 'C')
                dddrc = reg_drc(dddrc)
                n_tested += 1
                if dddrc != drc:
                    failures.append((dpart, drc, nddrc, dddrc, 'det'))

    return n_tested, failures


def test_descent_C_to_D():
    """
    Test: lift C-type DRC to D via lift_drc_C_D,
    then descent_drc(_, 'D') should recover the C-type DRC.
    """
    n_tested = 0
    failures = []

    for dpart in TEST_C_TO_D:
        c_drcs = dpart2drc(dpart, rtype='C', report=False)
        for drc in c_drcs:
            drc = reg_drc(drc)
            # Lift C -> D with various column lengths
            crow = len(drc[0][0]) + 1 if len(drc[0]) > 0 and len(drc[0][0]) > 0 else 1
            ndrcs = lift_drc_C_D(drc, crow)
            for ndrc, twist in ndrcs:
                ndrc = reg_drc(ndrc)
                # Descent: D -> C
                ddrc = descent_drc(ndrc, 'D')
                ddrc = reg_drc(ddrc)
                n_tested += 1
                if ddrc != drc:
                    failures.append((dpart, drc, ndrc, ddrc, f'crow={crow}'))

    return n_tested, failures


def test_descent_M_to_B():
    """
    Test: lift M-type DRC to B via lift_drc_M_B,
    then descent_drc(_, 'B') should recover the M-type DRC.
    """
    n_tested = 0
    failures = []

    for dpart in TEST_M_TO_B:
        m_drcs = dpart2drc(dpart, rtype='M', report=False)
        for drc in m_drcs:
            drc = reg_drc(drc)
            # aL = dpart[0]//2 (first row of dual partition divided by 2)
            aL = dpart[0] // 2
            ndrcs = lift_drc_M_B(drc, aL)
            for ndrc, twist in ndrcs:
                ndrc = reg_drc(ndrc)
                # Descent: B -> M
                try:
                    ddrc = descent_drc(ndrc, 'B')
                    ddrc = reg_drc(ddrc)
                except Exception as e:
                    failures.append((dpart, drc, ndrc, None, f'descent raised: {e}'))
                    n_tested += 1
                    continue
                n_tested += 1
                if ddrc != drc:
                    failures.append((dpart, drc, ndrc, ddrc, f'aL={aL}'))

    return n_tested, failures


def test_descent_B_to_M():
    """
    Test: lift B-type extended DRC to M via lift_extdrc_B_M,
    then descent_drc(_, 'M') should recover the B-type extended DRC.
    """
    n_tested = 0
    failures = []

    for dpart in TEST_B_TO_M:
        # Generate B-type extended DRCs via test_dpart2drcLS
        # Since we can't easily get extended DRCs from dpart2drc,
        # we build them from M-type DRCs + lift_drc_M_B
        m_drcs = dpart2drc(dpart, rtype='M', report=False)
        for mdrc in m_drcs:
            mdrc = reg_drc(mdrc)
            aL = dpart[0] // 2
            ext_drcs = lift_drc_M_B(mdrc, aL)
            for edrc, twist in ext_drcs:
                edrc = reg_drc(edrc)
                # Now lift B -> M
                a = aL  # same column length
                ndrc = lift_extdrc_B_M(edrc, a)
                if ndrc is None:
                    continue
                ndrc = reg_drc(ndrc)
                # Descent: M -> B should recover edrc
                try:
                    ddrc = descent_drc(ndrc, 'M')
                    ddrc = reg_drc(ddrc)
                except Exception as e:
                    failures.append((dpart, edrc, ndrc, None, f'descent raised: {e}'))
                    n_tested += 1
                    continue
                n_tested += 1
                if ddrc != edrc:
                    failures.append((dpart, edrc, ndrc, ddrc, f'aL={aL}'))

    return n_tested, failures


def report_failures(name, n_tested, failures):
    """Print failure details and return whether all passed."""
    if failures:
        print(f"\n  FAILED {name}: {len(failures)}/{n_tested} failed")
        for dpart, src, lifted, descent, info in failures[:5]:
            print(f"    dpart={dpart}, info={info}")
            print(f"    source:\n{str_dgms(src)}")
            print(f"    lifted:\n{str_dgms(lifted)}")
            if descent is not None:
                print(f"    descent (got):\n{str_dgms(descent)}")
            print(f"    expected:\n{str_dgms(src)}")
            print()
        if len(failures) > 5:
            print(f"    ... and {len(failures)-5} more")
        return False
    else:
        print(f"  PASSED {name}: {n_tested} lift-descent pairs verified")
        return True


def main():
    all_passed = True

    print(f"\n{'='*60}")
    print("Testing descent_drc as inverse of lifting")
    print(f"{'='*60}")

    n, f = test_descent_D_to_C()
    all_passed &= report_failures("D->C->D (descent 'C')", n, f)

    n, f = test_descent_C_to_D()
    all_passed &= report_failures("C->D->C (descent 'D')", n, f)

    n, f = test_descent_M_to_B()
    all_passed &= report_failures("M->B->M (descent 'B')", n, f)

    n, f = test_descent_B_to_M()
    all_passed &= report_failures("B->M->B (descent 'M')", n, f)

    print(f"\n{'='*60}")
    if all_passed:
        print("ALL TESTS PASSED")
    else:
        print("SOME TESTS FAILED")
        sys.exit(1)


if __name__ == '__main__':
    main()
