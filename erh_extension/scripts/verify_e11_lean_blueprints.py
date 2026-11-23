#!/usr/bin/env python3
"""
Wave-7 E11 Static Verification & Archive-Alignment Audit Script
Checks all 7 Lean 4.33.1 ERH blueprint modules in erh_research/lean_erh_blueprint/:
  Modules 1-3 (Wave-3 A19): RelCMHostVariantII.lean, GeneralizedLemmaM_HidaSetting4.lean, MainERH.lean
  Module  4   (Wave-4 B09): ChCore_ZqTower.lean
  Modules 5-7 (Wave-7 E11): GSp4CountI_RealQuadratic.lean, CountVAbsorption_C08_C09.lean,
                            PrismaticLinearCokernel_D10_D11.lean

NOTE: This is a static syntactic, delimiter-balance, universe-hygiene, and archive-symbol
alignment verifier backed by tools/lean_index.db and riemann-hypothesis/src/ (full Lean 4.33.1
elaboration/compilation is not performed here as `lean`/`lake` are not installed in this environment).
"""

import math
import os
import re
import sqlite3
import sys
from pathlib import Path

ROOT = Path("/Users/tiancaikeyize/Downloads/阅读黎曼猜想证明")
BLUEPRINT_DIR = ROOT / "erh_research" / "lean_erh_blueprint"
SRC_DIR = ROOT / "riemann-hypothesis" / "src"
DB_PATH = ROOT / "tools" / "lean_index.db"

WAVE7_NEW_FILES = [
    "GSp4CountI_RealQuadratic.lean",
    "CountVAbsorption_C08_C09.lean",
    "PrismaticLinearCokernel_D10_D11.lean",
]

PRIOR_CLEAN_FILES = [
    "RelCMHostVariantII.lean",
    "GeneralizedLemmaM_HidaSetting4.lean",
    "ChCore_ZqTower.lean",
]

LEGACY_WAVE3_MAIN = "MainERH.lean"

ALL_BLUEPRINTS = PRIOR_CLEAN_FILES + [LEGACY_WAVE3_MAIN] + WAVE7_NEW_FILES

# Documented legacy Wave-3 axioms in untouched MainERH.lean (immutability policy: do not edit Wave-3 files)
EXPECTED_LEGACY_MAINERH_AXIOMS = {
    295: "extendedRiemannHypothesis_of_totallyReal_D4_725_spec",
    325: "extendedRiemannHypothesis_regimeA_spec",
    356: "extendedRiemannHypothesis_regimeB_spec",
}

# Explicit archive symbol ledger for the 3 new Wave-7 blueprints:
# (blueprint_file, exact_archive_full_name, archive_rel_path, expected_line)
WAVE7_SYMBOL_LEDGER = [
    # Module 5: GSp4CountI_RealQuadratic.lean
    ("GSp4CountI_RealQuadratic.lean", "UpperTheory.V.Z.Kato.WeilSphericalRecords.KatoTwoW",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/KatoQuadraticCharacters/SphericalDecomposition/KatoTwoW.lean", 10),
    ("GSp4CountI_RealQuadratic.lean", "UpperTheory.V.Z.Kato.WeilSphericalRecords.kUse'",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/KatoQuadraticCharacters/SphericalDecomposition/KatoTwoW.lean", 26),
    ("GSp4CountI_RealQuadratic.lean", "UpperTheory.V.Z.Kato.Used",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/KatoQuadraticCharacters/KatoTwoOfUseN.lean", 11),
    ("GSp4CountI_RealQuadratic.lean", "UpperTheory.V.Z.Kato.KatoTwo",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/KatoQuadraticCharacters/KatoTwoOfUseN.lean", 43),
    ("GSp4CountI_RealQuadratic.lean", "UpperTheory.V.Z.Kato.RigII",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/KatoQuadraticCharacters/KatoTwoOfUseN.lean", 49),
    ("GSp4CountI_RealQuadratic.lean", "UpperTheory.V.Z.Win.WitAQ",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/AutomorphyLifting/AAcrossOf.lean", 17),
    ("GSp4CountI_RealQuadratic.lean", "UpperTheory.V.Af.BlochKatoSelmerVanishes",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/AutomorphicForms/BlochKatoSelmerVanishes.lean", 144),
    ("GSp4CountI_RealQuadratic.lean", "UpperTheory.V.U3.Dat",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeGroups/RhoKApply.lean", 16),
    ("GSp4CountI_RealQuadratic.lean", "UpperTheory.V.U3.Dat.Kill",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeGroups/RhoKApply.lean", 61),
    ("GSp4CountI_RealQuadratic.lean", "UpperTheory.V.U3.Dat.Ring",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeGroups/RhoKApply.lean", 66),
    ("GSp4CountI_RealQuadratic.lean", "UpperTheory.V.U3.Dat.IsModular",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeGroups/RhoKApply.lean", 91),
    ("GSp4CountI_RealQuadratic.lean", "UpperTheory.V.U3.dat_facts",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeGroups/DatFacts.lean", 70),
    ("GSp4CountI_RealQuadratic.lean", "UpperTheory.V.U3.admissible_of_typeII",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeGroups/AdmissibleOfTypeII.lean", 103),
    ("GSp4CountI_RealQuadratic.lean", "UpperTheory.V.U3.KatoUse",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeGroups/KatoUse.lean", 13),
    ("GSp4CountI_RealQuadratic.lean", "UpperTheory.V.HV.GD",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/Counts.lean", 9),
    ("GSp4CountI_RealQuadratic.lean", "UpperTheory.V.HV.CountI",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/Counts.lean", 53),
    ("GSp4CountI_RealQuadratic.lean", "UpperTheory.V.Z.Kato.WeilSphericalRecords.bloch_kato_selmer_vanishes_of_type_ii_modular_ext",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/TypeIIOfBlochKatoLocalPoint.lean", 16),

    # Module 6: CountVAbsorption_C08_C09.lean
    ("CountVAbsorption_C08_C09.lean", "UpperTheory.V.HV.c2",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/DirichletPrimeToLPartMulLPowerPart.lean", 92),
    ("CountVAbsorption_C08_C09.lean", "UpperTheory.V.HV.n0",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/DirichletPrimeToLPartMulLPowerPart.lean", 102),
    ("CountVAbsorption_C08_C09.lean", "UpperTheory.V.HV.Host",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/DirichletPrimeToLPartMulLPowerPart.lean", 148),
    ("CountVAbsorption_C08_C09.lean", "UpperTheory.V.HV.Host.R1",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/DirichletPrimeToLPartMulLPowerPart.lean", 206),
    ("CountVAbsorption_C08_C09.lean", "UpperTheory.V.HV.Host.CaseV",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/DirichletPrimeToLPartMulLPowerPart.lean", 219),
    ("CountVAbsorption_C08_C09.lean", "UpperTheory.V.HV.CountShape",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/Counts.lean", 60),
    ("CountVAbsorption_C08_C09.lean", "UpperTheory.V.HV.CountV",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/Counts.lean", 69),
    ("CountVAbsorption_C08_C09.lean", "UpperTheory.V.UnitaryThreeInertia.HostData",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeDeformations/IsHostFrame.lean", 12),
    ("CountVAbsorption_C08_C09.lean", "UpperTheory.V.UnitaryThreeInertia.eta4",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeDeformations/IsHostFrame.lean", 26),
    ("CountVAbsorption_C08_C09.lean", "UpperTheory.V.UnitaryThreeInertia.IsHostFrame",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeDeformations/IsHostFrame.lean", 32),
    ("CountVAbsorption_C08_C09.lean", "UpperTheory.V.UnitaryThreeInertia.XData",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeDeformations/IsHostFrame.lean", 47),
    ("CountVAbsorption_C08_C09.lean", "UpperTheory.V.UnitaryThreeInertia.hostData_of_host",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeDeformations/HostDataOf.lean", 9),
    ("CountVAbsorption_C08_C09.lean", "UpperTheory.V.UnitaryThreeInertia.HostVanE",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeDeformations/HostNumber.lean", 9),
    ("CountVAbsorption_C08_C09.lean", "UpperTheory.V.UnitaryThreeInertia.HostXpp",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeDeformations/HostNumber.lean", 14),
    ("CountVAbsorption_C08_C09.lean", "UpperTheory.V.UnitaryThreeInertia.HostRigid",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeDeformations/HostNumber.lean", 19),
    ("CountVAbsorption_C08_C09.lean", "UpperTheory.V.UnitaryThreeInertia.HostNumber",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeDeformations/HostNumber.lean", 26),
    ("CountVAbsorption_C08_C09.lean", "UpperTheory.V.UnitaryThreeInertia.countV_of_finiteness_duality_euler_host",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/CountVOf.lean", 33),
    ("CountVAbsorption_C08_C09.lean", "UpperTheory.V.GradeZeroInterpolatingElement.Raw",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/SymplecticGSp4/DecompSigmaOrd.lean", 34),
    ("CountVAbsorption_C08_C09.lean", "UpperTheory.V.GradeZeroInterpolatingElement.Raw.Psi",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/SymplecticGSp4/DecompSigmaOrd.lean", 57),
    ("CountVAbsorption_C08_C09.lean", "UpperTheory.V.GradeZeroInterpolatingElement.Raw.al",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/SymplecticGSp4/DecompSigmaOrd.lean", 59),
    ("CountVAbsorption_C08_C09.lean", "UpperTheory.V.GradeZeroInterpolatingElement.Raw.be",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/SymplecticGSp4/DecompSigmaOrd.lean", 61),
    ("CountVAbsorption_C08_C09.lean", "UpperTheory.V.GradeZeroInterpolatingElement.Raw.th",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/SymplecticGSp4/DecompSigmaOrd.lean", 63),
    ("CountVAbsorption_C08_C09.lean", "UpperTheory.V.GradeZeroInterpolatingElement.Raw.XVan",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/SymplecticGSp4/DecompSigmaOrd.lean", 90),
    ("CountVAbsorption_C08_C09.lean", "UpperTheory.V.GradeZeroInterpolatingElement.Raw.Good",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/SymplecticGSp4/DecompSigmaOrd.lean", 94),
    ("CountVAbsorption_C08_C09.lean", "UpperTheory.V.GradeZeroInterpolatingElement.nums",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/SymplecticGSp4/NumsZero.lean", 123),
    ("CountVAbsorption_C08_C09.lean", "UpperTheory.V.GradeZeroInterpolatingElement.dataEx",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/SymplecticGSp4/DataEx.lean", 366),
    ("CountVAbsorption_C08_C09.lean", "UpperTheory.V.X.lemmaX",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/LevelCohomology/LemmaX.lean", 78),
    ("CountVAbsorption_C08_C09.lean", "UpperTheory.V.X.corX",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/LevelCohomology/ChrInvNeg.lean", 197),

    # Module 7: PrismaticLinearCokernel_D10_D11.lean
    ("PrismaticLinearCokernel_D10_D11.lean", "Formalism.MainNotions.LiftingTheory.eWA",
     "Formalism/SharpRestriction/LevelLetterCocycles/LiftingTheory.lean", 17),
    ("PrismaticLinearCokernel_D10_D11.lean", "Formalism.MainNotions.LiftingTheory.eWB",
     "Formalism/SharpRestriction/LevelLetterCocycles/LiftingTheory.lean", 20),
    ("PrismaticLinearCokernel_D10_D11.lean", "Formalism.MainNotions.LiftingTheory.ePA",
     "Formalism/SharpRestriction/LevelLetterCocycles/LiftingTheory.lean", 27),
    ("PrismaticLinearCokernel_D10_D11.lean", "Formalism.MainNotions.LiftingTheory.ePB",
     "Formalism/SharpRestriction/LevelLetterCocycles/LiftingTheory.lean", 29),
    ("PrismaticLinearCokernel_D10_D11.lean", "Formalism.MainNotions.LiftingTheory.coreWX",
     "Formalism/SharpRestriction/LevelLetterCocycles/LiftingTheory.lean", 100),
    ("PrismaticLinearCokernel_D10_D11.lean", "Formalism.MainNotions.LiftingTheory.coreWB",
     "Formalism/SharpRestriction/LevelLetterCocycles/LiftingTheory.lean", 104),
    ("PrismaticLinearCokernel_D10_D11.lean", "Formalism.MainNotions.LiftingTheory.coreWA",
     "Formalism/SharpRestriction/LevelLetterCocycles/LiftingTheory.lean", 108),
    ("PrismaticLinearCokernel_D10_D11.lean", "Formalism.MainNotions.LiftingTheory.coreLiftA",
     "Formalism/SharpRestriction/LevelLetterCocycles/LiftingTheory.lean", 219),
    ("PrismaticLinearCokernel_D10_D11.lean", "Formalism.MainNotions.LiftingTheory.coreLiftB",
     "Formalism/SharpRestriction/LevelLetterCocycles/LiftingTheory.lean", 224),
    ("PrismaticLinearCokernel_D10_D11.lean", "Formalism.MainNotions.LiftingTheory.coreDesc",
     "Formalism/SharpRestriction/LevelLetterCocycles/LiftingTheory.lean", 462),
    ("PrismaticLinearCokernel_D10_D11.lean", "Formalism.MainNotions.LiftingTheory.LiftGaloisDescent",
     "Formalism/SharpRestriction/LevelLetterCocycles/LiftingTheory.lean", 577),
    ("PrismaticLinearCokernel_D10_D11.lean", "Formalism.MainNotions.LiftingTheory.LiftTheoremAllCases",
     "Formalism/SharpRestriction/LevelLetterCocycles/LiftingTheory.lean", 586),
    ("PrismaticLinearCokernel_D10_D11.lean", "Formalism.MainNotions.LocalSituation.TBat",
     "Formalism/SharpRestriction/LevelLetterCocycles/LocalSituation.lean", 165),
    ("PrismaticLinearCokernel_D10_D11.lean", "Formalism.LIFT.wBTail_of",
     "Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/Graded.lean", 115),
    ("PrismaticLinearCokernel_D10_D11.lean", "Formalism.LIFT.CocyclePolynomialSubmodules.uClaim_of",
     "Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/UClaim.lean", 194),
    ("PrismaticLinearCokernel_D10_D11.lean", "GlobalTheory.BSP.Digits",
     "Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsStratHom.lean", 125),
    ("PrismaticLinearCokernel_D10_D11.lean", "GlobalTheory.BSP.Env",
     "Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsStratHom.lean", 127),
    ("PrismaticLinearCokernel_D10_D11.lean", "GlobalTheory.BSP.Strat",
     "Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsStratHom.lean", 146),
    ("PrismaticLinearCokernel_D10_D11.lean", "GlobalTheory.BSP.Framed",
     "Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsStratHom.lean", 164),
    ("PrismaticLinearCokernel_D10_D11.lean", "GlobalTheory.BSP.IsStratHom",
     "Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsStratHom.lean", 170),
    ("PrismaticLinearCokernel_D10_D11.lean", "GlobalTheory.BSP.MReal",
     "Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsStratHom.lean", 177),
    ("PrismaticLinearCokernel_D10_D11.lean", "GlobalTheory.Cyc.ClassBound.class_bound",
     "Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CrystallineExtensionClassBound.lean", 359),
    ("PrismaticLinearCokernel_D10_D11.lean", "GlobalTheory.T.crystalline_extension_class_bound",
     "Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CrystallineExtensionClassBoundStatement.lean", 9),
    ("PrismaticLinearCokernel_D10_D11.lean", "GlobalTheory.PrismS.ker_theta_io",
     "Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsWachPrismOverIntegers.lean", 152),
    ("PrismaticLinearCokernel_D10_D11.lean", "GlobalTheory.PrismS.prismS",
     "Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsWachPrismOverIntegers.lean", 205),
    ("PrismaticLinearCokernel_D10_D11.lean", "GlobalTheory.PrismS.prismW",
     "Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsWachPrismOverIntegers.lean", 239),
    ("PrismaticLinearCokernel_D10_D11.lean", "GlobalTheory.PrismS.exists_prism",
     "Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsWachPrismOverIntegers.lean", 331),
    ("PrismaticLinearCokernel_D10_D11.lean", "GlobalTheory.T.exists_wach_prism_over_integers",
     "Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsWachPrismOverIntegersStatement.lean", 8),
    ("PrismaticLinearCokernel_D10_D11.lean", "GlobalTheory.Cyc.InvKilled.invariants_killed",
     "Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/InvariantsVanishAtPrimeOfAdmissible.lean", 156),
    ("PrismaticLinearCokernel_D10_D11.lean", "GlobalTheory.ExpImage.expStar_image",
     "Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DualExponentialImageContainsLattice.lean", 41),
    ("PrismaticLinearCokernel_D10_D11.lean", "GlobalTheory.Published.BhattScholzeIntegral",
     "Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/BhattScholzeIntegral.lean", 12),
    ("PrismaticLinearCokernel_D10_D11.lean", "UpperTheory.N.sN",
     "Development/AutomorphicArithmetic/ResidueCharacters/InvariantsKilledOverCyclotomicAlt.lean", 11),
    ("PrismaticLinearCokernel_D10_D11.lean", "UpperTheory.N.lamN",
     "Development/AutomorphicArithmetic/ResidueCharacters/InvariantsKilledOverCyclotomicAlt.lean", 13),
    ("PrismaticLinearCokernel_D10_D11.lean", "UpperTheory.N.eL",
     "Development/AutomorphicArithmetic/ResidueCharacters/InvariantsKilledOverCyclotomicAlt.lean", 15),
    ("PrismaticLinearCokernel_D10_D11.lean", "UpperTheory.N.c0L",
     "Development/AutomorphicArithmetic/ResidueCharacters/InvariantsKilledOverCyclotomicAlt.lean", 17),
    ("PrismaticLinearCokernel_D10_D11.lean", "UpperTheory.N.cBL",
     "Development/AutomorphicArithmetic/ResidueCharacters/InvariantsKilledOverCyclotomicAlt.lean", 19),
    ("PrismaticLinearCokernel_D10_D11.lean", "UpperTheory.N.Cyc",
     "Development/AutomorphicArithmetic/ResidueCharacters/InvariantsKilledOverCyclotomicAlt.lean", 23),
    ("PrismaticLinearCokernel_D10_D11.lean", "UpperTheory.N.LiftK",
     "Development/AutomorphicArithmetic/ResidueCharacters/InvariantsKilledOverCyclotomicAlt.lean", 31),
    ("PrismaticLinearCokernel_D10_D11.lean", "UpperTheory.N.InvariantsKilledOverCyclotomic",
     "Development/AutomorphicArithmetic/ResidueCharacters/InvariantsKilledOverCyclotomicAlt.lean", 38),
    ("PrismaticLinearCokernel_D10_D11.lean", "UpperTheory.N.TBK",
     "Development/AutomorphicArithmetic/ResidueCharacters/InvariantsKilledOverCyclotomicAlt.lean", 43),
    ("PrismaticLinearCokernel_D10_D11.lean", "UpperTheory.N.liftK_of",
     "Development/AutomorphicArithmetic/ResidueCharacters/LiftKOf.lean", 12),
]


def strip_comments_and_strings(text: str):
    """
    Strip Lean 4 nested block comments `/- ... -/`, line comments `-- ...`, and string literals
    `"..."`, preserving newlines so line numbers stay exact.
    Also verifies that block comments and string literals are properly closed.
    """
    out = []
    i = 0
    n = len(text)
    block_depth = 0
    in_line_comment = False
    in_string = False
    line = 1
    errors = []

    while i < n:
        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""

        if in_line_comment:
            if ch == "\n":
                in_line_comment = False
                out.append("\n")
                line += 1
            i += 1
            continue

        if block_depth > 0:
            if ch == "/" and nxt == "-":
                block_depth += 1
                i += 2
                continue
            if ch == "-" and nxt == "/":
                block_depth -= 1
                i += 2
                continue
            if ch == "\n":
                out.append("\n")
                line += 1
            i += 1
            continue

        if in_string:
            if ch == "\\":
                i += 2
                continue
            if ch == '"':
                in_string = False
                out.append(" ")
            elif ch == "\n":
                out.append("\n")
                line += 1
            i += 1
            continue

        # Normal code state
        if ch == "/" and nxt == "-":
            block_depth = 1
            i += 2
            continue
        if ch == "-" and nxt == "-":
            in_line_comment = True
            i += 2
            continue
        if ch == '"':
            in_string = True
            out.append(" ")
            i += 1
            continue
        if ch == "\n":
            line += 1
        out.append(ch)
        i += 1

    if block_depth != 0:
        errors.append(f"Unclosed block comment (depth={block_depth})")
    if in_string:
        errors.append("Unclosed string literal")

    return "".join(out), errors


def check_delimiters(code: str):
    """Check balanced (), [], {}, ⟨⟩ in comment/string-stripped Lean 4 code."""
    pairs = {"(": ")", "[": "]", "{": "}", "⟨": "⟩"}
    closing = {v: k for k, v in pairs.items()}
    stack = []
    line = 1
    col = 0
    errors = []
    for ch in code:
        if ch == "\n":
            line += 1
            col = 0
            continue
        col += 1
        if ch in pairs:
            stack.append((ch, line, col))
        elif ch in closing:
            if not stack:
                errors.append(f"L{line}:{col} unmatched closing '{ch}'")
            else:
                top_ch, top_l, top_c = stack.pop()
                if pairs[top_ch] != ch:
                    errors.append(
                        f"L{line}:{col} mismatched '{ch}' (expected '{pairs[top_ch]}' for '{top_ch}' opened at L{top_l}:{top_c})"
                    )
    for top_ch, top_l, top_c in stack:
        errors.append(f"L{top_l}:{top_c} unclosed '{top_ch}'")
    return errors


def check_axioms_and_sorry(fname: str, code: str):
    """Find all bare `axiom` declarations and `sorry` occurrences in executable code."""
    axioms = []
    sorries = []
    for idx, raw_line in enumerate(code.splitlines(), 1):
        m_ax = re.match(r"^\s*(?:private\s+|protected\s+)?axiom\s+([^\s:(]+)", raw_line)
        if m_ax:
            axioms.append((idx, m_ax.group(1)))
        if re.search(r"\bsorry\b", raw_line):
            sorries.append((idx, raw_line.strip()))
    return axioms, sorries


def check_imports(fname: str, code: str, cur: sqlite3.Cursor):
    """Verify every archive import exists in tools/lean_index.db AND on disk under src/."""
    imports = []
    missing_db = []
    missing_disk = []
    for idx, raw_line in enumerate(code.splitlines(), 1):
        m = re.match(r"^\s*import\s+([A-Za-z0-9_.\u2080-\u2089']+)", raw_line)
        if not m:
            continue
        mod = m.group(1)
        imports.append((idx, mod))
        if mod == "Mathlib" or mod.startswith("Mathlib.") or mod.startswith("ERH.") or mod.startswith("erh_research."):
            continue
        row = cur.execute("SELECT rel_path FROM files WHERE module = ?", (mod,)).fetchone()
        if row is None:
            missing_db.append((idx, mod))
        rel_path = mod.replace(".", "/") + ".lean"
        if not (SRC_DIR / rel_path).exists():
            missing_disk.append((idx, mod, rel_path))
    return imports, missing_db, missing_disk


def check_header_src_refs(fname: str, raw_text: str):
    """Verify every `@ src/...lean` path referenced in blueprint header comments exists on disk."""
    refs = re.findall(r"@\s*src/([A-Za-z0-9_/\u2080-\u2089'-]+\.lean)", raw_text)
    missing = []
    for rel in sorted(set(refs)):
        if not (SRC_DIR / rel).exists():
            missing.append(rel)
    return len(set(refs)), missing


def check_prop_structure_universe_hygiene(fname: str, code: str):
    """
    Static linter for the 3 new Wave-7 blueprints: ensures no `structure ... : Prop where`
    contains a naked `: Prop`, `: ℕ`, `: ℤ`, `: ℝ`, or `: Type` field (which causes Lean 4
    `invalid universe level in structure` errors).
    """
    issues = []
    lines = code.splitlines()
    in_prop_struct = False
    struct_name = ""
    for idx, line in enumerate(lines, 1):
        s = line.strip()
        m_start = re.match(r"^structure\s+([A-Za-z0-9_']+).*:\s*Prop\s+where\b", s)
        if m_start:
            in_prop_struct = True
            struct_name = m_start.group(1)
            continue
        if in_prop_struct:
            if not line.startswith(" ") and s != "":
                in_prop_struct = False
                continue
            # Check for direct field ending with naked `: Prop`, `: ℕ`, `: Type`
            m_field = re.match(r"^\s+([A-Za-z0-9_']+)\s*:\s*(Prop|ℕ|ℤ|ℝ|Type(?:\s+\d+)?)\s*$", line)
            if m_field:
                issues.append(f"L{idx} ({struct_name}.{m_field.group(1)} : {m_field.group(2)})")
    return issues


def v_p_fact(p: int, d: int) -> int:
    """Exact p-adic valuation v_p(d!) via Legendre's formula."""
    s = 0
    q = p
    while q <= d:
        s += d // q
        q *= p
    return s


def verify_arithmetic_theorems():
    """Pass 6: Independent exact Python/integer verification of arithmetic theorems in Modules 5-7."""
    # Module 5: lsz_weights_critical_gap & d01_optimal_smoothing_regime
    for e2 in range(4, 25):
        for e1 in range(e2 + 3, e2 + 25):
            r1 = e1 + e2 - 2
            r2 = e1 - e2 - 1
            t1 = e1 - e2
            t2 = e1 + e2 + 2
            a, r = e2, e2 + 3
            assert r1 - r2 >= 7, f"Failed r1-r2>=7 at ({e1},{e2})"
            assert t1 >= 3 and t2 >= 10 and r - a == 3

    # Module 6: r1_realQuad_ge_archive_R1 & c10_sturm_weight_le
    for l in [3, 5, 7, 11, 53]:
        for o in [1, 2, 4, 8]:
            for hq in [1, 3, 7]:
                for N_base in [hq, hq + 5, 2 * hq]:
                    for n0_val in [0, 1, 2, 3]:
                        archive_R1 = 16 * o * (l * hq) ** 2 * (4 ** n0_val)
                        rq_R1 = 16 * o * (l * N_base) ** 4 * (4 ** n0_val)
                        assert archive_R1 <= rq_R1
        for k_prime in range(0, l):
            assert 2 * k_prime + 2 * l + 3 <= 4 * l + 1

    # Module 7: d10_1a_bellmanFord_refuted
    for k in range(1, 21):
        a0 = k * (2 ** k) + 1
        a1 = (k - 1) * (2 ** k) + 1
        assert a0 - a1 == 2 ** k and a0 - a1 > 1
        if k >= 2:
            assert 2 * (2 ** k) - 1 < a0

    # Module 7: d10_1c_n_lin_linear_bound & Q2 strict improvement < 4H
    n_lin_cases = 0
    for l in [2, 3, 5, 7, 11, 53]:
        for eK in range(1, 11):
            for H in range(1, 31):
                d_max = (H * eK) // (l - 1)
                for d in range(1, d_max + 1):
                    v = v_p_fact(l, d)
                    assert (l - 1) * v + 1 <= d
                    n_lin = d + v + (H - 1) // (l - 1)
                    lhs = ((l - 1) ** 2) * n_lin + 2 * (l - 1)
                    rhs = (l * eK + l - 1) * H
                    assert lhs <= rhs, f"Failed D10-1c bound at l={l}, eK={eK}, H={H}, d={d}"
                    if l == 2 and eK == 1:
                        assert n_lin + 2 <= 3 * H and n_lin < 4 * H
                    n_lin_cases += 1

    # Module 7: d12_1_locAbelian_linear_bound
    for h in range(1, 10):
        for s in range(1, 8):
            for s1 in range(1, 8):
                for vf1 in range(0, 5):
                    m = max(s, s1)
                    assert 32 * (2 * h * m + 1) + m + vf1 == 64 * h * m + m + 32 + vf1

    return n_lin_cases


def main():
    print("=" * 84)
    print("WAVE-7 E11 STATIC VERIFICATION & ARCHIVE-ALIGNMENT AUDIT (ALL 7 LEAN BLUEPRINTS)")
    print("=" * 84)

    assert DB_PATH.exists(), f"Missing SQLite index: {DB_PATH}"
    conn = sqlite3.connect(str(DB_PATH))
    cur = conn.cursor()

    total_files_in_db = cur.execute("SELECT COUNT(*) FROM files").fetchone()[0]
    total_decls_in_db = cur.execute("SELECT COUNT(*) FROM decls").fetchone()[0]
    print(f"[DB] Loaded {DB_PATH.name}: {total_files_in_db:,} files, {total_decls_in_db:,} declarations\n")

    hard_failures = []
    summary_rows = []

    # Passes 1, 2, 3, 4(header src refs), 5(universe hygiene) across ALL 7 blueprints
    for fname in ALL_BLUEPRINTS:
        fpath = BLUEPRINT_DIR / fname
        if not fpath.exists():
            hard_failures.append(f"Missing blueprint file: {fpath}")
            continue

        raw_text = fpath.read_text(encoding="utf-8")
        line_count = len(raw_text.splitlines())
        code, comment_errs = strip_comments_and_strings(raw_text)
        delim_errs = check_delimiters(code)
        axioms, sorries = check_axioms_and_sorry(fname, code)
        imports, missing_db, missing_disk = check_imports(fname, code, cur)
        n_src_refs, missing_src_refs = check_header_src_refs(fname, raw_text)
        univ_issues = check_prop_structure_universe_hygiene(fname, code) if fname in WAVE7_NEW_FILES else []

        # Strict failure policy
        if comment_errs:
            hard_failures.append(f"{fname}: comment/string errors: {comment_errs}")
        if delim_errs:
            hard_failures.append(f"{fname}: delimiter errors: {delim_errs[:5]}")
        if sorries:
            hard_failures.append(f"{fname}: contains `sorry` at {sorries}")
        if missing_db:
            hard_failures.append(f"{fname}: imports missing in lean_index.db: {missing_db}")
        if missing_disk:
            hard_failures.append(f"{fname}: imports missing on disk: {missing_disk}")
        if missing_src_refs:
            hard_failures.append(f"{fname}: @ src/... header paths missing on disk: {missing_src_refs}")
        if univ_issues:
            hard_failures.append(f"{fname}: Prop-structure universe hygiene issues: {univ_issues}")

        # Axiom enforcement policy:
        #   - 0 bare axioms strictly required in all 3 new Wave-7 files and all 3 clean prior files
        #   - MainERH.lean (untouched Wave-3 file): exact match against 3 documented legacy *_spec axioms
        if fname == LEGACY_WAVE3_MAIN:
            ax_map = dict(axioms)
            if ax_map != EXPECTED_LEGACY_MAINERH_AXIOMS:
                hard_failures.append(
                    f"{fname}: axiom set {ax_map} != expected Wave-3 legacy set {EXPECTED_LEGACY_MAINERH_AXIOMS}"
                )
            ax_status = f"{len(axioms)} (Wave-3 legacy, untouched)"
        else:
            if axioms:
                hard_failures.append(f"{fname}: forbidden bare axiom(s): {axioms}")
            ax_status = "0"

        summary_rows.append((fname, line_count, len(imports), n_src_refs, ax_status, len(sorries), len(delim_errs)))

    print("PASS 1-3 & 5 SUMMARY (All 7 Blueprints):")
    print(f"{'Blueprint File':40s} {'Lines':>6s} {'Imports':>7s} {'@src':>5s} {'Axioms':>28s} {'Sorry':>5s} {'DelimErr':>8s}")
    print("-" * 105)
    for row in summary_rows:
        print(f"{row[0]:40s} {row[1]:6d} {row[2]:7d} {row[3]:5d} {row[4]:>28s} {row[5]:5d} {row[6]:8d}")

    # Pass 4: Exact Wave-7 Symbol & Line-Number Ledger Verification against lean_index.db + disk
    print("\nPASS 4: EXACT WAVE-7 ARCHIVE DECLARATION & LINE-NUMBER LEDGER VERIFICATION:")
    verified_symbols = 0
    for bp_file, full_name, rel_path, exp_line in WAVE7_SYMBOL_LEDGER:
        disk_path = SRC_DIR / rel_path
        if not disk_path.exists():
            hard_failures.append(f"Ledger file missing on disk: {rel_path}")
            continue
        # Check DB entry (either exact full_name or matching short name in same rel_path & line)
        short_name = full_name.split(".")[-1]
        row = cur.execute(
            "SELECT full_name, kind, line FROM decls WHERE rel_path = ? AND (full_name = ? OR (name = ? AND line = ?))",
            (rel_path, full_name, short_name, exp_line),
        ).fetchone()
        if row is None:
            hard_failures.append(
                f"Ledger symbol NOT found in lean_index.db: {full_name} @ {rel_path}:{exp_line}"
            )
            continue
        db_full, db_kind, db_line = row
        # Verify the exact source line on disk contains the short declaration name
        src_lines = disk_path.read_text(encoding="utf-8").splitlines()
        if not (1 <= exp_line <= len(src_lines)) or short_name not in src_lines[exp_line - 1]:
            hard_failures.append(
                f"Ledger line mismatch on disk: {full_name} expected at {rel_path}:{exp_line}, "
                f"line reads: {src_lines[exp_line - 1] if 1 <= exp_line <= len(src_lines) else 'EOF'}"
            )
            continue
        verified_symbols += 1

    print(f"  Verified {verified_symbols}/{len(WAVE7_SYMBOL_LEDGER)} exact archive declarations "
          f"(DB full_name/name + disk path + verbatim line match).")

    # Pass 4b: Code-Body Archive Identifier Existence Check (Modules 5-7)
    code_body_symbols = {
        "GSp4CountI_RealQuadratic.lean": [
            "KatoTwoW", "kUse'", "Used", "WitAQ", "BlochKatoSelmerVanishes", "colRep", "tw",
            "Newform", "Att", "cycBar", "Qbar", "Dat", "Kill", "IsPt", "Coef", "GG",
        ],
        "CountVAbsorption_C08_C09.lean": [
            "Raw", "al", "be", "th", "XVan", "Host", "R1", "c2", "n0", "CountV",
            "HostData", "XData", "hostData_of_host", "countV_of_finiteness_duality_euler_host",
            "ThmS6_s", "LemmaM", "LemmaM'", "LocalFiniteness", "LocalTateDuality", "LocalEulerChar",
            "GlobalFiniteness", "GlobalEulerChar", "PoitouTateNormalised", "HostVanE", "HostXpp",
            "HostRigid_s", "HostNumber_s", "UnramifiedCocycleIsCoboundaryOfBernoulliUnit", "CorX",
            "lemmaX", "corX",
        ],
        "PrismaticLinearCokernel_D10_D11.lean": [
            "LocPrime", "FinExt", "LocLat", "GK", "OL", "IsCrys", "JumpsInV", "IsJumpV", "actD",
            "TBAt", "IK", "D7", "HWOf", "FonOf", "LiftTheoremAllCases", "LiftGaloisDescent",
            "CrystallineRestrictionToExtension", "FontaineAt", "LiftK", "liftK_of", "LatHom", "LiftF",
        ],
    }
    total_cb = 0
    verified_cb = 0
    for bp_file, sym_list in code_body_symbols.items():
        bp_code, _ = strip_comments_and_strings((BLUEPRINT_DIR / bp_file).read_text(encoding="utf-8"))
        for sym in sym_list:
            total_cb += 1
            cnt = cur.execute("SELECT COUNT(*) FROM decls WHERE name = ?", (sym,)).fetchone()[0]
            if cnt == 0:
                hard_failures.append(f"Pass 4b: code-body symbol `{sym}` ({bp_file}) missing in lean_index.db")
            elif sym not in bp_code:
                hard_failures.append(f"Pass 4b: expected symbol `{sym}` not found in executable code of {bp_file}")
            else:
                verified_cb += 1
    print(f"  Pass 4b: Verified {verified_cb}/{total_cb} code-body archive symbols present in both blueprint code and lean_index.db.")

    # Pass 6: Exact Arithmetic Theorem Spot-Checks
    n_lin_cases = verify_arithmetic_theorems()
    print(f"\nPASS 6: ARITHMETIC THEOREM VERIFICATION:")
    print(f"  All exact integer checks passed (including {n_lin_cases:,} (l, eK, H, d) instances of D10-1c N_lin).")

    print("\n" + "=" * 84)
    if hard_failures:
        print(f"AUDIT FAILED with {len(hard_failures)} issue(s):")
        for err in hard_failures:
            print(f"  [FAIL] {err}")
        sys.exit(1)
    else:
        print("AUDIT PASSED (exit 0):")
        print("  - All 3 new Wave-7 blueprints: 0 bare axioms, 0 sorry, 0 delimiter errors,")
        print("    0 Prop-structure universe issues, 100% archive imports & symbol ledger verified.")
        print("  - All 3 clean prior blueprints (Modules 1, 2, 4): 0 bare axioms, 0 sorry, 100% imports verified.")
        print("  - Legacy Wave-3 MainERH.lean (untouched): 3 documented legacy *_spec axioms logged (L295, L325, L356).")
        print("  - Caveat: Static verification only (lean/lake compiler not installed in workspace).")
        sys.exit(0)


if __name__ == "__main__":
    main()
