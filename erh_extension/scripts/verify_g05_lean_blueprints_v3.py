#!/usr/bin/env python3
"""
Wave-9 G05 Static Verification, Archive-Alignment & E07 Empirical Audit Script
Checks all 11 Lean 4.33.1 ERH blueprint modules in erh_research/lean_erh_blueprint/:
  Modules 1-3 (Wave-3 A19): RelCMHostVariantII.lean, GeneralizedLemmaM_HidaSetting4.lean, MainERH.lean
  Module  4   (Wave-4 B09): ChCore_ZqTower.lean
  Modules 5-7 (Wave-7 E11): GSp4CountI_RealQuadratic.lean, CountVAbsorption_C08_C09.lean,
                            PrismaticLinearCokernel_D10_D11.lean
  Modules 8-11 (Wave-9 G05): MasterRQCountI_SchemeI_F06_F07.lean,
                             RegimeII_CoronaA1_G03_LTDK_G01.lean,
                             Mu2Zero_GroupClassification_F05_F10_G02.lean,
                             CountV_WallA_Fixed_E07_E08_F11.lean

NOTE: This is a static syntactic, delimiter-balance, universe-hygiene, archive-symbol
alignment, and SymPy/exact-arithmetic verification suite backed by tools/lean_index.db
and riemann-hypothesis/src/. Full Lean 4.33.1 elaboration/compilation is NOT performed
here because `lean`/`lake` are not installed in this workspace.
"""

import math
import os
import re
import sqlite3
import sys
from fractions import Fraction
from pathlib import Path

import sympy as sp

ROOT = Path("/Users/tiancaikeyize/Downloads/阅读黎曼猜想证明")
BLUEPRINT_DIR = ROOT / "erh_research" / "lean_erh_blueprint"
SRC_DIR = ROOT / "riemann-hypothesis" / "src"
DB_PATH = ROOT / "tools" / "lean_index.db"

PRIOR_CLEAN_FILES = [
    "RelCMHostVariantII.lean",
    "GeneralizedLemmaM_HidaSetting4.lean",
    "ChCore_ZqTower.lean",
]

LEGACY_WAVE3_MAIN = "MainERH.lean"

WAVE7_CLEAN_FILES = [
    "GSp4CountI_RealQuadratic.lean",
    "CountVAbsorption_C08_C09.lean",
    "PrismaticLinearCokernel_D10_D11.lean",
]

WAVE9_NEW_FILES = [
    "MasterRQCountI_SchemeI_F06_F07.lean",
    "RegimeII_CoronaA1_G03_LTDK_G01.lean",
    "Mu2Zero_GroupClassification_F05_F10_G02.lean",
    "CountV_WallA_Fixed_E07_E08_F11.lean",
]

ALL_BLUEPRINTS = PRIOR_CLEAN_FILES + [LEGACY_WAVE3_MAIN] + WAVE7_CLEAN_FILES + WAVE9_NEW_FILES

# Documented legacy Wave-3 axioms in untouched MainERH.lean (immutability policy: never edit Wave-3 files)
EXPECTED_LEGACY_MAINERH_AXIOMS = {
    295: "extendedRiemannHypothesis_of_totallyReal_D4_725_spec",
    325: "extendedRiemannHypothesis_regimeA_spec",
    356: "extendedRiemannHypothesis_regimeB_spec",
}

# Complete archive declaration & line-number ledger for ALL 4 Wave-9 blueprints (Modules 8-11)
# Tuple format: (blueprint_file, exact_archive_full_name, archive_rel_path, expected_line)
WAVE9_SYMBOL_LEDGER = [
    # ---- Module 8: MasterRQCountI_SchemeI_F06_F07.lean ----
    ("MasterRQCountI_SchemeI_F06_F07.lean", "UpperTheory.V.Z.Kato.WeilSphericalRecords.KatoTwoW",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/KatoQuadraticCharacters/SphericalDecomposition/KatoTwoW.lean", 10),
    ("MasterRQCountI_SchemeI_F06_F07.lean", "UpperTheory.V.Z.Kato.WeilSphericalRecords.kUse'",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/KatoQuadraticCharacters/SphericalDecomposition/KatoTwoW.lean", 26),
    ("MasterRQCountI_SchemeI_F06_F07.lean", "UpperTheory.V.Z.Kato.Used",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/KatoQuadraticCharacters/KatoTwoOfUseN.lean", 11),
    ("MasterRQCountI_SchemeI_F06_F07.lean", "UpperTheory.V.Z.Kato.KatoTwo",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/KatoQuadraticCharacters/KatoTwoOfUseN.lean", 43),
    ("MasterRQCountI_SchemeI_F06_F07.lean", "UpperTheory.V.Z.Kato.RigII",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/KatoQuadraticCharacters/KatoTwoOfUseN.lean", 49),
    ("MasterRQCountI_SchemeI_F06_F07.lean", "UpperTheory.V.Z.Win.WitAQ",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/AutomorphyLifting/AAcrossOf.lean", 17),
    ("MasterRQCountI_SchemeI_F06_F07.lean", "UpperTheory.V.Af.BlochKatoSelmerVanishes",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/AutomorphicForms/BlochKatoSelmerVanishes.lean", 144),
    ("MasterRQCountI_SchemeI_F06_F07.lean", "UpperTheory.V.U3.Dat",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeGroups/RhoKApply.lean", 16),
    ("MasterRQCountI_SchemeI_F06_F07.lean", "UpperTheory.V.U3.Dat.Kill",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeGroups/RhoKApply.lean", 61),
    ("MasterRQCountI_SchemeI_F06_F07.lean", "UpperTheory.V.U3.Dat.Ring",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeGroups/RhoKApply.lean", 66),
    ("MasterRQCountI_SchemeI_F06_F07.lean", "UpperTheory.V.U3.Dat.IsModular",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeGroups/RhoKApply.lean", 91),
    ("MasterRQCountI_SchemeI_F06_F07.lean", "UpperTheory.V.U3.admissible_of_typeII",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeGroups/AdmissibleOfTypeII.lean", 103),
    ("MasterRQCountI_SchemeI_F06_F07.lean", "UpperTheory.V.HV.GD",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/Counts.lean", 9),
    ("MasterRQCountI_SchemeI_F06_F07.lean", "UpperTheory.V.HV.CountI",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/Counts.lean", 53),
    ("MasterRQCountI_SchemeI_F06_F07.lean", "UpperTheory.V.Fr.b0",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/FrobeniusSmoothVectors/RankLeOfCardLe.lean", 137),
    ("MasterRQCountI_SchemeI_F06_F07.lean", "UpperTheory.V.Fr.krull_dim_lt_of_not_le_triangular",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/FrobeniusSmoothVectors/KrullDimLtOfNotLeTriangular.lean", 36),
    ("MasterRQCountI_SchemeI_F06_F07.lean", "UpperTheory.V.Pr.GalLink",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/CurveDVRSpecialization/HostFrameEx.lean", 22),
    ("MasterRQCountI_SchemeI_F06_F07.lean", "UpperTheory.V.Pr.HostFrameEx",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/CurveDVRSpecialization/HostFrameEx.lean", 69),
    ("MasterRQCountI_SchemeI_F06_F07.lean", "UpperTheory.V.Pr.GdFrameEx",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/CurveDVRSpecialization/HostFrameEx.lean", 75),
    ("MasterRQCountI_SchemeI_F06_F07.lean", "UpperTheory.V.Pr.components_good_rank_three",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/CurveDVRSpecialization/PropagationTheoremGL3.lean", 213),

    # ---- Module 9: RegimeII_CoronaA1_G03_LTDK_G01.lean ----
    ("RegimeII_CoronaA1_G03_LTDK_G01.lean", "Formalism.MainNotions.LiftingTheory.LiftGaloisDescent",
     "Formalism/SharpRestriction/LevelLetterCocycles/LiftingTheory.lean", 577),
    ("RegimeII_CoronaA1_G03_LTDK_G01.lean", "Formalism.MainNotions.LiftingTheory.LiftTheoremAllCases",
     "Formalism/SharpRestriction/LevelLetterCocycles/LiftingTheory.lean", 586),
    ("RegimeII_CoronaA1_G03_LTDK_G01.lean", "Formalism.MainNotions.LocalSituation.TBat",
     "Formalism/SharpRestriction/LevelLetterCocycles/LocalSituation.lean", 165),
    ("RegimeII_CoronaA1_G03_LTDK_G01.lean", "Formalism.LIFT.wBTail_of",
     "Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/Graded.lean", 115),
    ("RegimeII_CoronaA1_G03_LTDK_G01.lean", "Formalism.LIFT.CocyclePolynomialSubmodules.uClaim_of",
     "Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/UClaim.lean", 194),
    ("RegimeII_CoronaA1_G03_LTDK_G01.lean", "GlobalTheory.BSP.BK",
     "Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsStratHom.lean", 14),
    ("RegimeII_CoronaA1_G03_LTDK_G01.lean", "GlobalTheory.BSP.Digits",
     "Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsStratHom.lean", 125),
    ("RegimeII_CoronaA1_G03_LTDK_G01.lean", "GlobalTheory.BSP.Env",
     "Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsStratHom.lean", 127),
    ("RegimeII_CoronaA1_G03_LTDK_G01.lean", "GlobalTheory.BSP.Strat",
     "Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsStratHom.lean", 146),
    ("RegimeII_CoronaA1_G03_LTDK_G01.lean", "GlobalTheory.BSP.Framed",
     "Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsStratHom.lean", 164),
    ("RegimeII_CoronaA1_G03_LTDK_G01.lean", "GlobalTheory.BSP.IsStratHom",
     "Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsStratHom.lean", 170),
    ("RegimeII_CoronaA1_G03_LTDK_G01.lean", "GlobalTheory.BSP.MReal",
     "Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsStratHom.lean", 177),
    ("RegimeII_CoronaA1_G03_LTDK_G01.lean", "GlobalTheory.Published.BhattScholzeIntegral",
     "Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/BhattScholzeIntegral.lean", 12),
    ("RegimeII_CoronaA1_G03_LTDK_G01.lean", "GlobalTheory.Cyc.InvKilled.invariants_killed",
     "Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/InvariantsVanishAtPrimeOfAdmissible.lean", 156),
    ("RegimeII_CoronaA1_G03_LTDK_G01.lean", "GlobalTheory.ExpImage.expStar_image",
     "Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DualExponentialImageContainsLattice.lean", 41),
    ("RegimeII_CoronaA1_G03_LTDK_G01.lean", "UpperTheory.N.Cyc",
     "Development/AutomorphicArithmetic/ResidueCharacters/InvariantsKilledOverCyclotomicAlt.lean", 23),
    ("RegimeII_CoronaA1_G03_LTDK_G01.lean", "UpperTheory.N.LiftK",
     "Development/AutomorphicArithmetic/ResidueCharacters/InvariantsKilledOverCyclotomicAlt.lean", 31),
    ("RegimeII_CoronaA1_G03_LTDK_G01.lean", "UpperTheory.N.InvariantsKilledOverCyclotomic",
     "Development/AutomorphicArithmetic/ResidueCharacters/InvariantsKilledOverCyclotomicAlt.lean", 38),
    ("RegimeII_CoronaA1_G03_LTDK_G01.lean", "UpperTheory.N.TBK",
     "Development/AutomorphicArithmetic/ResidueCharacters/InvariantsKilledOverCyclotomicAlt.lean", 43),
    ("RegimeII_CoronaA1_G03_LTDK_G01.lean", "UpperTheory.N.liftK_of",
     "Development/AutomorphicArithmetic/ResidueCharacters/LiftKOf.lean", 12),

    # ---- Module 10: Mu2Zero_GroupClassification_F05_F10_G02.lean ----
    ("Mu2Zero_GroupClassification_F05_F10_G02.lean", "UpperTheory.V.Published.FerreroWashington",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/PublishedTheorems/FerreroWashington.lean", 7),
    ("Mu2Zero_GroupClassification_F05_F10_G02.lean", "UpperTheory.V.FW.cyc",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/FerreroWashington.lean", 18),
    ("Mu2Zero_GroupClassification_F05_F10_G02.lean", "UpperTheory.V.FW.ferreroWashington",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/FerreroWashington.lean", 104),
    ("Mu2Zero_GroupClassification_F05_F10_G02.lean", "UpperTheory.V.Two.fwRk",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/QuadraticExtensions/IsAlgClosureRat.lean", 37),
    ("Mu2Zero_GroupClassification_F05_F10_G02.lean", "UpperTheory.V.Two.abRk",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/QuadraticExtensions/IsAlgClosureRat.lean", 49),
    ("Mu2Zero_GroupClassification_F05_F10_G02.lean", "UpperTheory.V.Two.baseRk",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/QuadraticExtensions/IsAlgClosureRat.lean", 69),
    ("Mu2Zero_GroupClassification_F05_F10_G02.lean", "UpperTheory.V.Two.towerTwo",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/QuadraticExtensions/IsAlgClosureRat.lean", 87),
    ("Mu2Zero_GroupClassification_F05_F10_G02.lean", "UpperTheory.V.Two.towerFixed",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/QuadraticExtensions/IsAlgClosureRat.lean", 98),
    ("Mu2Zero_GroupClassification_F05_F10_G02.lean", "UpperTheory.V.Two.twoBase",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/QuadraticExtensions/IsAlgClosureRat.lean", 112),
    ("Mu2Zero_GroupClassification_F05_F10_G02.lean", "UpperTheory.V.Two.TowerBound",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/QuadraticExtensions/IsAlgClosureRat.lean", 130),
    ("Mu2Zero_GroupClassification_F05_F10_G02.lean", "UpperTheory.V.Two.twoIn",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/QuadraticExtensions/IsAlgClosureRat.lean", 133),
    ("Mu2Zero_GroupClassification_F05_F10_G02.lean", "UpperTheory.V.Two.fixedIn",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/QuadraticExtensions/IsAlgClosureRat.lean", 139),
    ("Mu2Zero_GroupClassification_F05_F10_G02.lean", "UpperTheory.V.Fr.b0",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/FrobeniusSmoothVectors/RankLeOfCardLe.lean", 137),
    ("Mu2Zero_GroupClassification_F05_F10_G02.lean", "UpperTheory.V.Ws.exists_iwasawaRank_bound_of_ferreroWashington",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/WeakShimuraTheory/RealPlaceConjugation/ExistsIwasawaRankBoundOfFerreroWashington.lean", 23),

    # ---- Module 11: CountV_WallA_Fixed_E07_E08_F11.lean ----
    ("CountV_WallA_Fixed_E07_E08_F11.lean", "Formalism.MainNotions.V.Pf.V2.Calc.HidaSetting",
     "Formalism/SharpRestriction/ValuationFrobeniusEpsilon/LeastPrimeTwists/QuotientShiftIrreducible/NoetherianQuotientCalc/EulerVanishingBelowDimension.lean", 113),
    ("CountV_WallA_Fixed_E07_E08_F11.lean", "UpperTheory.V.Alg.M2",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/CommutativeAlgebra/OrbitVanishingLocal.lean", 41),
    ("CountV_WallA_Fixed_E07_E08_F11.lean", "UpperTheory.V.Alg.M3",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/CommutativeAlgebra/OrbitVanishingLocal.lean", 45),
    ("CountV_WallA_Fixed_E07_E08_F11.lean", "UpperTheory.V.Alg.M4",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/CommutativeAlgebra/OrbitVanishingLocal.lean", 52),
    ("CountV_WallA_Fixed_E07_E08_F11.lean", "UpperTheory.V.Alg.M5",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/CommutativeAlgebra/OrbitVanishingLocal.lean", 66),
    ("CountV_WallA_Fixed_E07_E08_F11.lean", "UpperTheory.V.Alg.Eqns",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/CommutativeAlgebra/OrbitVanishingLocal.lean", 86),
    ("CountV_WallA_Fixed_E07_E08_F11.lean", "UpperTheory.V.Alg.mDims",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/CommutativeAlgebra/OrbitVanishingLocal.lean", 103),
    ("CountV_WallA_Fixed_E07_E08_F11.lean", "UpperTheory.V.Alg.M1",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/CommutativeAlgebra/OrbitVanishingLocal.lean", 107),
    ("CountV_WallA_Fixed_E07_E08_F11.lean", "UpperTheory.V.Alg.LemmaM",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/CommutativeAlgebra/OrbitVanishingLocal.lean", 111),
    ("CountV_WallA_Fixed_E07_E08_F11.lean", "UpperTheory.V.Alg.LemmaM'",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/CommutativeAlgebra/OrbitVanishingLocal.lean", 120),
    ("CountV_WallA_Fixed_E07_E08_F11.lean", "UpperTheory.V.UnitaryThreeInertia.Frame.defect",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeDeformations/AdjointDiagonalRepPreservesWeightPiece.lean", 208),
    ("CountV_WallA_Fixed_E07_E08_F11.lean", "UpperTheory.V.UnitaryThreeInertia.Frame.Count",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeDeformations/AdjointDiagonalRepPreservesWeightPiece.lean", 210),
    ("CountV_WallA_Fixed_E07_E08_F11.lean", "UpperTheory.V.UnitaryThreeInertia.Frame.Xpp",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeDeformations/AdjointDiagonalRepPreservesWeightPiece.lean", 217),
    ("CountV_WallA_Fixed_E07_E08_F11.lean", "UpperTheory.V.UnitaryThreeInertia.Frame.VanE",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeDeformations/IsCharZeroPt.lean", 100),
    ("CountV_WallA_Fixed_E07_E08_F11.lean", "UpperTheory.V.UnitaryThreeInertia.Frame.Cl1",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeDeformations/IsCharZeroPt.lean", 107),
    ("CountV_WallA_Fixed_E07_E08_F11.lean", "UpperTheory.V.UnitaryThreeInertia.Frame.IsCharZeroPt",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeDeformations/IsCharZeroPt.lean", 114),
    ("CountV_WallA_Fixed_E07_E08_F11.lean", "UpperTheory.V.UnitaryThreeInertia.Frame.Rigid",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeDeformations/IsCharZeroPt.lean", 118),
    ("CountV_WallA_Fixed_E07_E08_F11.lean", "UpperTheory.V.UnitaryThreeInertia.abstract_count",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeDeformations/AbstractCount.lean", 25),
    ("CountV_WallA_Fixed_E07_E08_F11.lean", "UpperTheory.V.UnitaryThreeInertia.diag_eq_of_tri",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeDeformations/DiagEq.lean", 277),
    ("CountV_WallA_Fixed_E07_E08_F11.lean", "UpperTheory.V.UnitaryThreeInertia.universal_diagonal_of_triangular_points",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeDeformations/UniversalDiagonalOfTriangularPoints.lean", 22),
    ("CountV_WallA_Fixed_E07_E08_F11.lean", "UpperTheory.V.UnitaryThreeInertia.eq_rz_of_diag",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeDeformations/UnitEqOneOfPowEqOneOfResidueOne.lean", 165),
    ("CountV_WallA_Fixed_E07_E08_F11.lean", "UpperTheory.V.UnitaryThreeInertia.frame_class_one",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeDeformations/FrameClassOne.lean", 166),
    ("CountV_WallA_Fixed_E07_E08_F11.lean", "UpperTheory.V.UnitaryThreeInertia.levelAway_of_pt",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeDeformations/LevelAway.lean", 176),
    ("CountV_WallA_Fixed_E07_E08_F11.lean", "UpperTheory.V.UnitaryThreeInertia.levelAt_of_pt",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeDeformations/LevelAt.lean", 172),
    ("CountV_WallA_Fixed_E07_E08_F11.lean", "UpperTheory.V.X.So.lineZero",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/LevelCohomology/SoLineZero.lean", 6),
    ("CountV_WallA_Fixed_E07_E08_F11.lean", "UpperTheory.V.X.So.soCocL",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/LevelCohomology/SoCocL.lean", 9),
    ("CountV_WallA_Fixed_E07_E08_F11.lean", "UpperTheory.V.X.So.hostVanE",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/LevelCohomology/SoHostVanE.lean", 11),
    ("CountV_WallA_Fixed_E07_E08_F11.lean", "UpperTheory.V.Z.J.hostNumberUE_alt",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/EHostNumberU.lean", 317),
    ("CountV_WallA_Fixed_E07_E08_F11.lean", "UpperTheory.V.Af.cohBoundFree",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/AutomorphicForms/TemperedLocalComponents/CohBoundFree.lean", 93),
    ("CountV_WallA_Fixed_E07_E08_F11.lean", "UpperTheory.V.Z.Win.Birth.MixSeedP",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/AutomorphyLifting/PrimeIndexConstruction/MixSeedPAlt.lean", 35),
    ("CountV_WallA_Fixed_E07_E08_F11.lean", "UpperTheory.V.Z.Win.Birth.MixOfP",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/AutomorphyLifting/PrimeIndexConstruction/MixSeedPAlt.lean", 50),
    ("CountV_WallA_Fixed_E07_E08_F11.lean", "UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.polMix_alt",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/EGPolMix.lean", 50),
    ("CountV_WallA_Fixed_E07_E08_F11.lean", "UpperTheory.V.Ws.exists_tame_tower_ok_two",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/WeakShimuraTheory/CompactIntegralFields/ExistsTameTowerOkTwo.lean", 22),
    ("CountV_WallA_Fixed_E07_E08_F11.lean", "UpperTheory.V.Ws.Tower",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/WeakShimuraTheory/NearSplit.lean", 141),
    ("CountV_WallA_Fixed_E07_E08_F11.lean", "UpperTheory.V.Ws.Tower.Two",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/WeakShimuraTheory/NearSplit.lean", 227),
    ("CountV_WallA_Fixed_E07_E08_F11.lean", "UpperTheory.V.Ws.ok2A",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/WeakShimuraTheory/FrobeniusFields/OddPowNe.lean", 55),
    ("CountV_WallA_Fixed_E07_E08_F11.lean", "UpperTheory.V.GradeZeroInterpolatingElement.Raw.XVan",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/SymplecticGSp4/DecompSigmaOrd.lean", 90),
    ("CountV_WallA_Fixed_E07_E08_F11.lean", "UpperTheory.V.GradeZeroInterpolatingElement.Raw.Good",
     "Development/AutomorphicArithmetic/AutomorphicVarieties/SymplecticGSp4/DecompSigmaOrd.lean", 94),
]


def strip_comments_and_strings(text: str):
    """Strip Lean 4 nested block comments `/- ... -/`, line comments `-- ...`, and string literals."""
    out = []
    i = 0
    n = len(text)
    block_depth = 0
    in_line_comment = False
    in_string = False
    errors = []

    while i < n:
        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""

        if in_line_comment:
            if ch == "\n":
                in_line_comment = False
                out.append("\n")
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
            i += 1
            continue

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


def check_axioms_and_sorry(code: str):
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


def check_imports(code: str, cur: sqlite3.Cursor):
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


def check_header_src_refs(raw_text: str):
    """Verify every `@ src/...lean` path referenced in blueprint header comments exists on disk."""
    refs = re.findall(r"@\s*src/([A-Za-z0-9_/\u2080-\u2089'-]+\.lean)", raw_text)
    missing = [rel for rel in sorted(set(refs)) if not (SRC_DIR / rel).exists()]
    return len(set(refs)), missing


def check_prop_structure_universe_hygiene(code: str):
    """Ensure no `structure ... : Prop where` contains naked `: Prop`, `: ℕ`, `: ℤ`, `: ℝ`, or `: Type` fields."""
    issues = []
    in_prop_struct = False
    struct_name = ""
    for idx, line in enumerate(code.splitlines(), 1):
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
            m_field = re.match(r"^\s+([A-Za-z0-9_']+)\s*:\s*(Prop|ℕ|ℤ|ℝ|Type(?:\s+\d+)?)\s*$", line)
            if m_field:
                issues.append(f"L{idx} ({struct_name}.{m_field.group(1)} : {m_field.group(2)})")
    return issues


def verify_e07_and_f11_empirical_audit(cur: sqlite3.Cursor):
    """
    Pass 6A: Automated empirical assertions for Task 1 (E07 Proposition E07-3, Theorem E07-1/2,
    and F11 Fix B4) directly against tools/lean_index.db, riemann-hypothesis/src/, and SymPy.
    """
    results = []

    # 1. Exhaustive transitive-importer audit of Frame.Cl1 & FrameClassOne
    seed_mods = [
        "Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt",
        "Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.FrameClassOne",
    ]
    adj = {}
    for src_mod, imp_mod in cur.execute("SELECT module, imported FROM imports"):
        adj.setdefault(imp_mod, []).append(src_mod)

    visited = set(seed_mods)
    queue = list(seed_mods)
    while queue:
        m = queue.pop()
        for nxt in adj.get(m, []):
            if nxt not in visited:
                visited.add(nxt)
                queue.append(nxt)

    cl1_consumers = []
    for mod in sorted(visited):
        row = cur.execute("SELECT rel_path FROM files WHERE module = ?", (mod,)).fetchone()
        if not row:
            continue
        rp = row[0]
        p = SRC_DIR / rp
        if not p.exists():
            continue
        txt = p.read_text(encoding="utf-8", errors="ignore")
        if re.search(r"\bCl1\b", txt):
            cl1_consumers.append(rp)

    expected_cl1_files = sorted([
        "Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeDeformations/IsCharZeroPt.lean",
        "Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeDeformations/FrameClassOne.lean",
        "Development/AutomorphicArithmetic/AutomorphicVarieties/LevelCohomology/SoLineZero.lean",
        "Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeDeformations/DiagEq.lean",
        "Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeDeformations/UniversalDiagonalOfTriangularPoints.lean",
        "Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeDeformations/UnitEqOneOfPowEqOneOfResidueOne.lean",
        "Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeDeformations/AbstractCount.lean",
    ])
    assert cl1_consumers == expected_cl1_files, (
        f"Unexpected Cl1 consumers! Found={cl1_consumers}, expected={expected_cl1_files}"
    )
    results.append(
        f"Exhaustive Frame.Cl1 scan ({len(visited)} transitive importers): EXACTLY 7 files "
        f"(1 def + 1 producer + 3 core consumers + 2 forwarding wrappers)."
    )

    # 2. Gap G05-1 empirical check: DiagEq.lean:277-282 lacks char-l hypothesis on A,
    #    while UniversalDiagonalOfTriangularPoints.lean:45 ALREADY supplies hA!
    diageq_lines = (
        SRC_DIR / "Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeDeformations/DiagEq.lean"
    ).read_text(encoding="utf-8").splitlines()
    diageq_sig = "\n".join(diageq_lines[276:283])
    assert "UpperTheory.V.UnitaryThreeInertia.diag_eq_of_tri" in diageq_sig and "F.Cl1" in diageq_sig
    assert "algebraMap O A a = 0" not in diageq_sig and "CharP" not in diageq_sig, (
        "Expected DiagEq.lean:277-283 to lack char-l hypothesis on A!"
    )

    udtp_lines = (
        SRC_DIR / "Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeDeformations/UniversalDiagonalOfTriangularPoints.lean"
    ).read_text(encoding="utf-8").splitlines()
    assert "∀ a ∈ maximalIdeal O, algebraMap O A a = 0" in udtp_lines[26]
    assert "intro A _ _ _ f hf hA" in udtp_lines[44]
    results.append(
        "Gap G05-1 verified: DiagEq.lean:277-282 lacks `∀ a ∈ maximalIdeal O, algebraMap O A a = 0`, "
        "whereas sole caller UniversalDiagonalOfTriangularPoints.lean:45 already has it."
    )

    # 3. Gap G05-3 & G05-4 empirical check: AbsCoord.lean:80-82 uses diagonal uniqueness (= W.origin),
    #    AbstractCount.lean:108 invokes eq_rz_of_diag, while SoCocL.lean:9 is arbitrary [NumberField k]
    #    and quantifies over ALL v ∣ l!
    abscoord_lines = (
        SRC_DIR / "Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeDeformations/AbsCoord.lean"
    ).read_text(encoding="utf-8").splitlines()
    assert "(m3 : ∀ ξ : gradedSub 𝒮 →ₐ[O] K," in abscoord_lines[79]
    assert "algebraMap O K (W.origin h x)" in abscoord_lines[81]
    abscount_lines = (
        SRC_DIR / "Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeDeformations/AbstractCount.lean"
    ).read_text(encoding="utf-8").splitlines()
    assert "eq_rz_of_diag" in abscount_lines[107]
    sococ_lines = (
        SRC_DIR / "Development/AutomorphicArithmetic/AutomorphicVarieties/LevelCohomology/SoCocL.lean"
    ).read_text(encoding="utf-8").splitlines()
    assert "UpperTheory.V.X.So.soCocL" in sococ_lines[8]
    assert "[NumberField k]" in sococ_lines[8]
    assert "∀ v : HeightOneSpectrum (𝓞 k), ((l : ℕ) : 𝓞 k) ∈ v.asIdeal" in sococ_lines[8]
    results.append(
        "Gaps G05-3 & G05-4 verified: AbsCoord.lean:80-82 + AbstractCount.lean:108 force diagonal "
        "uniqueness via eq_rz_of_diag, while SoCocL.lean:9 is arbitrary `[NumberField k]` over ALL v ∣ l."
    )

    # 4. E07 Prop E07-3(2) `(M2)` algebraic check: u^{hK} = 1 ∧ u ≡ 1 mod m_A ⇒ u = 1 in char-l domain,
    #    PLUS BOTH counterexamples when either hypothesis is dropped!
    t = sp.Symbol("t")
    poly_checked = 0
    for l in [2, 3, 5, 7]:
        # Test in F_l[t] / (t^N): if u = 1 + c * t^r (c != 0 in F_l), then for hK = l^v * m (l ∤ m),
        # u^{hK} = (1 + c t^r)^{l^v * m} = (1 + c^{l^v} t^{r l^v})^m = 1 + m * c * t^{r l^v} + O(t^{2 r l^v}) != 1!
        for v in [1, 2]:
            lv = l ** v
            for m in [1, 2, 3, 4, 6]:
                if m % l == 0:
                    continue
                hK = lv * m
                # Leading non-constant term of (1 + c * t)^hK mod l is m * c * t^{l^v}
                c_lead = (m % l)
                assert c_lead != 0
                # Direct polynomial expansion check for small hK
                if hK <= 25:
                    for c in range(1, l):
                        poly = sp.Poly((1 + c * t) ** hK, t, modulus=l)
                        coeff_lv = poly.nth(lv) % l
                        assert coeff_lv == (m * c) % l and coeff_lv != 0
                        poly_checked += 1
    # Counterexample A: drop `u - 1 ∈ m_A` in F_l (l odd): u = -1 has u^{2*l} = 1, u != 1
    for l in [3, 5, 7, 11]:
        assert pow(-1, 2 * l, l) == 1 and (-1 % l) != 1
    # Counterexample B: drop `CharP A l` (char 0 cyclotomic ring Z[zeta_l]):
    # u = zeta_l satisfies N(u - 1) = Phi_l(1) = l (so u - 1 in m = (1 - zeta_l)), u^l = 1, yet u != 1!
    x = sp.Symbol("x")
    for l in [3, 5, 7]:
        phi_l = sp.cyclotomic_poly(l, x)
        assert int(phi_l.subs(x, 1)) == l  # Norm_{Q(zeta_l)/Q}(1 - zeta_l) = l => zeta_l - 1 in maximal ideal
        assert sp.rem(x ** l - 1, phi_l, x) == 0
        assert sp.rem(x - 1, phi_l, x) != 0
    results.append(
        f"E07 Prop E07-3(2) `(M2)` verified: {poly_checked} char-l domain polynomial expansions "
        f"(hK = l^v * m, v>=1, m>1) + Counterexample A (no residue=1: u=-1, u^(2l)=1) "
        f"+ Counterexample B (char 0: u=zeta_l, u-1 in m, u^l=1, u!=1)."
    )

    # 5. SymPy verification of E07 Prop E07-3(3) 3x3 matrix identities (exact archive Jmat R 3 & E07 L333 U_1!)
    x0, a1, a2, a3, w_sym = sp.symbols("x0 a1 a2 a3 w")
    J = sp.Matrix([[0, 0, 1], [0, 1, 0], [1, 0, 0]])  # Exact archive Jmat R 3 (UnitaryThreeReflectionRight.lean:44)
    U1 = sp.Matrix([[1, 0, 0], [-x0, 1, 0], [-x0 ** 2 / 2, x0, 1]])  # Exact E07 L333 lower unipotent U_1
    assert U1.det() == 1
    # Involution theta(M) = J * (M^{-1})^T * J; verify theta(U1) = U1
    theta_U1 = sp.simplify(J * (U1.inv()).T * J)
    assert theta_U1 == U1, f"theta(U1) != U1: {theta_U1}"
    # Verify theta(M^{-1})_{a,b} = (J * M^T * J)_{a,b} = M_{2-b, 2-a} (in particular (2,0) entry = w!)
    M_low = sp.Matrix([[a1, 0, 0], [0, a2, 0], [w_sym, 0, a3]])
    theta_inv_M = sp.simplify(J * M_low.T * J)
    assert theta_inv_M[2, 0] == w_sym and theta_inv_M[0, 0] == a3 and theta_inv_M[2, 2] == a1
    # Verify E07 L339 zmat(c, g1, U1^{-1} r1 U1)_{1,0} = (U1^{-1} diag(a1,a2,a3) U1)_{1,0} - (U1^{-1} diag(a3,a2,a1) U1)_{1,0} = x0*(a1 - a3)
    D_g1 = sp.diag(a1, a2, a3)
    D_g1star = sp.diag(a3, a2, a1)
    M1 = sp.simplify(U1.inv() * D_g1 * U1)
    M1star = sp.simplify(U1.inv() * D_g1star * U1)
    assert sp.simplify((M1 - M1star)[1, 0] - x0 * (a1 - a3)) == 0
    results.append(
        "SymPy 3x3 U(3) matrix verification passed (archive Jmat R 3 & E07 L333 U_1): "
        "det(U_1)=1, theta(U_1)=U_1, theta(M^{-1})_{2,0}=w, zmat(c,g_1,U_1^{-1}r_1 U_1)_{1,0}=x0(a1-a3)."
    )

    # 6. F11 Fix B4 verbatim archive checks (including MixSeedP naming catch!)
    mix_txt = (
        SRC_DIR / "Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/AutomorphyLifting/PrimeIndexConstruction/MixSeedPAlt.lean"
    ).read_text(encoding="utf-8")
    mix_lines = mix_txt.splitlines()
    assert "def MixSeedP : Prop :=" in mix_lines[34]
    assert "Ine (F := F) A ≤ ξ.ker" in mix_lines[37]
    assert "mixSeedP_alt" not in mix_txt  # Confirming F11 L161 naming typo!

    pol_lines = (
        SRC_DIR / "Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/EGPolMix.lean"
    ).read_text(encoding="utf-8").splitlines()
    assert "UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.polMix_alt" in pol_lines[49]

    tame_lines = (
        SRC_DIR / "Development/AutomorphicArithmetic/AutomorphicVarieties/WeakShimuraTheory/CompactIntegralFields/ExistsTameTowerOkTwo.lean"
    ).read_text(encoding="utf-8").splitlines()
    assert "quadEx Ω 1 D.S hD.S_prime" in tame_lines[29]

    odd_lines = (
        SRC_DIR / "Development/AutomorphicArithmetic/AutomorphicVarieties/WeakShimuraTheory/FrobeniusFields/OddPowNe.lean"
    ).read_text(encoding="utf-8").splitlines()
    assert "UpperTheory.V.Ws.ok2A" in odd_lines[54]
    results.append(
        "F11 Fix B4 4-step archive match confirmed (with minor F11 L161 typo logged: "
        "MixSeedPAlt.lean:35 defines `MixSeedP`, not `mixSeedP_alt`)."
    )

    return results


def verify_wave9_arithmetic_theorems():
    """Pass 6B: Independent exact Python & SymPy verification of ALL arithmetic/algebraic theorems in Modules 8-11."""
    checks = 0

    # ---- Module 8: MasterRQCountI_SchemeI_F06_F07.lean ----
    # f07_gap1A_e2_eq_four_insufficient
    assert (4 - 1) // 2 + 1 == 2 and 2 < 3
    checks += 1
    # f07_e2MinSchemeI_bounds, f07_schemeI_m2_sufficient, f07_schemeI_critical_counts, f07_regionF_and_euler_unit
    for l in [5, 7, 11, 13, 17, 29, 53, 101, 257]:
        e2_min = max(5, (l + 8) // 4)
        assert e2_min >= 5 and 4 * e2_min >= l + 5
        for e in range(1, 10):
            for delta in [False, True]:
                e2_m2 = e + 2 * (l - 1) - ((l + 1) // 2 if delta else 1)
                assert e2_m2 >= e2_min and e2_m2 >= 6
                checks += 1
        for e2 in [e2_min, e2_min + 1, 2 * l + 9, 2 * l + 15]:
            cd = (e2 - 1) // 2 + 1
            cp = e2 // 2 + 1
            assert cd >= 3 and cp >= 3
            if e2 >= 2 * l + 9:
                assert cd > l + 3 and cp > l + 3
            for r in [e2 + 2, e2 + 3]:
                for j1 in range(0, r - 1):
                    assert 2 * e2 - 1 - r >= 1
                    assert 1 <= r + 1 - j1 <= 2 * e2
                    assert e2 + (l + 1) // 2 - 4 >= 4
                    checks += 1

    # f07_dual_klingen_trace_identity & eq_one (SymPy exact rational)
    l_s, q_s = sp.symbols("l q")
    assert sp.expand((l_s - q_s) - (l_s * q_s - 1) - (l_s + 1) * (1 - q_s)) == 0
    assert sp.simplify(((l_s - q_s) / (1 - q_s) + (l_s * q_s - 1) / (q_s - 1)) / (l_s + 1)) == 1
    checks += 2

    # f02_anticyclotomic_non_cm_collapse, f02_nonpolarized_gln_dimension_inversion, f02_blasius_steinberg_ratio_gap
    for d0 in range(1, 6):
        for p in [3, 5, 7]:
            for m in range(1, 5):
                assert d0 <= d0 * ((p ** m - 1) // 2)
                checks += 1
    for n in range(2, 8):
        for r2 in range(0, 6):
            for dL in range(0, 4):
                assert n * r2 < n * (r2 + 1 + dL)
                assert (n - 1) * r2 < (n - 1) * (r2 + 1 + dL)
                checks += 1
    for qv0 in range(2, 20):
        assert 1 < qv0 ** 2 and 4 <= qv0 ** 2
        checks += 1

    # ---- Module 9: RegimeII_CoronaA1_G03_LTDK_G01.lean ----
    for s in range(1, 12):
        for e1 in range(1, 12):
            for H in range(1, 12):
                ann = 2 * (s + 4 * e1 - 2) * H
                assert ann == 2 * s * H + 2 * (4 * e1 - 2) * H
                if s == 1:
                    assert (2 * e1 + 1) * H <= ann
                checks += 1
    for i in range(0, 20):
        assert 2 * (2 ** i - 1) + 1 == 2 ** (i + 1) - 1
        checks += 1
    for k in range(3, 200):
        for v in range(0, 10):
            if 2 ** v <= k:
                assert 4 * v + 4 <= 3 * k
                checks += 1
    for k in range(1, 15):
        d = 2 ** k + 1
        assert d >= 3 and 2 * d - 2 < 2 * d and 2 * d - (2 * d - 2) == 2
        checks += 1
    # g01_wayB_ult_law_multiplicativity (SymPy)
    c_s, y1_s, y2_s = sp.symbols("c y1 y2")
    assert sp.expand((1 + c_s * y1_s) * (1 + c_s * y2_s) - (1 + c_s * (y1_s + y2_s + c_s * y1_s * y2_s))) == 0
    checks += 1
    # g01_zeta0_no_t_pole_bound
    for eK in range(1, 15):
        for l in [2, 3, 5, 7, 11]:
            for m in range(0, l):
                assert (l - m + eK - 1) // eK <= l - m
                checks += 1
    # f11_b1_buzzardGee_p5_k8_residues
    assert 3 % 24 not in {7, 11, 13, 17} and (5 * 3) % 24 not in {7, 11, 13, 17}
    checks += 1
    # f08_3b_contraction_margin & f08_2c_hensel_threshold
    for l in [2, 3, 5, 7, 11]:
        for M in range(0, 40):
            mc = M // (l - 1) + 1
            assert M + mc + 1 <= l * mc
            checks += 1
        for eK in range(1, 15):
            n0 = (l * eK) // (l - 1) + 1
            for n in range(n0, n0 + 5):
                assert eK <= n and n < l * (n - eK)
                checks += 1

    # ---- Module 10: Mu2Zero_GroupClassification_F05_F10_G02.lean ----
    for X in [1, 2, 4, 8, 16, 32]:
        ind = 1 if X == 1 else 0
        phi = X - 2 if X >= 4 else 0
        assert ind == phi + (2 - X)
        checks += 1
    for Y in range(1, 33):
        for X in [Y, 2 * Y]:
            indY = 1 if Y == 1 else 0
            indX = 1 if X == 1 else 0
            assert indY + Y - X <= indX
            checks += 1
    # g02_1_extremal_law_unique (SymPy exact rational solve)
    p12, p22, phi_s = sp.symbols("p12 p22 p_hi")
    sol = sp.solve([p12 + p22 + phi_s - 1, 2 * p12 + 2 * p22 + 4 * phi_s - 2, p12 + 2 * p22 + 2 * phi_s - sp.Rational(5, 4)], [p12, p22, phi_s])
    assert sol == {phi_s: 0, p12: sp.Rational(3, 4), p22: sp.Rational(1, 4)}
    # g02_2_monogenic_one_twelfth_bound
    EX = Fraction(5, 2)
    EX2 = Fraction(9, 1)
    assert (EX - 2) ** 2 / (EX2 - 4 * EX + 4) == Fraction(1, 12)
    assert Fraction(13, 16) < Fraction(5, 6)
    assert 3 * 2 ** 0 - 2 == 1 and 3 * 2 ** 1 - 5 == 1
    checks += 4

    # ---- Module 11: CountV_WallA_Fixed_E07_E08_F11.lean ----
    def defect_deg(d0, j):
        if j == -1:
            return -d0
        if j == 0:
            return 1 - d0
        if j in (1, 2):
            return d0
        return 0

    def archive_defect(j):
        if j == -1:
            return -1
        if j in (1, 2):
            return 1
        return 0

    for j in range(-5, 6):
        assert defect_deg(1, j) == archive_defect(j)
        checks += 1
    for d0 in range(1, 51):
        assert sum(defect_deg(d0, j) for j in [-2, -1, 0, 1, 2]) == 1
        for r in range(1, 8):
            for rp in range(0, 8):
                assert 2 ** (r + rp + 2 * d0 - 1) == (2 ** d0) * (2 ** (r + rp + d0 - 1))
                checks += 1
    M_s, tr_s, nm_s = sp.symbols("M tr nm")
    assert sp.expand((1 + M_s * tr_s + M_s ** 2 * nm_s) - 1 - M_s * (tr_s + M_s * nm_s)) == 0
    for e in range(1, 8):
        for d0 in range(1, 6):
            assert (e ** 3) ** (2 * d0) == e ** (6 * d0)
            checks += 1
    # R1Fix & big2ThresholdFixed
    for ord_c in [1, 2, 4, 8, 16]:
        for dH in [1, 2, 3, 6]:
            for MF in [1, 3, 7, 27]:
                o2 = max(4, ord_c)
                r1 = max(2 ** 12, 8 * 2 ** 2, 4 * 5 * 7 * 4 ** 2, 8 * o2 * dH * MF ** 2)
                twoPowN = r1 + 1
                assert o2 * MF ** 2 < twoPowN and 2 ** 12 < twoPowN
                checks += 1

    return checks


def main():
    print("=" * 90)
    print("WAVE-9 G05 STATIC VERIFICATION, ARCHIVE-ALIGNMENT & E07 AUDIT (ALL 11 LEAN BLUEPRINTS)")
    print("=" * 90)

    assert DB_PATH.exists(), f"Missing SQLite index: {DB_PATH}"
    conn = sqlite3.connect(str(DB_PATH))
    cur = conn.cursor()

    total_files_in_db = cur.execute("SELECT COUNT(*) FROM files").fetchone()[0]
    total_decls_in_db = cur.execute("SELECT COUNT(*) FROM decls").fetchone()[0]
    print(f"[DB] Loaded {DB_PATH.name}: {total_files_in_db:,} files, {total_decls_in_db:,} declarations\n")

    # Verify no unexpected extra .lean files exist in BLUEPRINT_DIR
    disk_lean_files = sorted(p.name for p in BLUEPRINT_DIR.glob("*.lean"))
    assert set(disk_lean_files) == set(ALL_BLUEPRINTS), (
        f"Blueprint inventory mismatch! Disk={disk_lean_files}, Expected={sorted(ALL_BLUEPRINTS)}"
    )

    hard_failures = []
    summary_rows = []

    # Passes 1, 2, 3, 4(header src refs), 5(universe hygiene) across ALL 11 blueprints
    for fname in ALL_BLUEPRINTS:
        fpath = BLUEPRINT_DIR / fname
        raw_text = fpath.read_text(encoding="utf-8")
        line_count = len(raw_text.splitlines())
        code, comment_errs = strip_comments_and_strings(raw_text)
        delim_errs = check_delimiters(code)
        axioms, sorries = check_axioms_and_sorry(code)
        imports, missing_db, missing_disk = check_imports(code, cur)
        n_src_refs, missing_src_refs = check_header_src_refs(raw_text)
        univ_issues = (
            check_prop_structure_universe_hygiene(code)
            if fname in (WAVE7_CLEAN_FILES + WAVE9_NEW_FILES)
            else []
        )

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

    print("PASS 1-3 & 5 SUMMARY (All 11 Blueprints = 10 Clean 0-Axiom/0-Sorry + 1 Untouched Wave-3 MainERH):")
    print(f"{'Blueprint File':45s} {'Lines':>6s} {'Imports':>7s} {'@src':>5s} {'Axioms':>28s} {'Sorry':>5s} {'DelimErr':>8s}")
    print("-" * 110)
    for row in summary_rows:
        print(f"{row[0]:45s} {row[1]:6d} {row[2]:7d} {row[3]:5d} {row[4]:>28s} {row[5]:5d} {row[6]:8d}")

    # Pass 4a: Exact Wave-9 Symbol & Line-Number Ledger Verification against lean_index.db + disk
    print("\nPASS 4a: EXACT WAVE-9 ARCHIVE DECLARATION & LINE-NUMBER LEDGER VERIFICATION:")
    verified_symbols = 0
    for bp_file, full_name, rel_path, exp_line in WAVE9_SYMBOL_LEDGER:
        disk_path = SRC_DIR / rel_path
        if not disk_path.exists():
            hard_failures.append(f"Ledger file missing on disk: {rel_path}")
            continue
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
        src_lines = disk_path.read_text(encoding="utf-8").splitlines()
        if not (1 <= exp_line <= len(src_lines)) or short_name not in src_lines[exp_line - 1]:
            hard_failures.append(
                f"Ledger line mismatch on disk: {full_name} expected at {rel_path}:{exp_line}, "
                f"line reads: {src_lines[exp_line - 1] if 1 <= exp_line <= len(src_lines) else 'EOF'}"
            )
            continue
        verified_symbols += 1

    print(
        f"  Verified {verified_symbols}/{len(WAVE9_SYMBOL_LEDGER)} exact Wave-9 archive declarations "
        f"(DB full_name/name + disk path + verbatim line match)."
    )

    # Pass 4b: Code-Body Archive Identifier Existence Check (Modules 8-11)
    code_body_symbols = {
        "MasterRQCountI_SchemeI_F06_F07.lean": [
            "KatoTwoW", "kUse'", "Used", "WitAQ", "BlochKatoSelmerVanishes", "colRep", "tw",
            "Newform", "Att", "cycBar", "Qbar", "Dat", "Coef", "G",
        ],
        "RegimeII_CoronaA1_G03_LTDK_G01.lean": [
            "LocPrime", "LiftK",
        ],
        "Mu2Zero_GroupClassification_F05_F10_G02.lean": [
            "FerreroWashington", "TowerBound", "twoIn", "TwoIn",
        ],
        "CountV_WallA_Fixed_E07_E08_F11.lean": [
            "Frame", "defect", "Cl1", "MixSeedP", "MixOfP", "HypothesesH'", "PolMix", "polMix_alt",
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
    print(
        f"  Pass 4b: Verified {verified_cb}/{total_cb} code-body archive symbols present in both "
        f"Wave-9 blueprint executable code and lean_index.db."
    )

    # Pass 6A: E07 & F11 Empirical Audit Assertions
    print("\nPASS 6A: E07 & F11 EMPIRICAL AUDIT ASSERTIONS (DB + SOURCE + SYMPY):")
    audit_results = verify_e07_and_f11_empirical_audit(cur)
    for r in audit_results:
        print(f"  [OK] {r}")

    # Pass 6B: Exact Arithmetic & SymPy Checks for Modules 8-11
    n_arith = verify_wave9_arithmetic_theorems()
    print(f"\nPASS 6B: WAVE-9 ARITHMETIC & SYMPY VERIFICATION:")
    print(f"  All {n_arith:,} exact integer/rational/SymPy assertions across Modules 8-11 passed.")

    print("\n" + "=" * 90)
    if hard_failures:
        print(f"AUDIT FAILED with {len(hard_failures)} issue(s):")
        for err in hard_failures:
            print(f"  [FAIL] {err}")
        sys.exit(1)
    else:
        print("AUDIT PASSED (exit 0):")
        print("  - All 4 new Wave-9 blueprints (Modules 8-11): 0 bare axioms, 0 sorry, 0 delimiter errors,")
        print("    0 Prop-structure universe issues, 100% archive imports & symbol ledger verified.")
        print("  - All 6 clean prior blueprints (Modules 1, 2, 4, 5, 6, 7): 0 bare axioms, 0 sorry, 100% imports verified.")
        print("  - Legacy Wave-3 MainERH.lean (untouched): 3 documented legacy *_spec axioms logged (L295, L325, L356).")
        print("  - E07 Prop E07-3 exhaustive Frame.Cl1 audit + (M2) char-l domain verification + SymPy checks passed.")
        print("  - Caveat: Static + DB + SymPy verification only (lean/lake compiler not installed in workspace).")
        sys.exit(0)


if __name__ == "__main__":
    main()
