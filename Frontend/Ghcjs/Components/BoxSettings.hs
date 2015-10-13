{- Copyright (C) 2015 Jake Ehrlich and Graham Leach-Krouse <gleachkr@ksu.edu>

This file is part of Carnap 

Carnap is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

Carnap is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License
along with Carnap. If not, see <http://www.gnu.org/licenses/>.
-}

module Carnap.Frontend.Ghcjs.Components.BoxSettings (BoxSettings(..), modTableFOL, longModTable, shortModTable, modTableSL,initSettingsSL,initSettingsFOL, modeTableSL)

where

import GHCJS.DOM.Types (HTMLElement)
import Text.Blaze.Html5
import Carnap.Core.Unification.HigherOrderMatching (MatchError)
import Carnap.Systems.NaturalDeduction.ProofTreeDataTypes (ProofForest)
import Carnap.Core.Data.AbstractSyntaxDataTypes (DisplayVar,NextVar,Schematizable, Form)
import Carnap.Core.Data.AbstractSyntaxSecondOrderMatching (S_NextVar, S_DisplayVar, SchemeVar,SSequentItem, Var)
import Carnap.Core.Data.Rules (Sequent(Sequent), AbsRule(AbsRule),AmbiguousRulePlus)
import Carnap.Calculi.ClassicalFirstOrderLogic1 (classicalRules, classicalQLruleSet, prettyLogicBookSDruleSetQL, prettyLogicBookSDruleSetQL, logicBookSDruleSetQL, prettyClassicalQLruleSet)
import Carnap.Calculi.ClassicalSententialLogic1 (classicalSLRules, prettyClassicalSLruleSet, classicalSLruleSet, logicBookSDrules,logicBookSDruleSet)
import Carnap.Languages.FirstOrder.QuantifiedParser (formulaParser, strictFormulaParser)
import Carnap.Languages.Sentential.PropositionalParser (formulaParserSL)
import Carnap.Systems.NaturalDeduction.KalishAndMontegueProofTreeHandler
import Carnap.Systems.NaturalDeduction.FitchProofTreeHandler
import Carnap.Frontend.Components.ProofTreeParser (parseTheBlockKM,parseTheBlockFitch)
import Data.Set
import Data.Map as M
import Carnap.Core.Data.AbstractDerivationDataTypes (RulesAndArity)
import Carnap.Core.Data.AbstractDerivationSecondOrderMatching
import Carnap.Languages.Util.ParserTypes
import Carnap.Systems.NaturalDeduction.Util.ReportTypes
import Carnap.Frontend.Ghcjs.Components.GenHelp (helpPopupQL,helpPopupSL,helpPopupLogicBookSD)

--this module houses data types, some generic settings, and some utility functions for BoxSettings 

data BoxSettings pred con quant f sv a st = BoxSettings {
                    fparser :: FParser (Form pred con quant f sv a) st,
                    fhandler:: ProofForest (Form pred con quant f sv a) -> RulesAndArity -> Set (AmbiguousRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())) -> 
                        Either (DerivationReport (Form pred con quant f sv a))
                            (Either [MatchError (Var pred con quant f sv () (AbsRule (Sequent (SSequentItem pred con quant f sv)))) (AbsRule (Sequent (SSequentItem pred con quant f sv)))] 
                                    (Sequent (SSequentItem pred con quant f sv)), DerivationReport (Form pred con quant f sv a)),
                    pparser :: FParser (Form pred con quant f sv a) st -> String -> ProofForest (Form pred con quant f sv a),
                    rules :: RulesAndArity,
                    ruleset :: Set (AmbiguousRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())),
                    manalysis :: Maybe HTMLElement,
                    mresult :: Maybe HTMLElement,
                    mproofpane :: Maybe HTMLElement,
                    clearAnalysisOnComplete :: Bool, --should we clear the analysis div when the proof is complete?
                    helpMessage :: Maybe Html
                    }

initSettingsFOL = BoxSettings { fparser = formulaParser,
                             pparser = parseTheBlockKM,
                             fhandler = handleForestKM,
                             manalysis = Nothing, 
                             mproofpane = Nothing,
                             mresult = Nothing,
                             rules = classicalRules,
                             ruleset = classicalQLruleSet,
                             clearAnalysisOnComplete = True,
                             helpMessage = Just helpPopupQL}

initSettingsSL = BoxSettings { fparser = formulaParserSL
                             , pparser = parseTheBlockKM
                             , fhandler = handleForestKM
                             , manalysis = Nothing
                             , mproofpane = Nothing
                             , mresult = Nothing
                             , rules = classicalSLRules
                             , ruleset = classicalSLruleSet
                             , clearAnalysisOnComplete = True
                             , helpMessage = Just helpPopupSL
                             }

visOn settings = settings {clearAnalysisOnComplete = False}

strictOn settings = settings {fparser = strictFormulaParser}

fitchOn settings = settings { fhandler = handleForestFitch
                            , pparser = parseTheBlockFitch
                            }

kmOn settings = settings { fhandler = handleForestKM
                         , pparser = parseTheBlockKM
                         , rules = classicalRules
                         , ruleset = classicalQLruleSet
                         , helpMessage = Just helpPopupQL
                         }

logicBookSDOn settings = settings { fhandler = handleForestFitch
                                  , pparser = parseTheBlockFitch
                                  , rules = logicBookSDrules
                                  , ruleset = logicBookSDruleSet
                                  , helpMessage = Just helpPopupLogicBookSD
                                  }

logicBookModeQL settings = settings { fhandler = handleForestFitch
                                    , pparser = parseTheBlockFitch
                                    , rules = logicBookSDrules
                                    , ruleset = logicBookSDruleSetQL
                                    , helpMessage = Just helpPopupLogicBookSD
                                  }

kmSLOn settings = settings { fhandler = handleForestKM
                           , pparser = parseTheBlockKM
                           , rules = classicalSLRules
                           , ruleset = classicalSLruleSet
                           , helpMessage = Just helpPopupSL
                           }

--list of keywords that activate settings modifiers
modTableFOL = M.fromList [ ("visible",visOn)
                       , ("strict", strictOn)
                       , ("fitch", fitchOn)
                       ]

modTableSL = M.fromList [ ("visible", visOn)
                      , ("fitch", fitchOn)
                      , ("logicBookSD",logicBookSDOn)
                      ]

shortModTable = M.fromList [ ('F', fitchOn)
                           , ('D', kmOn)
                           , ('L', logicBookModeQL)
                           ]

longModTable = M.fromList [ ("-", id)
                      , ("Fitch Mode", fitchOn)
                      , ("Default Mode", kmOn)
                      , ("Logic Book Mode", logicBookModeQL)
                      ]

modeTableSL = M.fromList [ ("-", id)
                         , ("Logic Book Mode", logicBookSDOn)
                         , ("Default Mode", kmSLOn)
                         ] --XXX: this is shameful. Come up with a better naming convention.

