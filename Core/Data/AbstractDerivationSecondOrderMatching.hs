{-#LANGUAGE GADTs, TypeSynonymInstances, FlexibleInstances, FlexibleContexts, MultiParamTypeClasses #-}

module Carnap.Core.Data.AbstractDerivationSecondOrderMatching where 

import Carnap.Core.Data.AbstractDerivationDataTypes
import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Data.AbstractSyntaxSecondOrderMatching
import Carnap.Core.Data.Rules
import Carnap.Core.Unification.HigherOrderMatching
import Carnap.Core.Unification.HigherOrderUtil
import Data.List

type SSequent pred con quant f sv = Sequent (SSequentItem pred con quant f sv)