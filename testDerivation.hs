{-#LANGUAGE PostfixOperators, MultiParamTypeClasses, EmptyDataDecls, GADTs, TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}

import PropositionalDerivations
import PropositionalLanguage
import AbstractDerivationDataTypes

simpleDerivationTest2 :: PropDerivation
simpleDerivationTest2 = do
    prove (pn 1 .→. pn 1) $ do
        l1 <- ((pn 1) `prRule`)
        cdRule l1

simpleDerivationTest :: PropDerivation
simpleDerivationTest = do
    prove ((pn 1 .→. (pn 2 .→. pn 3)) .→. ((pn 1 .→. pn 2) .→. (pn 1 .→. pn 3))) $ do 
        l1 <- (pn 1 .→. (pn 2 .→. pn 3) `prRule` )
        l2 <- prove ((pn 1 .→. pn 2) .→. (pn 1 .→. pn 3)) $ do 
            l3 <- (pn 1 .→. pn 2        `prRule` )
            l4 <- prove (pn 1 .→. pn 3) $ do  
                l5 <- ( pn 1            `prRule` )
                l6 <- ( pn 2 .→. pn 3   `mpRule` l1 $ l5 )
                l7 <- ( pn 2            `mpRule` l5 $ l3 )
                l8 <- ( pn 3            `mpRule` l7 $ l6 )
                cdRule l8
            cdRule l4
        cdRule l2 
